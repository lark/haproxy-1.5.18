/*
 * Channel management functions.
 *
 * Copyright 2000-2012 Willy Tarreau <w@1wt.eu>
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version
 * 2 of the License, or (at your option) any later version.
 *
 */

#include <ctype.h>
#include <stdarg.h>
#include <stdio.h>
#include <string.h>

#include <common/config.h>
#include <common/memory.h>
#include <common/buffer.h>

#include <proto/channel.h>

struct pool_head *pool2_channel;


/* perform minimal intializations, report 0 in case of error, 1 if OK. */
int init_channel()
{
	pool2_channel = create_pool("channel", sizeof(struct channel), MEM_F_SHARED);
	return pool2_channel != NULL;
}

/* Schedule up to <bytes> more bytes to be forwarded via the channel without
 * notifying the owner task. Any data pending in the buffer are scheduled to be
 * sent as well, within the limit of the number of bytes to forward. This must
 * be the only method to use to schedule bytes to be forwarded. If the requested
 * number is too large, it is automatically adjusted. The number of bytes taken
 * into account is returned. Directly touching ->to_forward will cause lockups
 * when buf->o goes down to zero if nobody is ready to push the remaining data.
 */
unsigned long long __channel_forward(struct channel *chn, unsigned long long bytes)
{
	unsigned int budget;
	unsigned int forwarded;

	/* This is more of a safety measure as it's not supposed to happen in
	 * regular code paths.
	 */
	if (unlikely(chn->to_forward == CHN_INFINITE_FORWARD)) {
		b_adv(chn->buf, chn->buf->i);
		return bytes;
	}

	/* Bound the transferred size to a 32-bit count since all our values
	 * are 32-bit, and we don't want to reach CHN_INFINITE_FORWARD.
	 */
	budget = MIN(bytes, CHN_INFINITE_FORWARD - 1);

	/* transfer as much as we can of buf->i */
	forwarded = MIN(chn->buf->i, budget);
	b_adv(chn->buf, forwarded);
	budget -= forwarded;

	if (!budget)
		return forwarded;

	/* Now we must ensure chn->to_forward sats below CHN_INFINITE_FORWARD,
	 * which also implies it won't overflow. It's less operations in 64-bit.
	 */
	bytes = (unsigned long long)chn->to_forward + budget;
	if (bytes >= CHN_INFINITE_FORWARD)
		bytes = CHN_INFINITE_FORWARD - 1;
	budget = bytes - chn->to_forward;

	chn->to_forward += budget;
	forwarded += budget;
	return forwarded;
}

/* writes <len> bytes from message <msg> to the channel's buffer. Returns -1 in
 * case of success, -2 if the message is larger than the buffer size, or the
 * number of bytes available otherwise. The send limit is automatically
 * adjusted to the amount of data written. FIXME-20060521: handle unaligned
 * data. Note: this function appends data to the buffer's output and possibly
 * overwrites any pending input data which are assumed not to exist.
 */
int bo_inject(struct channel *chn, const char *msg, int len)
{
	int max;

	if (len == 0)
		return -1;

	if (len < 0 || len > chn->buf->size) {
		/* we can't write this chunk and will never be able to, because
		 * it is larger than the buffer. This must be reported as an
		 * error. Then we return -2 so that writers that don't care can
		 * ignore it and go on, and others can check for this value.
		 */
		return -2;
	}

	max = buffer_realign(chn->buf);

	if (len > max)
		return max;

	memcpy(chn->buf->p, msg, len);
	chn->buf->o += len;
	chn->buf->p = b_ptr(chn->buf, len);
	chn->total += len;
	return -1;
}

/* Tries to copy character <c> into the channel's buffer after some length
 * controls. The chn->o and to_forward pointers are updated. If the channel
 * input is closed, -2 is returned. If there is not enough room left in the
 * buffer, -1 is returned. Otherwise the number of bytes copied is returned
 * (1). Channel flag READ_PARTIAL is updated if some data can be transferred.
 * Channel flag CF_WAKE_WRITE is set if the write fails because the buffer is
 * full.
 */
int bi_putchr(struct channel *chn, char c)
{
	if (unlikely(channel_input_closed(chn)))
		return -2;

	if (channel_full(chn)) {
		chn->flags |= CF_WAKE_WRITE;
		return -1;
	}

	*bi_end(chn->buf) = c;

	chn->buf->i++;
	chn->flags |= CF_READ_PARTIAL;

	if (chn->to_forward >= 1) {
		if (chn->to_forward != CHN_INFINITE_FORWARD)
			chn->to_forward--;
		b_adv(chn->buf, 1);
	}

	chn->total++;
	return 1;
}

/* Tries to copy block <blk> at once into the channel's buffer after length
 * controls. The chn->o and to_forward pointers are updated. If the channel
 * input is closed, -2 is returned. If the block is too large for this buffer,
 * -3 is returned. If there is not enough room left in the buffer, -1 is
 * returned. Otherwise the number of bytes copied is returned (0 being a valid
 * number). Channel flag READ_PARTIAL is updated if some data can be
 * transferred. Channel flag CF_WAKE_WRITE is set if the write fails because
 * the buffer is full.
 */
int bi_putblk(struct channel *chn, const char *blk, int len)
{
	int max;

	if (unlikely(channel_input_closed(chn)))
		return -2;

	if (len < 0)
		return -3;

	max = buffer_max_len(chn);
	if (unlikely(len > max - buffer_len(chn->buf))) {
		/* we can't write this chunk right now because the buffer is
		 * almost full or because the block is too large. Return the
		 * available space or -2 if impossible.
		 */
		if (len > max)
			return -3;

		chn->flags |= CF_WAKE_WRITE;
		return -1;
	}

	if (unlikely(len == 0))
		return 0;

	/* OK so the data fits in the buffer in one or two blocks */
	max = buffer_contig_space(chn->buf);
	memcpy(bi_end(chn->buf), blk, MIN(len, max));
	if (len > max)
		memcpy(chn->buf->data, blk + max, len - max);

	chn->buf->i += len;
	chn->total += len;
	if (chn->to_forward) {
		unsigned long fwd = len;
		if (chn->to_forward != CHN_INFINITE_FORWARD) {
			if (fwd > chn->to_forward)
				fwd = chn->to_forward;
			chn->to_forward -= fwd;
		}
		b_adv(chn->buf, fwd);
	}

	/* notify that some data was read from the SI into the buffer */
	chn->flags |= CF_READ_PARTIAL;
	return len;
}

/* Gets one text line out of a channel's buffer from a stream interface.
 * Return values :
 *   >0 : number of bytes read. Includes the \n if present before len or end.
 *   =0 : no '\n' before end found. <str> is left undefined.
 *   <0 : no more bytes readable because output is shut.
 * The channel status is not changed. The caller must call bo_skip() to
 * update it. The '\n' is waited for as long as neither the buffer nor the
 * output are full. If either of them is full, the string may be returned
 * as is, without the '\n'.
 */
int bo_getline(struct channel *chn, char *str, int len)
{
	int ret, max;
	char *p;

	ret = 0;
	max = len;

	/* closed or empty + imminent close = -1; empty = 0 */
	if (unlikely((chn->flags & CF_SHUTW) || channel_is_empty(chn))) {
		if (chn->flags & (CF_SHUTW|CF_SHUTW_NOW))
			ret = -1;
		goto out;
	}

	p = bo_ptr(chn->buf);

	if (max > chn->buf->o) {
		max = chn->buf->o;
		str[max-1] = 0;
	}
	while (max) {
		*str++ = *p;
		ret++;
		max--;

		if (*p == '\n')
			break;
		p = buffer_wrap_add(chn->buf, p + 1);
	}
	if (ret > 0 && ret < len &&
	    (ret < chn->buf->o || !channel_full(chn)) &&
	    *(str-1) != '\n' &&
	    !(chn->flags & (CF_SHUTW|CF_SHUTW_NOW)))
		ret = 0;
 out:
	if (max)
		*str = 0;
	return ret;
}

/* Gets one full block of data at once from a channel's buffer, optionally from
 * a specific offset. Return values :
 *   >0 : number of bytes read, equal to requested size.
 *   =0 : not enough data available. <blk> is left undefined.
 *   <0 : no more bytes readable because output is shut.
 * The channel status is not changed. The caller must call bo_skip() to
 * update it.
 */
int bo_getblk(struct channel *chn, char *blk, int len, int offset)
{
	int firstblock;

	if (chn->flags & CF_SHUTW)
		return -1;

	if (len + offset > chn->buf->o) {
		if (chn->flags & (CF_SHUTW|CF_SHUTW_NOW))
			return -1;
		return 0;
	}

	firstblock = chn->buf->data + chn->buf->size - bo_ptr(chn->buf);
	if (firstblock > offset) {
		if (firstblock >= len + offset) {
			memcpy(blk, bo_ptr(chn->buf) + offset, len);
			return len;
		}

		memcpy(blk, bo_ptr(chn->buf) + offset, firstblock - offset);
		memcpy(blk + firstblock - offset, chn->buf->data, len - firstblock + offset);
		return len;
	}

	memcpy(blk, chn->buf->data + offset - firstblock, len);
	return len;
}

/*
 * Local variables:
 *  c-indent-level: 8
 *  c-basic-offset: 8
 * End:
 */
