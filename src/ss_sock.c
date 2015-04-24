/*
 * SHADOWSOCKS transport layer over SOCK_STREAM sockets
 *
 * Copyright (C) 2015 Wang Jian <larkwang@gmail.com>
 *
 * crypto code partly based on shadowsocks-libev:
 *     https://github.com/shadowsocks/shadowsocks-libev
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version
 * 2 of the License, or (at your option) any later version.
 */

#define _GNU_SOURCE
#include <ctype.h>
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>

#include <openssl/ssl.h>
#include <openssl/md5.h>
#include <openssl/rand.h>

#include <netinet/tcp.h>
#include <common/buffer.h>
#include <common/compat.h>
#include <common/config.h>
#include <common/debug.h>
#include <common/errors.h>
#include <common/standard.h>
#include <common/ticks.h>
#include <common/time.h>
#include <common/cfgparse.h>

#include <ebsttree.h>

#include <types/global.h>
#include <types/server.h>

#include <proto/acl.h>
#include <proto/arg.h>
#include <proto/connection.h>
#include <proto/fd.h>
#include <proto/freq_ctr.h>
#include <proto/frontend.h>
#include <proto/listener.h>
#include <proto/pattern.h>
#include <proto/server.h>
#include <proto/log.h>
#include <proto/proxy.h>
#include <proto/shctx.h>
#include <proto/task.h>

#include <proto/ss_sock.h>

static const char * supported_ciphers[] = {
	"table",
	"rc4",
	"rc4-md5",
	"aes-128-cfb",
	"aes-192-cfb",
	"aes-256-cfb",
	"bf-cfb",
	"camellia-128-cfb",
	"camellia-192-cfb",
	"camellia-256-cfb",
	"cast5-cfb",
	"des-cfb",
	"idea-cfb",
	"rc2-cfb",
	"seed-cfb",
};

static struct xprt_ops ss_sock;

enum {
	SS_CIPHER_TABLE = 0,
	SS_CIPHER_RC4,
	SS_CIPHER_RC4_MD5,
	SS_CIPHER_AES_128_CFB,
	SS_CIPHER_AES_192_CFB,
	SS_CIPHER_AES_256_CFB,
	SS_CIPHER_BF_CFB,
	SS_CIPHER_CAMELLIA_128_CFB,
	SS_CIPHER_CAMELLIA_192_CFB,
	SS_CIPHER_CAMELLIA_256_CFB,
	SS_CIPHER_CAST5_CFB,
	SS_CIPHER_DES_CFB,
	SS_CIPHER_IDEA_CFB,
	SS_CIPHER_RC2_CFB,
	SS_CIPHER_SEED_CFB,
	SS_CIPHER_LAST_CIPHER,
};

struct cipher_ctx {
	uint32_t	init;
	uint64_t	counter;
	EVP_CIPHER_CTX	evp;
	uint8_t		iv[EVP_MAX_IV_LENGTH];
};

struct ss_sock_ctx {
	int method;
	int iv_len;
	struct {
		int	len;
		char	*pos;
		char	*end;
		char	*buf;
	} s;
	struct {
		int	len;
		char	*pos;
		char	*end;
		char	*buf;
	} r;
	uint8_t key[EVP_MAX_KEY_LENGTH];
	unsigned char *e_table;
	unsigned char *d_table;
	struct cipher_ctx *e_ctx;
	struct cipher_ctx *d_ctx;
};

#define SS_BUF_SIZE		2048
#define OFFSET_ROL(p, o)	((uint64_t)(*(p + o)) << (8 * o))

static int random_compare(const void *_x, const void *_y, uint32_t i, uint64_t a)
{
	uint8_t x = *((uint8_t *)_x);
	uint8_t y = *((uint8_t *)_y);
	return a % (x + i) - a % (y + i);
}

static void merge(uint8_t *left, int llength, uint8_t *right,
                  int rlength, uint32_t salt, uint64_t key)
{
	uint8_t *ltmp = (uint8_t *)malloc(llength * sizeof(uint8_t));
	uint8_t *rtmp = (uint8_t *)malloc(rlength * sizeof(uint8_t));

	uint8_t *ll = ltmp;
	uint8_t *rr = rtmp;

	uint8_t *result = left;

	memcpy(ltmp, left, llength * sizeof(uint8_t));
	memcpy(rtmp, right, rlength * sizeof(uint8_t));

	while (llength > 0 && rlength > 0) {
		if (random_compare(ll, rr, salt, key) <= 0) {
			*result = *ll;
			++ll;
			--llength;
		} else {
			*result = *rr;
			++rr;
			--rlength;
		}
		++result;
	}

	if (llength > 0) {
		while (llength > 0) {
			*result = *ll;
			++result;
			++ll;
			--llength;
		}
	} else {
		while (rlength > 0) {
			*result = *rr;
			++result;
			++rr;
			--rlength;
		}
	}

	free(ltmp);
	free(rtmp);
}

static void merge_sort(uint8_t array[], int length, uint32_t salt, uint64_t key)
{
	uint8_t middle;
	uint8_t *left, *right;
	int llength;

	if (length <= 1) {
		return;
	}

	middle = length / 2;

	llength = length - middle;

	left = array;
	right = array + llength;

	merge_sort(left, llength, salt, key);
	merge_sort(right, middle, salt, key);
	merge(left, llength, right, middle, salt, key);
}

static const EVP_CIPHER *get_cipher(int method)
{
	if (method <= SS_CIPHER_TABLE || method >= SS_CIPHER_LAST_CIPHER)
		return NULL;

	if (method == SS_CIPHER_RC4_MD5)
		method = SS_CIPHER_RC4;

	return EVP_get_cipherbyname(supported_ciphers[method]);
}

static int ss_sock_srv_init_table(struct server *srv, struct proxy *curproxy)
{
	uint32_t i;
	uint64_t key = 0;
	uint8_t  *digest;

	srv->ss_ctx.e_table = malloc(256);
	srv->ss_ctx.d_table = malloc(256);
	if (srv->ss_ctx.e_table == NULL || srv->ss_ctx.d_table == NULL) {
		if (srv->ss_ctx.e_table) {
			free(srv->ss_ctx.e_table);
			srv->ss_ctx.e_table = NULL;
		}
		if (srv->ss_ctx.d_table) {
			free(srv->ss_ctx.d_table);
			srv->ss_ctx.d_table = NULL;
		}
		return 1;
	}

	digest = MD5(srv->ss_ctx.secret, strlen((char *)srv->ss_ctx.secret), NULL);

	for (i = 0; i < 8; i++) {
		key += OFFSET_ROL(digest, i);
	}
	for (i = 0; i < 256; ++i) {
		srv->ss_ctx.e_table[i] = i;
	}
	for (i = 1; i < 1024; ++i) {
		merge_sort(srv->ss_ctx.e_table, 256, i, key);
	}
	for (i = 0; i < 256; ++i) {
		srv->ss_ctx.d_table[srv->ss_ctx.e_table[i]] = i;
	}

	return 0;
}

static int ss_sock_srv_init_key(struct server *srv, struct proxy *curproxy)
{
	unsigned char     iv[EVP_MAX_IV_LENGTH];
	const EVP_CIPHER  *cipher;
	const EVP_MD      *md;

	OpenSSL_add_all_algorithms();

	cipher = get_cipher(srv->ss_ctx.method);

	if (cipher == NULL) {
		Alert("config : %s '%s', server '%s': cipher '%s' not found in crypto library.\n",
		      proxy_type_str(curproxy), curproxy->id, srv->id,
		      supported_ciphers[srv->ss_ctx.method]);
		return 1;
	}

	md = EVP_get_digestbyname("MD5");
	if (md == NULL) {
		Alert("config : %s '%s', server '%s': digest 'MD5' not found in crypto library.\n",
		      proxy_type_str(curproxy), curproxy->id, srv->id);
		return 1;
	}

	srv->ss_ctx.key_len = EVP_BytesToKey(cipher, md,
					     NULL,
					     srv->ss_ctx.secret,
					     strlen((char *)srv->ss_ctx.secret),
					     1,
					     srv->ss_ctx.key, iv);
	if (srv->ss_ctx.key_len == 0) {
		Alert("config : %s '%s', server '%s': fail to generate key and iv.\n",
		      proxy_type_str(curproxy), curproxy->id, srv->id);
		return 1;
	}

	if (srv->ss_ctx.method == SS_CIPHER_RC4_MD5) {
		srv->ss_ctx.iv_len = 16;
	} else {
		srv->ss_ctx.iv_len = EVP_CIPHER_iv_length(cipher);
	}
	return 0;
}

/* prepare shadowsocks context from server options. Returns an error count */
int ss_sock_prepare_srv_ctx(struct server *srv, struct proxy *curproxy)
{
	int cfgerr = 0;

	if (srv->use_shadowsocks) {
		if (!srv->ss_ctx.secret) {
			Alert("config : %s '%s', server '%s': secret not specified.\n",
			      proxy_type_str(curproxy), curproxy->id, srv->id);
			cfgerr++;
			return cfgerr;
		}
		if (srv->ss_ctx.method == SS_CIPHER_TABLE) {
			if (ss_sock_srv_init_table(srv, curproxy)) {
				Alert("config : %s '%s', server '%s': fail to init table.\n",
				      proxy_type_str(curproxy), curproxy->id, srv->id);
				cfgerr++;
				return cfgerr;
			}
		} else {
			if (ss_sock_srv_init_key(srv, curproxy)) {
				Alert("config : %s '%s', server '%s': fail to init key.\n",
				      proxy_type_str(curproxy), curproxy->id, srv->id);
				cfgerr++;
				return cfgerr;
			}
		}

		srv->xprt = &ss_sock;
	}

	return cfgerr;
}

static int cipher_ctx_init(struct cipher_ctx *ctx, struct server *srv, int enc)
{
	int method = srv->ss_ctx.method;

	memset(ctx, 0, sizeof(struct cipher_ctx));
	if (method <= SS_CIPHER_TABLE || method >= SS_CIPHER_LAST_CIPHER)
		return -1;

	EVP_CIPHER_CTX *evp = &ctx->evp;

	EVP_CIPHER_CTX_init(evp);
	if (!EVP_CipherInit_ex(evp, get_cipher(srv->ss_ctx.method), NULL, NULL, NULL, enc)) {
		Alert("failed to initialize cipher %s\n", supported_ciphers[method]);
		return -1;
	}
	if (!EVP_CIPHER_CTX_set_key_length(evp, srv->ss_ctx.key_len)) {
		EVP_CIPHER_CTX_cleanup(evp);
		Alert("failed to set key length: %d", srv->ss_ctx.key_len);
		return -1;
	}
	if (srv->ss_ctx.method > SS_CIPHER_RC4_MD5)
		EVP_CIPHER_CTX_set_padding(evp, 1);

	return 0;
}

static int ss_sock_ctx_set_iv(struct ss_sock_ctx *sock_ctx, uint8_t *iv,
			      size_t iv_len, int enc)
{
	const unsigned char *true_key;
	struct cipher_ctx *ctx;

	if (enc) {
		RAND_bytes(iv, iv_len);
		ctx = sock_ctx->e_ctx;
	} else {
		ctx = sock_ctx->d_ctx;
	}

	if (sock_ctx->method == SS_CIPHER_RC4_MD5) {
		unsigned char key_iv[32];
		memcpy(key_iv, sock_ctx->key, 16);
		memcpy(key_iv + 16, iv, 16);
		true_key = MD5(key_iv, 32, NULL);
		iv_len = 0;
	} else {
		true_key = sock_ctx->key;
	}

	if (!EVP_CipherInit_ex(&ctx->evp, NULL, NULL, true_key, iv, enc)) {
		EVP_CIPHER_CTX_cleanup(&ctx->evp);
		return -1;
	}
	return 0;
}

static void ss_sock_ctx_free(struct ss_sock_ctx *sock_ctx)
{
	if (sock_ctx == NULL)
		return;

	if (sock_ctx->s.buf)
		free(sock_ctx->s.buf);
	if (sock_ctx->r.buf)
		free(sock_ctx->r.buf);

	if (sock_ctx->e_ctx)
		free(sock_ctx->e_ctx);
	if (sock_ctx->d_ctx)
		free(sock_ctx->d_ctx);
	if (sock_ctx->e_table)
		free(sock_ctx->e_table);
	if (sock_ctx->d_table)
		free(sock_ctx->d_table);

	free(sock_ctx);
}

static int ss_sock_init(struct connection *conn)
{
	struct server *srv;
	struct ss_sock_ctx *sock_ctx;

	/* already initialized */
	if (conn->xprt_ctx)
		return 0;

	if (!conn_ctrl_ready(conn))
		return 0;

	/* if connection to shadowsocks server */
	if (objt_server(conn->target)) {
		srv = objt_server(conn->target);
		sock_ctx = malloc(sizeof(struct ss_sock_ctx));
		if (sock_ctx) {
			memset(sock_ctx, 0, sizeof(struct ss_sock_ctx));
			sock_ctx->method = srv->ss_ctx.method;
			conn->xprt_ctx = sock_ctx;
		} else {
			conn->err_code = CO_ER_SYS_MEMLIM;
			goto out_error;
		}

		/* buffer */
		sock_ctx->s.buf = malloc(SS_BUF_SIZE);
		sock_ctx->s.pos = sock_ctx->s.end = sock_ctx->s.buf;
		sock_ctx->s.len = SS_BUF_SIZE;

		sock_ctx->r.buf = malloc(SS_BUF_SIZE);
		sock_ctx->r.pos = sock_ctx->r.end = sock_ctx->r.buf;
		sock_ctx->r.len = SS_BUF_SIZE;

		if (!sock_ctx->s.buf || !sock_ctx->r.buf) {
			conn->err_code = CO_ER_SYS_MEMLIM;
			goto out_error;
		}

		/* table */
		if (srv->ss_ctx.method == SS_CIPHER_TABLE) {
			sock_ctx->e_table = malloc(256);
			sock_ctx->d_table = malloc(256);

			if (!sock_ctx->e_table || !sock_ctx->d_table) {
				conn->err_code = CO_ER_SYS_MEMLIM;
				goto out_error;
			}

			memcpy(sock_ctx->e_table, srv->ss_ctx.e_table, 256);
			memcpy(sock_ctx->d_table, srv->ss_ctx.d_table, 256);
		}

		/* init cipher context */
		if (srv->ss_ctx.method > SS_CIPHER_TABLE) {
			memcpy(sock_ctx->key, srv->ss_ctx.key, EVP_MAX_KEY_LENGTH);
			sock_ctx->iv_len = srv->ss_ctx.iv_len;

			sock_ctx->e_ctx = malloc(sizeof(struct cipher_ctx));
			sock_ctx->d_ctx = malloc(sizeof(struct cipher_ctx));

			if (!sock_ctx->e_ctx || !sock_ctx->d_ctx) {
				conn->err_code = CO_ER_SYS_MEMLIM;
				goto out_error;
			}

			if (cipher_ctx_init(sock_ctx->e_ctx, srv, 1)
			    || cipher_ctx_init(sock_ctx->d_ctx, srv, 0))
				goto out_error;
		}

		/* leave init state and start pseudo handshake */
		conn_data_want_send(conn);

		return 0;

	out_error:
		ss_sock_ctx_free(sock_ctx);
		conn->xprt_ctx = NULL;
		return -1;
	}
	/* don't know how to handle it */
	else {
		conn->err_code = CO_ER_NOPROTO;
		return -1;
	}

}

/* encrypt plain data from provided buffer into s.buf */
static int ss_sock_encrypt(struct ss_sock_ctx *sock_ctx, const uint8_t *plain, ssize_t len)
{
	char *crypt;

	/* use simple table encryption */
	if (sock_ctx->method == SS_CIPHER_TABLE) {
		int n;
		crypt = sock_ctx->s.buf;
		for (n = 0; n < len; n++) {
			crypt[n] = (char) sock_ctx->e_table[(unsigned char)plain[n]];
		}
		sock_ctx->s.pos = sock_ctx->s.buf;
		sock_ctx->s.end = sock_ctx->s.buf + len;
		return 0;
	}

	/* use cipher */
	int p_len = len, c_len = len;
	int buf_size = c_len;
	int err;
	int iv_len = 0;

	/* if first called, we need to send IV to peer */
	if (!sock_ctx->e_ctx->init)
		iv_len = sock_ctx->iv_len;

	/* enlarge send buffer if necessary */
	buf_size += iv_len;
	if (buf_size > sock_ctx->s.len) {
		char *tmp = realloc(sock_ctx->s.buf, buf_size);
		if (tmp) {
			sock_ctx->s.buf = tmp;
			sock_ctx->s.len = buf_size;
		}
		else
			return -1;
	}

	if (!sock_ctx->e_ctx->init) {
		uint8_t iv[EVP_MAX_IV_LENGTH];
		ss_sock_ctx_set_iv(sock_ctx, iv, iv_len, 1);
		memcpy(sock_ctx->s.buf, iv, iv_len);
		sock_ctx->e_ctx->init = 1;
	}

	err = EVP_CipherUpdate(&sock_ctx->e_ctx->evp,
			       (uint8_t *)(sock_ctx->s.buf + iv_len), &c_len,
			       plain, p_len);
	if (!err)
		return -1;

	sock_ctx->s.pos = sock_ctx->s.buf;
	sock_ctx->s.end = sock_ctx->s.buf + iv_len + c_len;
	return 0;
}

/* decrypt data from r.buf into provided buffer
 * result maybe smaller then expected */
static int ss_sock_decrypt(struct ss_sock_ctx *sock_ctx, uint8_t *plain, ssize_t *len)
{
	char *crypt = sock_ctx->r.buf;

	/* using simple table encryption */
	if (sock_ctx->method == SS_CIPHER_TABLE) {
		int n;
		for (n = 0; n < *len; n++) {
			plain[n] = (char) sock_ctx->d_table[(unsigned char)crypt[n]];
		}
		sock_ctx->r.pos = sock_ctx->r.buf;
		sock_ctx->r.end = sock_ctx->r.buf + *len;
		return 0;
	}

	/* use cipher */
	int p_len = *len, c_len = *len;
	int err;
	int iv_len = 0;

	/* the first iv_len bytes is IV we recv */
	if (!sock_ctx->d_ctx->init) {
		iv_len = sock_ctx->iv_len;
		c_len -= iv_len;
		ss_sock_ctx_set_iv(sock_ctx, (uint8_t *)crypt, iv_len, 0);
		sock_ctx->d_ctx->init = 1;
	}

	err = EVP_CipherUpdate(&sock_ctx->d_ctx->evp,
			       plain, &p_len,
			       (uint8_t *)(crypt + iv_len), c_len);
	if (!err)
		return -1;

	*len = p_len;
	return 0;
}

/*
 * send data in buffer
 * NOTE: after call, check conn->sock_ctx.end, if equals to conn->sock_ctx.buf,
 * all data is sent.
 */
/* 0 = error
 * 1 = socket not ready
 * 2 = partial send
 * 3 = all send
 */
static inline int real_send(struct connection *conn)
{
	ssize_t ret, try;
	struct ss_sock_ctx *sock_ctx;

	sock_ctx = (struct ss_sock_ctx *) conn->xprt_ctx;

	try = sock_ctx->s.end - sock_ctx->s.pos;
	if (try == 0)
		goto finished;

	ret = send(conn->t.sock.fd, sock_ctx->s.pos, try, 0);

	if (ret == -1) {
		if (errno == EAGAIN || errno == ENOTCONN) {
			fd_cant_send(conn->t.sock.fd);
			return 1;
		} else {
			conn->flags |= CO_FL_ERROR;
			return 0;
		}
	}
	if (ret < try) {
		sock_ctx->s.pos += ret;
		return 2;
	}

finished:
	sock_ctx->s.pos = sock_ctx->s.end = sock_ctx->s.buf;

	return 3;
}

static int ss_sock_from_buf(struct connection *conn, struct buffer *buf, int flags)
{
	ssize_t ret, try, done = 0;
	struct ss_sock_ctx *sock_ctx;
	ssize_t len = 0;

	if (!conn->xprt_ctx)
		goto out_error;

	if (!conn_ctrl_ready(conn))
		return 0;

	if (!fd_send_ready(conn->t.sock.fd))
		return 0;

	sock_ctx = (struct ss_sock_ctx *) conn->xprt_ctx;

	/* pseudo handshake: send destaddr to shadowsocks server */
	if (!conn->xprt_st) {
		struct session *sess;
		struct connection *cli_conn;
		char hdr_buf[32];

		sess = conn->owner;
		cli_conn = objt_conn(sess->req->prod->end);

		if (cli_conn)
			conn_get_to_addr(cli_conn);
		else
			goto out_error;

		if (cli_conn->addr.to.ss_family == AF_INET6) {
			hdr_buf[len++] = 4;
			memcpy(hdr_buf + len,
			       &(((struct sockaddr_in6 *)&(cli_conn->addr.to))->sin6_addr),
			       sizeof(struct in6_addr));
			len += sizeof(struct in6_addr);
			memcpy(hdr_buf + len,
			       &(((struct sockaddr_in6 *)&(cli_conn->addr.to))->sin6_port),
			       2);
			len += 2;
		} else {
			hdr_buf[len++] = 1;
			memcpy(hdr_buf + len,
			       &(((struct sockaddr_in *)&(cli_conn->addr.to))->sin_addr),
			       sizeof(struct in_addr));
			len += sizeof(struct in_addr);
			memcpy(hdr_buf + len,
			       &(((struct sockaddr_in *)&(cli_conn->addr.to))->sin_port),
			       2);
			len += 2;
		}
		if (ss_sock_encrypt(sock_ctx, (uint8_t *)hdr_buf, len)) {
			conn->err_code = CO_ER_SYS_MEMLIM;
			goto out_error;
		}
		conn->xprt_st = 1;
	}

	ret = real_send(conn);
	if (ret == 0)
		goto out_error;
	else if (ret == 1 || ret == 2)
		return 0;

	/* we can send data now */
	while(buf->o) {
		try = bo_contig_data(buf);
		if (try > sock_ctx->s.len)
			try = sock_ctx->s.len;

		if (ss_sock_encrypt(sock_ctx, (uint8_t *)bo_ptr(buf), try))
			goto out_error;

		done += try;
		buf->o -= try;

		ret = real_send(conn);
		if (ret == 0)
			goto out_error;
		else if (ret == 1 || ret == 2)
			return done;
	}
	return done;

out_error:
	conn->flags |= CO_FL_ERROR;
	return done;
}

static int ss_sock_to_buf(struct connection *conn, struct buffer *buf, int count)
{
	ssize_t ret, try, done = 0;
	struct ss_sock_ctx *sock_ctx;

	if (!conn->xprt_ctx)
		goto out_error;

	if (buffer_empty(buf))
		buf->p = buf->data;

	sock_ctx = (struct ss_sock_ctx *) conn->xprt_ctx;

	while (count > 0) {
		/* first check if we have some room after p+i */
		try = buf->data + buf->size - (buf->p + buf->i);
		/* otherwise continue between data and p-o */
		if (try <= 0) {
			try = buf->p - (buf->data + buf->o);
			if (try <= 0)
				break;
		}
		if (try > count)
			try = count;
		if (try > sock_ctx->r.len)
			try = sock_ctx->r.len;

		ret = recv(conn->t.sock.fd, sock_ctx->r.buf, try, 0);
		if (ret > 0) {
			ssize_t dec = ret;
			if (ss_sock_decrypt(sock_ctx, (uint8_t *)bi_end(buf), &dec)) {
				return -1;
			}
			buf->i += dec;
			done += dec;

			if (ret < try)
				break;
			count -= ret;
		}
		else if (ret == 0)
			goto read0;
		else {
			if (errno == EAGAIN || errno == ENOTCONN) {
				fd_cant_recv(conn->t.sock.fd);
				break;
			}
			goto out_error;
		}

	}
	return done;

read0:
	conn_sock_read0(conn);
	return done;

out_error:
	conn->flags |= CO_FL_ERROR;
	return done;
}

static void ss_sock_close(struct connection *conn)
{
	if (conn->xprt_ctx) {
		ss_sock_ctx_free(conn->xprt_ctx);
		conn->xprt_ctx = NULL;
	}
}

static void ss_sock_shutw(struct connection *conn, int clean)
{
	//if (conn->flags & CO_FL_HANDSHAKE)
	//	return;

	/* no shakehand in progress, try a clean shutdown */
	shutdown(conn->t.sock.fd, SHUT_WR);
}

/* parse the "shadowsocks" server keyword */
static int srv_parse_shadowsocks(char **args, int *cur_arg, struct proxy *px, struct server *newsrv, char **err)
{
	newsrv->use_shadowsocks = 1;
	return 0;
}

/* parse the "method" server keyword */
static int srv_parse_method(char **args, int *cur_arg, struct proxy *px, struct server *newsrv, char **err)
{
	if (!*args[*cur_arg+1]) {
		if (err)
			memprintf(err, "'%s' : missing method name", args[*cur_arg]);
		return ERR_ALERT | ERR_FATAL;
	}

	if (strcmp(args[*cur_arg + 1], "table") == 0)
		newsrv->ss_ctx.method = SS_CIPHER_TABLE;
	else if (strcmp(args[*cur_arg + 1], "rc4") == 0)
		newsrv->ss_ctx.method = SS_CIPHER_RC4;
	else if (strcmp(args[*cur_arg + 1], "rc4-md5") == 0)
		newsrv->ss_ctx.method = SS_CIPHER_RC4_MD5;
	else if (strcmp(args[*cur_arg + 1], "aes-128-cfb") == 0)
		newsrv->ss_ctx.method = SS_CIPHER_AES_128_CFB;
	else if (strcmp(args[*cur_arg + 1], "aes-192-cfb") == 0)
		newsrv->ss_ctx.method = SS_CIPHER_AES_192_CFB;
	else if (strcmp(args[*cur_arg + 1], "aes-256-cfb") == 0)
		newsrv->ss_ctx.method = SS_CIPHER_AES_256_CFB;
	else if (strcmp(args[*cur_arg + 1], "bf-cfb") == 0)
		newsrv->ss_ctx.method = SS_CIPHER_BF_CFB;
	else if (strcmp(args[*cur_arg + 1], "camellia-128-cfb") == 0)
		newsrv->ss_ctx.method = SS_CIPHER_CAMELLIA_128_CFB;
	else if (strcmp(args[*cur_arg + 1], "camellia-192-cfb") == 0)
		newsrv->ss_ctx.method = SS_CIPHER_CAMELLIA_192_CFB;
	else if (strcmp(args[*cur_arg + 1], "camellia-256-cfb") == 0)
		newsrv->ss_ctx.method = SS_CIPHER_CAMELLIA_256_CFB;
	else if (strcmp(args[*cur_arg + 1], "cast5-cfb") == 0)
		newsrv->ss_ctx.method = SS_CIPHER_CAST5_CFB;
	else if (strcmp(args[*cur_arg + 1], "des-cfb") == 0)
		newsrv->ss_ctx.method = SS_CIPHER_DES_CFB;
	else if (strcmp(args[*cur_arg + 1], "idea-cfb") == 0)
		newsrv->ss_ctx.method = SS_CIPHER_IDEA_CFB;
	else if (strcmp(args[*cur_arg + 1], "rc2-cfb") == 0)
		newsrv->ss_ctx.method = SS_CIPHER_RC2_CFB;
	else if (strcmp(args[*cur_arg + 1], "seed-cfb") == 0)
		newsrv->ss_ctx.method = SS_CIPHER_SEED_CFB;
	else {
		if (err)
			memprintf(err, "'%s' : unknown crypto '%s', only table, rc4, rc4-md5, aes-128-cfb, aes-192-cfb, aes-256-cfb, bf-cfb, camellia-128-cfb, camellia-192-cfb, camellia-256-cfb, cast5-cfb, des-cfb, idea-cfb, rc2-cfb, seed-cfb are supported\n",
				  args[*cur_arg], args[*cur_arg + 1]);
		return ERR_ALERT | ERR_FATAL;
	}

	return 0;
}

/* parse the "password" or "secret" server keyword */
static int srv_parse_secret(char **args, int *cur_arg, struct proxy *px, struct server *newsrv, char **err)
{
	if (!*args[*cur_arg+1]) {
		if (err)
			memprintf(err, "'%s' : missing shared secret", args[*cur_arg]);
		return ERR_ALERT | ERR_FATAL;
	}
	newsrv->ss_ctx.secret = (unsigned char *) strdup(args[*cur_arg + 1]);

	return 0;
}

static struct srv_kw_list srv_kws = { "SHADOWSOCKS", { }, {
	{ "shadowsocks",  srv_parse_shadowsocks,  0, 0 },
	{ "method",       srv_parse_method,       1, 0 },
	{ "password",     srv_parse_secret,       1, 0 },
	{ "secret",       srv_parse_secret,       1, 0 },
	{ NULL, NULL, 0, 0 },
}};

static struct xprt_ops ss_sock = {
	.snd_buf  = ss_sock_from_buf,
	.rcv_buf  = ss_sock_to_buf,
	.rcv_pipe = NULL,
	.snd_pipe = NULL,
	.shutr    = NULL,
	.shutw    = ss_sock_shutw,
	.close    = ss_sock_close,
	.init     = ss_sock_init,
};

__attribute__((constructor))
static void __ss_sock_init(void)
{
	srv_register_keywords(&srv_kws);
}

/*
 * Local variables:
 *  c-indent-level: 8
 *  c-basic-offset: 8
 * End:
 */
