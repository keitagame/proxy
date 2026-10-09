/*
 * proxy.c - 汎用プロキシサーバー (HTTP / HTTPS(CONNECT) / SOCKS5)
 *
 * 機能:
 *   - 同一ポートで HTTP プロキシと SOCKS5 を自動判別 (先頭1バイトで判定)
 *   - HTTP: 絶対URI形式のリクエスト転送 (GET/POST/PUT/... 全メソッド)
 *   - HTTPS: CONNECT メソッドによるトンネリング
 *   - SOCKS5: CONNECT コマンド、IPv4 / IPv6 / ドメイン名
 *   - 認証 (任意): HTTP Basic (Proxy-Authorization) / SOCKS5 ユーザー名+パスワード
 *   - IPv4 / IPv6 両対応、スレッド毎接続、同時接続数上限、各種タイムアウト
 *   - SIGINT / SIGTERM による正常終了
 *
 * ビルド:
 *   gcc -O2 -Wall -Wextra -pthread -o proxy proxy.c
 *
 * 使い方:
 *   ./proxy                         # 127.0.0.1:8080 で待ち受け
 *   ./proxy -b 0.0.0.0 -p 3128      # 全インターフェースで待ち受け (要認証推奨)
 *   ./proxy -a user:pass -v         # 認証あり + 詳細ログ
 *
 * テスト:
 *   curl -x http://127.0.0.1:8080 http://example.com/
 *   curl -x http://127.0.0.1:8080 https://example.com/
 *   curl --socks5-hostname 127.0.0.1:8080 https://example.com/
 */

#define _GNU_SOURCE
#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <getopt.h>
#include <netdb.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <poll.h>
#include <pthread.h>
#include <signal.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>

#define HDR_MAX 16384
#define BUF_SZ  16384
#define LINE_MAX_LEN 8192

/* ------------------------------------------------------------------ */
/* 設定・グローバル                                                     */
/* ------------------------------------------------------------------ */

typedef struct {
    const char *bind_addr;
    const char *port;
    int max_conn;
    int connect_timeout_ms;
    int idle_timeout_ms;
    int hdr_timeout_s;
    int verbose;
    int auth_enabled;
    char auth_user[256];
    char auth_pass[256];
    char auth_b64[700];
} config_t;

static config_t cfg = {
    .bind_addr = "127.0.0.1",
    .port = "8080",
    .max_conn = 512,
    .connect_timeout_ms = 10000,
    .idle_timeout_ms = 300000,
    .hdr_timeout_s = 30,
    .verbose = 0,
    .auth_enabled = 0,
};

static volatile sig_atomic_t g_stop = 0;
static int g_active = 0;

/* ------------------------------------------------------------------ */
/* ログ                                                                 */
/* ------------------------------------------------------------------ */

static void plog(const char *fmt, ...)
{
    char ts[32];
    time_t t = time(NULL);
    struct tm tm;
    localtime_r(&t, &tm);
    strftime(ts, sizeof ts, "%Y-%m-%d %H:%M:%S", &tm);

    char msg[1024];
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(msg, sizeof msg, fmt, ap);
    va_end(ap);

    fprintf(stderr, "[%s] %s\n", ts, msg);
}

/* ------------------------------------------------------------------ */
/* ユーティリティ                                                       */
/* ------------------------------------------------------------------ */

static int send_all(int fd, const void *buf, size_t n)
{
    const char *p = buf;
    while (n > 0) {
        ssize_t w = send(fd, p, n, MSG_NOSIGNAL);
        if (w < 0) {
            if (errno == EINTR) continue;
            return -1;
        }
        p += w;
        n -= (size_t)w;
    }
    return 0;
}

static int recv_exact(int fd, void *buf, size_t n)
{
    char *p = buf;
    while (n > 0) {
        ssize_t r = recv(fd, p, n, 0);
        if (r < 0) {
            if (errno == EINTR) continue;
            return -1;
        }
        if (r == 0) return -1;
        p += r;
        n -= (size_t)r;
    }
    return 0;
}

static void b64enc(const unsigned char *in, size_t n, char *out)
{
    static const char t[] =
        "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    size_t i, o = 0;
    for (i = 0; i + 2 < n; i += 3) {
        out[o++] = t[in[i] >> 2];
        out[o++] = t[((in[i] & 3) << 4) | (in[i + 1] >> 4)];
        out[o++] = t[((in[i + 1] & 15) << 2) | (in[i + 2] >> 6)];
        out[o++] = t[in[i + 2] & 63];
    }
    if (i < n) {
        out[o++] = t[in[i] >> 2];
        if (i + 1 < n) {
            out[o++] = t[((in[i] & 3) << 4) | (in[i + 1] >> 4)];
            out[o++] = t[(in[i + 1] & 15) << 2];
        } else {
            out[o++] = t[(in[i] & 3) << 4];
            out[o++] = '=';
        }
        out[o++] = '=';
    }
    out[o] = '\0';
}

/* 長さ非依存に近い比較 (タイミング攻撃の軽減) */
static int ct_eq(const char *a, const char *b)
{
    size_t la = strlen(a), lb = strlen(b);
    unsigned d = (unsigned)(la ^ lb);
    for (size_t i = 0; i < la && i < lb; i++)
        d |= (unsigned char)a[i] ^ (unsigned char)b[i];
    return d == 0;
}

/* "host", "host:port", "[v6]:port", "v6(裸)" を分解 */
static int parse_hostport(const char *s, int defport,
                          char *host, size_t hs, char *port, size_t ps)
{
    const char *colon = NULL;
    size_t hl;

    if (*s == '[') {
        const char *r = strchr(s, ']');
        if (!r) return -1;
        hl = (size_t)(r - s - 1);
        if (hl == 0 || hl >= hs) return -1;
        memcpy(host, s + 1, hl);
        if (r[1] == ':') colon = r + 1;
        else if (r[1] != '\0') return -1;
    } else {
        const char *c = strrchr(s, ':');
        if (c && memchr(s, ':', (size_t)(c - s)) != NULL) {
            /* コロンが複数 = ポート無しの裸IPv6 */
            hl = strlen(s);
        } else {
            colon = c;
            hl = colon ? (size_t)(colon - s) : strlen(s);
        }
        if (hl == 0 || hl >= hs) return -1;
        memcpy(host, s, hl);
    }
    host[hl] = '\0';

    if (colon && colon[1] != '\0') {
        const char *d = colon + 1;
        long v = 0;
        for (; *d; d++) {
            if (*d < '0' || *d > '9') return -1;
            v = v * 10 + (*d - '0');
            if (v > 65535) return -1;
        }
        if (v < 1) return -1;
        snprintf(port, ps, "%ld", v);
    } else {
        snprintf(port, ps, "%d", defport);
    }
    return 0;
}

/* ------------------------------------------------------------------ */
/* 接続・中継                                                           */
/* ------------------------------------------------------------------ */

/* 失敗時 -1 を返し errno を設定 */
static int connect_to(const char *host, const char *port, int timeout_ms)
{
    struct addrinfo hints, *res = NULL, *ai;
    memset(&hints, 0, sizeof hints);
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;

    if (getaddrinfo(host, port, &hints, &res) != 0) {
        errno = EHOSTUNREACH;
        return -1;
    }

    int fd = -1, last = ECONNREFUSED;
    for (ai = res; ai; ai = ai->ai_next) {
        fd = socket(ai->ai_family, ai->ai_socktype, ai->ai_protocol);
        if (fd < 0) { last = errno; continue; }

        int fl = fcntl(fd, F_GETFL, 0);
        fcntl(fd, F_SETFL, fl | O_NONBLOCK);

        int r = connect(fd, ai->ai_addr, ai->ai_addrlen);
        if (r < 0 && errno == EINPROGRESS) {
            struct pollfd pf = { .fd = fd, .events = POLLOUT };
            int pr;
            do { pr = poll(&pf, 1, timeout_ms); } while (pr < 0 && errno == EINTR);
            if (pr == 0) { last = ETIMEDOUT; close(fd); fd = -1; continue; }
            if (pr < 0)  { last = errno;     close(fd); fd = -1; continue; }
            int e = 0;
            socklen_t l = sizeof e;
            getsockopt(fd, SOL_SOCKET, SO_ERROR, &e, &l);
            if (e) { last = e; close(fd); fd = -1; continue; }
            r = 0;
        }
        if (r < 0) { last = errno; close(fd); fd = -1; continue; }

        fcntl(fd, F_SETFL, fl);                 /* ブロッキングに戻す */
        int one = 1;
        setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one);
        struct timeval tv = { .tv_sec = 30, .tv_usec = 0 };
        setsockopt(fd, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof tv);
        break;
    }
    freeaddrinfo(res);
    if (fd < 0) errno = last;
    return fd;
}

/* 双方向中継。どちらかが閉じるか、アイドルタイムアウトまで */
static void tunnel(int a, int b)
{
    char buf[BUF_SZ];
    int open_a = 1, open_b = 1;

    while (open_a || open_b) {
        struct pollfd p[2];
        p[0].fd = open_a ? a : -1; p[0].events = POLLIN; p[0].revents = 0;
        p[1].fd = open_b ? b : -1; p[1].events = POLLIN; p[1].revents = 0;

        int r = poll(p, 2, cfg.idle_timeout_ms);
        if (r == 0) break;                       /* idle timeout */
        if (r < 0) {
            if (errno == EINTR) { if (g_stop) break; continue; }
            break;
        }

        if (open_a && (p[0].revents & (POLLIN | POLLHUP | POLLERR))) {
            ssize_t n = recv(a, buf, sizeof buf, 0);
            if (n < 0 && (errno == EINTR || errno == EAGAIN)) {
                /* retry */
            } else if (n <= 0) {
                open_a = 0;
                shutdown(b, SHUT_WR);
            } else if (send_all(b, buf, (size_t)n) < 0) {
                break;
            }
        }
        if (open_b && (p[1].revents & (POLLIN | POLLHUP | POLLERR))) {
            ssize_t n = recv(b, buf, sizeof buf, 0);
            if (n < 0 && (errno == EINTR || errno == EAGAIN)) {
                /* retry */
            } else if (n <= 0) {
                open_b = 0;
                shutdown(a, SHUT_WR);
            } else if (send_all(a, buf, (size_t)n) < 0) {
                break;
            }
        }
    }
}

/* ------------------------------------------------------------------ */
/* HTTP プロキシ                                                        */
/* ------------------------------------------------------------------ */

static void http_error(int fd, int code, const char *reason, const char *extra)
{
    char body[256], resp[768];
    int bl = snprintf(body, sizeof body, "%d %s\n", code, reason);
    int rl = snprintf(resp, sizeof resp,
                      "HTTP/1.1 %d %s\r\n"
                      "Content-Type: text/plain\r\n"
                      "Content-Length: %d\r\n"
                      "Connection: close\r\n"
                      "%s"
                      "\r\n%s",
                      code, reason, bl, extra ? extra : "", body);
    send_all(fd, resp, (size_t)rl);
}

static int errno_to_http(int e, const char **reason)
{
    if (e == ETIMEDOUT) { *reason = "Gateway Timeout"; return 504; }
    *reason = "Bad Gateway";
    return 502;
}

static int is_hdr(const char *p, size_t len, const char *name)
{
    size_t nl = strlen(name);
    return len > nl && strncasecmp(p, name, nl) == 0 && p[nl] == ':';
}

static int find_header(const char *buf, size_t hdr_len, const char *name,
                       char *out, size_t outsz)
{
    const char *p = memchr(buf, '\n', hdr_len);
    if (!p) return 0;
    p++;
    const char *end = buf + hdr_len;
    while (p < end) {
        const char *e = memchr(p, '\n', (size_t)(end - p));
        if (!e) break;
        size_t len = (size_t)(e - p);
        if (len && p[len - 1] == '\r') len--;
        if (len == 0) break;
        if (is_hdr(p, len, name)) {
            const char *v = p + strlen(name) + 1;
            size_t vl = len - strlen(name) - 1;
            while (vl && (*v == ' ' || *v == '\t')) { v++; vl--; }
            while (vl && (v[vl - 1] == ' ' || v[vl - 1] == '\t')) vl--;
            if (vl >= outsz) vl = outsz - 1;
            memcpy(out, v, vl);
            out[vl] = '\0';
            return 1;
        }
        p = e + 1;
    }
    return 0;
}

static void handle_http(int cfd, const char *caddr)
{
    char buf[HDR_MAX];
    size_t len = 0;
    ssize_t hdr_len = -1;

    /* ヘッダ終端 (CRLFCRLF) まで読む */
    for (;;) {
        if (len >= sizeof buf) { http_error(cfd, 431, "Request Header Fields Too Large", NULL); return; }
        ssize_t n = recv(cfd, buf + len, sizeof buf - len, 0);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) return;
        size_t from = len >= 3 ? len - 3 : 0;
        len += (size_t)n;
        for (size_t i = from; i + 3 < len; i++) {
            if (memcmp(buf + i, "\r\n\r\n", 4) == 0) { hdr_len = (ssize_t)(i + 4); break; }
        }
        if (hdr_len >= 0) break;
    }

    /* リクエストライン */
    char *nl = memchr(buf, '\n', (size_t)hdr_len);
    size_t ll = (size_t)(nl - buf);
    if (ll && buf[ll - 1] == '\r') ll--;
    if (ll == 0 || ll >= LINE_MAX_LEN) { http_error(cfd, 400, "Bad Request", NULL); return; }

    char line[LINE_MAX_LEN];
    memcpy(line, buf, ll);
    line[ll] = '\0';

    char method[16], target[LINE_MAX_LEN], version[16];
    if (sscanf(line, "%15s %8191s %15s", method, target, version) != 3) {
        http_error(cfd, 400, "Bad Request", NULL);
        return;
    }
    if (strncasecmp(version, "HTTP/1.", 7) != 0) {
        http_error(cfd, 505, "HTTP Version Not Supported", NULL);
        return;
    }

    /* 認証 */
    if (cfg.auth_enabled) {
        char v[1024];
        int ok = 0;
        if (find_header(buf, (size_t)hdr_len, "Proxy-Authorization", v, sizeof v) &&
            strncasecmp(v, "Basic ", 6) == 0) {
            const char *t = v + 6;
            while (*t == ' ') t++;
            ok = ct_eq(t, cfg.auth_b64);
        }
        if (!ok) {
            http_error(cfd, 407, "Proxy Authentication Required",
                       "Proxy-Authenticate: Basic realm=\"proxy\"\r\n");
            plog("%s auth failed", caddr);
            return;
        }
    }

    char host[256], port[8];
    size_t leftover = len - (size_t)hdr_len;      /* ヘッダ直後に読み込んだ本文 */

    /* ---- CONNECT (HTTPS トンネル) ---- */
    if (strcasecmp(method, "CONNECT") == 0) {
        if (parse_hostport(target, 443, host, sizeof host, port, sizeof port) < 0) {
            http_error(cfd, 400, "Bad Request", NULL);
            return;
        }
        int sfd = connect_to(host, port, cfg.connect_timeout_ms);
        if (sfd < 0) {
            int e = errno;
            const char *reason;
            int code = errno_to_http(e, &reason);
            http_error(cfd, code, reason, NULL);
            plog("%s CONNECT %s:%s failed: %s", caddr, host, port, strerror(e));
            return;
        }
        static const char ok[] = "HTTP/1.1 200 Connection Established\r\n\r\n";
        if (send_all(cfd, ok, sizeof ok - 1) < 0) { close(sfd); return; }
        if (leftover && send_all(sfd, buf + hdr_len, leftover) < 0) { close(sfd); return; }
        plog("%s CONNECT %s:%s", caddr, host, port);
        tunnel(cfd, sfd);
        close(sfd);
        return;
    }

    /* ---- 通常の HTTP (絶対URI) ---- */
    if (strncasecmp(target, "http://", 7) != 0) {
        http_error(cfd, 400, "Bad Request: absolute http:// URI required", NULL);
        return;
    }
    const char *auth = target + 7;
    const char *pe = auth + strcspn(auth, "/?#");
    size_t al = (size_t)(pe - auth);
    char authority[512];
    if (al == 0 || al >= sizeof authority) { http_error(cfd, 400, "Bad Request", NULL); return; }
    memcpy(authority, auth, al);
    authority[al] = '\0';

    char *at = strrchr(authority, '@');
    const char *hp = at ? at + 1 : authority;
    if (parse_hostport(hp, 80, host, sizeof host, port, sizeof port) < 0) {
        http_error(cfd, 400, "Bad Request", NULL);
        return;
    }

    char path[LINE_MAX_LEN];
    if (*pe == '/')      snprintf(path, sizeof path, "%s", pe);
    else if (*pe == '?') snprintf(path, sizeof path, "/%s", pe);
    else                 snprintf(path, sizeof path, "/");

    /* 上流へ送るリクエストを組み立て (hop-by-hop ヘッダを除去) */
    char out[HDR_MAX + 2048];
    size_t o = 0;
    o += (size_t)snprintf(out + o, sizeof out - o, "%s %s %s\r\n", method, path, version);

    int has_host = 0, has_upgrade = 0;
    const char *p = nl + 1;
    const char *end = buf + hdr_len;
    while (p < end) {
        const char *e = memchr(p, '\n', (size_t)(end - p));
        if (!e) break;
        size_t hl = (size_t)(e - p);
        if (hl && p[hl - 1] == '\r') hl--;
        if (hl == 0) break;

        if (is_hdr(p, hl, "Proxy-Connection") || is_hdr(p, hl, "Proxy-Authorization") ||
            is_hdr(p, hl, "Connection") || is_hdr(p, hl, "Keep-Alive")) {
            /* drop */
        } else {
            if (is_hdr(p, hl, "Host")) has_host = 1;
            if (is_hdr(p, hl, "Upgrade")) has_upgrade = 1;
            memcpy(out + o, p, hl);
            o += hl;
            out[o++] = '\r';
            out[o++] = '\n';
        }
        p = e + 1;
    }
    if (!has_host) {
        int v6 = strchr(host, ':') != NULL;
        o += (size_t)snprintf(out + o, sizeof out - o, "Host: %s%s%s%s%s\r\n",
                              v6 ? "[" : "", host, v6 ? "]" : "",
                              strcmp(port, "80") ? ":" : "",
                              strcmp(port, "80") ? port : "");
    }
    o += (size_t)snprintf(out + o, sizeof out - o, "Connection: %s\r\n\r\n",
                          has_upgrade ? "Upgrade" : "close");

    int sfd = connect_to(host, port, cfg.connect_timeout_ms);
    if (sfd < 0) {
        int e = errno;
        const char *reason;
        int code = errno_to_http(e, &reason);
        http_error(cfd, code, reason, NULL);
        plog("%s %s %s:%s failed: %s", caddr, method, host, port, strerror(e));
        return;
    }
    if (send_all(sfd, out, o) < 0 ||
        (leftover && send_all(sfd, buf + hdr_len, leftover) < 0)) {
        close(sfd);
        return;
    }
    plog("%s %s http://%s:%s%s", caddr, method, host, port, cfg.verbose ? path : "");
    tunnel(cfd, sfd);
    close(sfd);
}

/* ------------------------------------------------------------------ */
/* SOCKS5                                                               */
/* ------------------------------------------------------------------ */

static void socks_reply(int fd, unsigned char rep)
{
    unsigned char r[10] = { 5, rep, 0, 1, 0, 0, 0, 0, 0, 0 };
    send_all(fd, r, sizeof r);
}

static void handle_socks5(int cfd, const char *caddr)
{
    unsigned char h[2];
    if (recv_exact(cfd, h, 2) < 0 || h[0] != 5) return;

    unsigned char methods[256];
    if (h[1] && recv_exact(cfd, methods, h[1]) < 0) return;

    unsigned char want = cfg.auth_enabled ? 0x02 : 0x00;
    int found = 0;
    for (int i = 0; i < h[1]; i++) if (methods[i] == want) found = 1;

    unsigned char sel[2] = { 5, found ? want : 0xFF };
    if (send_all(cfd, sel, 2) < 0 || !found) return;

    if (want == 0x02) {                           /* RFC 1929 */
        unsigned char vu[2];
        char user[256], pass[256];
        unsigned char pl;
        if (recv_exact(cfd, vu, 2) < 0 || vu[0] != 1) return;
        if (vu[1] && recv_exact(cfd, user, vu[1]) < 0) return;
        user[vu[1]] = '\0';
        if (recv_exact(cfd, &pl, 1) < 0) return;
        if (pl && recv_exact(cfd, pass, pl) < 0) return;
        pass[pl] = '\0';

        int ok = ct_eq(user, cfg.auth_user) & ct_eq(pass, cfg.auth_pass);
        unsigned char ar[2] = { 1, ok ? 0 : 1 };
        send_all(cfd, ar, 2);
        if (!ok) { plog("%s socks5 auth failed", caddr); return; }
    }

    unsigned char rq[4];
    if (recv_exact(cfd, rq, 4) < 0 || rq[0] != 5) return;
    if (rq[1] != 1) { socks_reply(cfd, 7); return; }       /* CONNECT のみ */

    char host[256], port[8];
    unsigned char pb[2];

    if (rq[3] == 1) {
        unsigned char a[4];
        if (recv_exact(cfd, a, 4) < 0) return;
        inet_ntop(AF_INET, a, host, sizeof host);
    } else if (rq[3] == 3) {
        unsigned char dl;
        if (recv_exact(cfd, &dl, 1) < 0 || dl == 0) return;
        if (recv_exact(cfd, host, dl) < 0) return;
        host[dl] = '\0';
    } else if (rq[3] == 4) {
        unsigned char a[16];
        if (recv_exact(cfd, a, 16) < 0) return;
        inet_ntop(AF_INET6, a, host, sizeof host);
    } else {
        socks_reply(cfd, 8);
        return;
    }
    if (recv_exact(cfd, pb, 2) < 0) return;
    snprintf(port, sizeof port, "%u", (unsigned)((pb[0] << 8) | pb[1]));

    int sfd = connect_to(host, port, cfg.connect_timeout_ms);
    if (sfd < 0) {
        int e = errno;
        unsigned char rep = 1;
        switch (e) {
        case ECONNREFUSED: rep = 5; break;
        case ENETUNREACH:  rep = 3; break;
        case EHOSTUNREACH:
        case ETIMEDOUT:    rep = 4; break;
        default: break;
        }
        socks_reply(cfd, rep);
        plog("%s SOCKS5 %s:%s failed: %s", caddr, host, port, strerror(e));
        return;
    }
    socks_reply(cfd, 0);
    plog("%s SOCKS5 %s:%s", caddr, host, port);
    tunnel(cfd, sfd);
    close(sfd);
}

/* ------------------------------------------------------------------ */
/* ワーカースレッド / メイン                                            */
/* ------------------------------------------------------------------ */

typedef struct {
    int fd;
    char addr[80];
} client_t;

static void *worker(void *arg)
{
    client_t c = *(client_t *)arg;
    free(arg);

    struct timeval tv = { .tv_sec = cfg.hdr_timeout_s, .tv_usec = 0 };
    setsockopt(c.fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv);
    setsockopt(c.fd, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof tv);
    int one = 1;
    setsockopt(c.fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one);

    unsigned char b;
    ssize_t n;
    do { n = recv(c.fd, &b, 1, MSG_PEEK); } while (n < 0 && errno == EINTR);
    if (n == 1) {
        if (b == 0x05) handle_socks5(c.fd, c.addr);
        else           handle_http(c.fd, c.addr);
    }

    close(c.fd);
    __atomic_fetch_sub(&g_active, 1, __ATOMIC_SEQ_CST);
    return NULL;
}

static void on_signal(int sig) { (void)sig; g_stop = 1; }

static int listen_on(const char *addr, const char *port)
{
    struct addrinfo hints, *res, *ai;
    memset(&hints, 0, sizeof hints);
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    hints.ai_flags = AI_PASSIVE;

    int rc = getaddrinfo(addr, port, &hints, &res);
    if (rc) {
        fprintf(stderr, "getaddrinfo: %s\n", gai_strerror(rc));
        return -1;
    }
    int fd = -1;
    for (ai = res; ai; ai = ai->ai_next) {
        fd = socket(ai->ai_family, ai->ai_socktype, ai->ai_protocol);
        if (fd < 0) continue;
        int one = 1, zero = 0;
        setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
        if (ai->ai_family == AF_INET6)
            setsockopt(fd, IPPROTO_IPV6, IPV6_V6ONLY, &zero, sizeof zero);
        if (bind(fd, ai->ai_addr, ai->ai_addrlen) == 0 && listen(fd, 128) == 0) break;
        close(fd);
        fd = -1;
    }
    freeaddrinfo(res);
    if (fd < 0) perror("bind/listen");
    return fd;
}

static void usage(const char *prog)
{
    fprintf(stderr,
        "Usage: %s [options]\n"
        "  -b ADDR     待ち受けアドレス (default: 127.0.0.1, 全開放: 0.0.0.0 / ::)\n"
        "  -p PORT     待ち受けポート (default: 8080)\n"
        "  -m N        同時接続数の上限 (default: 512)\n"
        "  -c SEC      上流への接続タイムアウト秒 (default: 10)\n"
        "  -t SEC      アイドルタイムアウト秒 (default: 300)\n"
        "  -a USER:PASS 認証を有効化 (環境変数 PROXY_AUTH でも指定可)\n"
        "  -v          詳細ログ\n"
        "  -h          このヘルプ\n", prog);
}

int main(int argc, char **argv)
{
    const char *auth_arg = getenv("PROXY_AUTH");
    int opt;
    while ((opt = getopt(argc, argv, "b:p:m:c:t:a:vh")) != -1) {
        switch (opt) {
        case 'b': cfg.bind_addr = optarg; break;
        case 'p': cfg.port = optarg; break;
        case 'm': cfg.max_conn = atoi(optarg); break;
        case 'c': cfg.connect_timeout_ms = atoi(optarg) * 1000; break;
        case 't': cfg.idle_timeout_ms = atoi(optarg) * 1000; break;
        case 'a': auth_arg = optarg; break;
        case 'v': cfg.verbose = 1; break;
        default:  usage(argv[0]); return opt == 'h' ? 0 : 1;
        }
    }
    if (cfg.max_conn < 1) cfg.max_conn = 1;

    if (auth_arg && *auth_arg) {
        const char *col = strchr(auth_arg, ':');
        if (!col || col == auth_arg || (size_t)(col - auth_arg) > 255 || strlen(col + 1) > 255) {
            fprintf(stderr, "認証指定は USER:PASS 形式 (各255文字以内) で指定してください\n");
            return 1;
        }
        size_t ul = (size_t)(col - auth_arg);
        memcpy(cfg.auth_user, auth_arg, ul);
        cfg.auth_user[ul] = '\0';
        snprintf(cfg.auth_pass, sizeof cfg.auth_pass, "%s", col + 1);
        b64enc((const unsigned char *)auth_arg, strlen(auth_arg), cfg.auth_b64);
        cfg.auth_enabled = 1;
    }

    signal(SIGPIPE, SIG_IGN);
    struct sigaction sa;
    memset(&sa, 0, sizeof sa);
    sa.sa_handler = on_signal;                     /* SA_RESTART なし: accept を中断させる */
    sigaction(SIGINT, &sa, NULL);
    sigaction(SIGTERM, &sa, NULL);

    int lfd = listen_on(cfg.bind_addr, cfg.port);
    if (lfd < 0) return 1;

    plog("listening on %s:%s (HTTP/CONNECT/SOCKS5, auth=%s, max=%d)",
         cfg.bind_addr, cfg.port, cfg.auth_enabled ? "on" : "off", cfg.max_conn);
    if (!cfg.auth_enabled && strcmp(cfg.bind_addr, "127.0.0.1") != 0 &&
        strcmp(cfg.bind_addr, "::1") != 0)
        plog("WARNING: 認証なしで外部に公開されています (オープンプロキシになります)");

    pthread_attr_t attr;
    pthread_attr_init(&attr);
    pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED);
    pthread_attr_setstacksize(&attr, 512 * 1024);

    while (!g_stop) {
        struct sockaddr_storage ss;
        socklen_t sl = sizeof ss;
        int cfd = accept(lfd, (struct sockaddr *)&ss, &sl);
        if (cfd < 0) {
            if (errno == EINTR || errno == ECONNABORTED) continue;
            if (errno == EMFILE || errno == ENFILE) { usleep(100000); continue; }
            perror("accept");
            break;
        }

        if (__atomic_load_n(&g_active, __ATOMIC_SEQ_CST) >= cfg.max_conn) {
            close(cfd);
            continue;
        }

        client_t *c = malloc(sizeof *c);
        if (!c) { close(cfd); continue; }
        c->fd = cfd;
        char ip[64] = "?", sv[16] = "?";
        getnameinfo((struct sockaddr *)&ss, sl, ip, sizeof ip, sv, sizeof sv,
                    NI_NUMERICHOST | NI_NUMERICSERV);
        snprintf(c->addr, sizeof c->addr, "%s:%s", ip, sv);

        __atomic_fetch_add(&g_active, 1, __ATOMIC_SEQ_CST);
        pthread_t th;
        if (pthread_create(&th, &attr, worker, c) != 0) {
            __atomic_fetch_sub(&g_active, 1, __ATOMIC_SEQ_CST);
            close(cfd);
            free(c);
        }
    }

    plog("shutting down");
    close(lfd);
    pthread_attr_destroy(&attr);
    return 0;
}
