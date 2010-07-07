/*
 * 2008+ Copyright (c) Evgeniy Polyakov <zbr@ioremap.net>
 * All rights reserved.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 */

#include "config.h"

#include <sys/types.h>
#include <sys/stat.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <sys/syscall.h>

#include <ctype.h>
#include <fcntl.h>
#include <errno.h>
#include <unistd.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "elliptics/packet.h"
#include "elliptics/interface.h"

#include "common.h"
#include "backends.h"
#include "hash.h"

#ifndef __unused
#define __unused	__attribute__ ((unused))
#endif

/*
 * Config parser is single-threaded.
 * No locks and simultaneous access from different threads.
 */

#define DNET_CONF_COMMENT	'#'
#define DNET_CONF_DELIMITER	'='

static int dnet_background(void)
{
	pid_t pid;

	pid = fork();
	if (pid == -1) {
		dnet_backend_log(DNET_LOG_ERROR, "Failed to fork to background: %s.\n", strerror(errno));
		return -1;
	}

	if (pid != 0) {
		printf("Daemon pid: %d.\n", pid);
		exit(0);
	}

	setsid();

	close(0);
	close(1);
	close(2);

	return 0;
}

static char *dnet_skip_line(char *line)
{
	int len = strlen(line), i;

	for (i=0; i<len; ++i) {
		if (line[i] == DNET_CONF_COMMENT)
			return NULL;
		if (isspace(line[i]))
			continue;

		return &line[i];
	}

	return NULL;
}

static struct dnet_config dnet_cfg_state;
static char *dnet_cfg_remotes, *dnet_cfg_transform;
static int dnet_daemon_mode;

static int dnet_simple_set(struct dnet_config_backend *b __unused, char *key, char *str)
{
	unsigned long value = strtoul(str, NULL, 0);

	if (!strcmp(key, "max_pending_requests"))
		dnet_cfg_state.max_pending = value;
	else if (!strcmp(key, "io_thread_num"))
		dnet_cfg_state.io_thread_num = value;
	else if (!strcmp(key, "log_mask"))
		dnet_cfg_state.log_mask = value;
	else if (!strcmp(key, "wait_timeout"))
		dnet_cfg_state.wait_timeout = value;
	else if (!strcmp(key, "resend_timeout"))
		dnet_cfg_state.resend_timeout.tv_sec = value;
	else if (!strcmp(key, "join"))
		dnet_cfg_state.join = value;
	else if (!strcmp(key, "daemon"))
		dnet_daemon_mode = value;
	else
		return -1;

	return 0;
}

static int dnet_set_id(struct dnet_config_backend *b __unused, char *key __unused, char *value)
{
	return dnet_parse_numeric_id(value, dnet_cfg_state.id);
}

static int dnet_set_addr(struct dnet_config_backend *b __unused, char *key __unused, char *value)
{
	return dnet_parse_addr(value, &dnet_cfg_state);
}

static int dnet_set_remote_addrs(struct dnet_config_backend *b __unused, char *key __unused, char *value)
{
	dnet_cfg_remotes = strdup(value);
	if (!dnet_cfg_remotes)
		return -ENOMEM;

	return 0;
}

static int dnet_set_transform_functions(struct dnet_config_backend *b __unused, char *key __unused, char *value)
{
	dnet_cfg_transform = strdup(value);
	if (!dnet_cfg_transform)
		return -ENOMEM;

	return 0;
}
static int dnet_set_backend(struct dnet_config_backend *b, char *key __unused, char *value);
	
static int dnet_set_log(struct dnet_config_backend *b __unused, char *key __unused, char *value)
{
	FILE *log;
	int err;

	log = fopen(value, "a");
	if (!log) {
		err = -errno;
		fprintf(stderr, "cnf: failed to open log file '%s': %s.\n", value, strerror(errno));
		return err;
	}

	dnet_cfg_state.log_private = log;
	dnet_cfg_state.log = dnet_common_log;

	return 0;
}


static struct dnet_config_entry dnet_cfg_entries[] = {
	{"max_pending_requests", dnet_simple_set},
	{"io_thread_num", dnet_simple_set},
	{"log_mask", dnet_simple_set},
	{"wait_timeout", dnet_simple_set},
	{"resend_timeout", dnet_simple_set},
	{"id", dnet_set_id},
	{"addr", dnet_set_addr},
	{"remote", dnet_set_remote_addrs},
	{"join", dnet_simple_set},
	{"transform", dnet_set_transform_functions},
	{"backend", dnet_set_backend},
	{"daemon", dnet_simple_set},
	{"log", dnet_set_log},
};

static struct dnet_config_entry *dnet_cur_cfg_entries = dnet_cfg_entries;
static int dnet_cur_cfg_size = ARRAY_SIZE(dnet_cfg_entries);

static struct dnet_config_backend *dnet_cfg_backend, *dnet_cfg_current_backend;
static int dnet_cfg_backend_num;

static int dnet_set_backend(struct dnet_config_backend *current_backend __unused, char *key __unused, char *value)
{
	struct dnet_config_backend *b;
	int i;

	for (i=0; i<dnet_cfg_backend_num; ++i) {
		b = &dnet_cfg_backend[i];

		if (!strcmp(value, b->name)) {
			if (b->size) {
				b->data = malloc(b->size);
				if (!b->data)
					return -ENOMEM;
				memset(b->data, 0, b->size);
			}

			dnet_cur_cfg_entries = b->ent;
			dnet_cur_cfg_size = b->num;
			dnet_cfg_current_backend = b;

			return 0;
		}
	}

	return -ENOENT;
}

int dnet_backend_register(struct dnet_config_backend *b)
{
	dnet_cfg_backend = realloc(dnet_cfg_backend, (dnet_cfg_backend_num + 1) * sizeof(struct dnet_config_backend));
	if (!dnet_cfg_backend)
		return -ENOMEM;

	memcpy(&dnet_cfg_backend[dnet_cfg_backend_num], b, sizeof(struct dnet_config_backend));
	dnet_cfg_backend_num++;

	return 0;
}

struct dnet_node *dnet_parse_config(char *file)
{
	FILE *f;
	char buf[4096], *ptr, *value, *key;
	int err, i, len;
	int line_num = 0;
	struct dnet_node *n;

	f = fopen(file, "r");
	if (!f) {
		err = -errno;
		fprintf(stderr, "cnf: failed to open config file '%s': %s.\n", file, strerror(errno));
		goto err_out_exit;
	}

	dnet_cfg_state.log = dnet_common_log;

	err = dnet_file_backend_init();
	if (err)
		goto err_out_close;
 
#ifdef HAVE_TOKYOCABINET_SUPPORT
	err = dnet_tc_backend_init();
	if (err)
		goto err_out_file_exit;
#endif

	err = dnet_blob_backend_init();
	if (err)
		goto err_out_tc_exit;

	while (1) {
		ptr = fgets(buf, sizeof(buf), f);
		if (!ptr) {
			if (feof(f))
				break;

			err = -errno;
			dnet_backend_log(DNET_LOG_ERROR, "cnf: failed to read config file '%s': %s.\n", file, strerror(errno));
			goto err_out_free;
		}

		line_num++;

		ptr = dnet_skip_line(ptr);
		if (!ptr)
			continue;

		len = strlen(ptr);

		if (len > 1) {
			if (ptr[len - 1] == '\r' || ptr[len - 1] == '\n') {
				ptr[len - 1] = '\0';
				len--;
			}
		}

		if (len > 2) {
			if (ptr[len - 2] == '\r' || ptr[len - 2] == '\n') {
				ptr[len - 2] = '\0';
				len--;
			}
		}

		key = value = NULL;
		err = 0;
		for (i=0; i<len; ++i) {
			if (isspace(ptr[i])) {
				if (key)
					ptr[i] = '\0';
				continue;
			}

			if (!key) {
				key = ptr + i;
				continue;
			}

			if (!value) {
				if (ptr[i] == DNET_CONF_DELIMITER) {
					value = ptr;
					ptr[i] = '\0';
					continue;
				}
				
				if (ptr[i] ==  DNET_CONF_COMMENT) {
					key = value = NULL;
					break;
				}

				continue;
			} else {
				value = ptr + i;
				break;
			}

			key = value = NULL;
			err = -EINVAL;
			fprintf(stderr, "cnf: error in line %d: %s.\n", line_num, ptr);
			goto err_out_free;
		}

		if (err)
			goto err_out_free;
		if (!key || !value)
			continue;

		for (i=0; i<dnet_cur_cfg_size; ++i) {
			if (!strcmp(key, dnet_cur_cfg_entries[i].key)) {
				err = dnet_cur_cfg_entries[i].callback(dnet_cfg_current_backend, key, value);
				dnet_backend_log(DNET_LOG_INFO, "backend: %s, key: %s, value: %s, err: %d\n",
						(dnet_cfg_current_backend) ? dnet_cfg_current_backend->name : "root level",
						ptr, value, err);
				if (err)
					goto err_out_free;

				break;
			}
		}
	}

	if (!dnet_cfg_current_backend) {
		err = -EINVAL;
		goto err_out_free;
	}

	err = dnet_cfg_current_backend->init(dnet_cfg_current_backend, &dnet_cfg_state);
	if (err)
		goto err_out_free;

	n = dnet_node_create(&dnet_cfg_state);
	if (!n)
		goto err_out_cleanup;

	err = dnet_common_add_remote_addr(n, &dnet_cfg_state, dnet_cfg_remotes);
	if (err)
		goto err_out_node_destroy;

	err = dnet_common_add_transform(n, dnet_cfg_transform);
	if (err)
		goto err_out_node_destroy;

	if (dnet_cfg_state.join & DNET_JOIN_NETWORK) {
		err = dnet_join(n);
		if (err)
			goto err_out_node_destroy;
	}

	if (dnet_daemon_mode)
		dnet_background();

	return n;

err_out_node_destroy:
	dnet_node_destroy(n);
err_out_cleanup:
	dnet_cfg_current_backend->cleanup(dnet_cfg_current_backend);
err_out_free:
	free(dnet_cfg_transform);
	free(dnet_cfg_remotes);
err_out_blob_exit:
	dnet_blob_backend_exit();
err_out_tc_exit:
#ifdef HAVE_TOKYOCABINET_SUPPORT
	dnet_tc_backend_exit();
#endif
err_out_file_exit:
	dnet_file_backend_exit();
err_out_close:
	fclose(f);
err_out_exit:
	return NULL;
}

void dnet_backend_log(uint32_t mask, const char *format, ...)
{
	va_list args;
	char buf[1024];
	int buflen = sizeof(buf);

	if (!dnet_cfg_state.log || !(dnet_cfg_state.log_mask & mask))
		return;

	va_start(args, format);
	vsnprintf(buf, buflen, format, args);
	buf[buflen-1] = '\0';
	dnet_cfg_state.log(dnet_cfg_state.log_private, mask, buf);
	va_end(args);
}
