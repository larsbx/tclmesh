/* Linux test-only interposer: observe real fsync/link calls, inject EIO, or
 * terminate after the parent fsync and before claim() can return to import().
 * No production environment-variable hooks are added to the backend. */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static void event(const char *op, const char *kind) {
    const char *log = getenv("CLAIM_PROBE_LOG");
    if (!log) return;
    int fd = open(log, O_WRONLY | O_CREAT | O_APPEND, 0600);
    if (fd < 0) _exit(90);
    char line[128];
    int n = snprintf(line, sizeof(line), "%s %s\n", op, kind);
    if (write(fd, line, n) != n) _exit(91);
    close(fd);
}

int fsync(int fd) {
    int (*real_fsync)(int) = dlsym(RTLD_NEXT, "fsync");
    const char *root = getenv("CLAIM_PROBE_KEYS");
    char proc[64], path[PATH_MAX], claims[PATH_MAX];
    snprintf(proc, sizeof(proc), "/proc/self/fd/%d", fd);
    ssize_t n = readlink(proc, path, sizeof(path) - 1);
    if (!root || n < 0) return real_fsync(fd);
    path[n] = 0;
    snprintf(claims, sizeof(claims), "%s/claims", root);
    const char *kind = !strcmp(path, root) ? "parent" :
        !strcmp(path, claims) ? "claims" :
        !strncmp(path, claims, strlen(claims)) &&
        path[strlen(claims)] == '/' ? "file" : NULL;
    if (!kind) return real_fsync(fd);
    event("before", kind);
    const char *fail = getenv("CLAIM_PROBE_FAIL");
    if (fail && !strcmp(fail, kind)) {
        event("fail", kind);
        errno = EIO;
        return -1;
    }
    int result = real_fsync(fd);
    if (result) return result;
    event("synced", kind);
    if (!strcmp(kind, "parent") && getenv("CLAIM_PROBE_EXIT")) _exit(86);
    return result;
}

int link(const char *old, const char *new) {
    int (*real_link)(const char *, const char *) = dlsym(RTLD_NEXT, "link");
    int result = real_link(old, new);
    if (!result) event("linked", "claim");
    return result;
}
