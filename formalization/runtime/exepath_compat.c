#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/auxv.h>
#include <unistd.h>

/* The managed runtime has no /proc executable symlinks. Fall back to the
 * process's own AT_EXECFN only for its own executable path. No file reads,
 * proof checking, Lean declarations, or access controls are changed. */
ssize_t readlink(const char *path, char *buf, size_t size) {
  static ssize_t (*original)(const char *, char *, size_t);
  if (!original) original = dlsym(RTLD_NEXT, "readlink");
  ssize_t result = original(path, buf, size);
  if (result >= 0) return result;
  char own[64];
  snprintf(own, sizeof own, "/proc/%ld/exe", (long)getpid());
  if (strcmp(path, own) && strcmp(path, "/proc/self/exe")) return result;
  const char *exe = (const char *)getauxval(AT_EXECFN);
  if (!exe || !*exe) return result;
  char *absolute = realpath(exe, NULL);
  if (!absolute) return result;
  size_t n = strlen(absolute);
  if (n > size) n = size;
  memcpy(buf, absolute, n);
  free(absolute);
  return (ssize_t)n;
}
