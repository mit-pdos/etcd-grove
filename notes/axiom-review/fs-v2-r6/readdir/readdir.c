// fs-v2-r6 (d): can a directory read on C return a name twice that no call touched while it ran?
// The model's DirReadNext (Impl.lean) excludes it. A directory of N names (one 4 KiB block, linear
// format while it fits) is read with getdents64 through a small buffer; after the first batch, M new
// names are created (enough to overflow block 0, which converts the directory to an htree:
// make_indexed_dir); the read goes on to the end. Prints the names returned more than once that are
// among the original N (untouched by the creates).
// Usage: readdir DIR N M BUF
#define _GNU_SOURCE
#include <dirent.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/syscall.h>
#include <unistd.h>

struct d64 { unsigned long ino; long off; unsigned short reclen; unsigned char type; char name[]; };

int main(int argc, char **argv) {
  const char *dir = argv[1];
  int n = atoi(argv[2]), m = atoi(argv[3]), bsz = atoi(argv[4]);
  char p[4096];
  for (int i = 0; i < n; i++) {
    snprintf(p, sizeof p, "%s/orig%05d", dir, i);
    int fd = open(p, O_CREAT | O_WRONLY, 0644); if (fd < 0) { perror(p); return 2; } close(fd);
  }
  int dfd = open(dir, O_RDONLY | O_DIRECTORY);
  static int seen[100000];
  char *buf = malloc(bsz);
  int batch = 0, dup = 0, total = 0;
  for (;;) {
    long r = syscall(SYS_getdents64, dfd, buf, bsz);
    if (r < 0) { perror("getdents64"); return 2; }
    if (r == 0) break;
    for (long o = 0; o < r;) {
      struct d64 *e = (struct d64 *)(buf + o);
      int k;
      if (sscanf(e->name, "orig%05d", &k) == 1) {
        total++;
        if (seen[k]++) { dup++; if (dup <= 5) printf("duplicate untouched name %s (batch %d)\n", e->name, batch); }
      }
      o += e->reclen;
    }
    if (batch++ == 0)
      for (int i = 0; i < m; i++) {
        snprintf(p, sizeof p, "%s/new%05d", dir, i);
        int fd = open(p, O_CREAT | O_WRONLY, 0644); close(fd);
      }
  }
  int missing = 0;
  for (int i = 0; i < n; i++) if (!seen[i]) missing++;
  printf("N %d M %d buf %d: %d batches, %d original names returned, %d duplicates, %d missing\n",
         n, m, bsz, batch, total, dup, missing);
  return 0;
}
