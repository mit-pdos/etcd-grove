#!/bin/bash
# Fetch the kernel source files eof-page.md cites, at tag $1 (v7.0), into directory $2.
set -u
TAG=$1; OUT=$2
BASE="https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/plain"
mkdir -p "$OUT"; cd "$OUT"
for f in fs/ext4/inode.c fs/ext4/extents.c fs/ext4/page-io.c fs/ext4/readpage.c fs/ext4/file.c fs/ext4/ext4_jbd2.c mm/truncate.c fs/attr.c fs/open.c fs/buffer.c; do
  mkdir -p "$(dirname "$f")"
  curl -sfL "$BASE/$f?h=$TAG" -o "$f" || echo "FAIL $f"
done
wc -l fs/ext4/*.c mm/truncate.c fs/*.c
