#!/bin/bash
# Fetch the v7.0 kernel files cited in README.md (torvalds/linux mirror) into DIR.
set -eu
D=${1:?dir}; mkdir -p "$D"
for f in mm/filemap.c fs/ext4/file.c fs/ext4/inode.c fs/ext4/super.c fs/read_write.c fs/buffer.c fs/ext4/balloc.c; do
  curl -sfL -o "$D/$(echo "$f" | tr / _)" "https://raw.githubusercontent.com/torvalds/linux/v7.0/$f" && echo "ok $f"
done
