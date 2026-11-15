#!/bin/bash
# Measure decision (1) of notes/bbolt-port-plan.md on configuration C (../fs-config/README.md):
# what a buffered pwrite returns when it cannot write everything, and what the page cache holds.
# Usage: run.sh WORKDIR [CASE...]   (cases of pw/main.go: enospc efbig rlimit signals efault shutdown;
# default all). Runs pw as this (non-root) user; each case on a fresh C filesystem.
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
. "$HERE/../fs-config/mkfs-mount.sh"
W=${1:?workdir}; shift
CASES=${*:-enospc efbig rlimit signals efault shutdown}
mkdir -p "$W"
(cd "$HERE/pw" && GOTOOLCHAIN=go1.27.3 GOPROXY=off GOFLAGS=-mod=mod GOSUMDB=off go build -o "$W/pw" .) || exit 1
for c in $CASES; do
  sudo umount "$W/mnt" 2>/dev/null
  L=$(c_mkfs "$W/c.img")
  c_mount "$L" "$W/mnt"
  echo "== $c"
  c_check "$W/mnt" || { echo "not C"; exit 1; }
  case $c in
    rlimit|efault|shutdown) echo "(contrast: not C; see README.md)" ;;
  esac
  "$W/pw" "$c" "$W/mnt" 2>&1 | cat   # a pipe: rlimit's RLIMIT_FSIZE would cut a redirect to a file
  sudo umount "$W/mnt"; sudo losetup -d "$L"
done
