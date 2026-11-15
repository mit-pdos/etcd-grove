#!/bin/bash
# fs-v2-r6 (d): readdir.c on a filesystem of configuration C, for a few directory sizes.
# Usage: readdir.sh WORKDIR
set -u
H=$(cd "$(dirname "$0")" && pwd)
. "$H/../../fs-config/mkfs-mount.sh"
D=${1:?workdir}
mkdir -p "$D"
sudo umount "$D/mnt" 2>/dev/null
L=$(c_mkfs "$D/c.img")
c_mount "$L" "$D/mnt"
c_check "$D/mnt" || exit 1
gcc -O1 -o "$D/readdir" "$H/readdir.c" || exit 1
i=0
for n in 100 150 200 240 1000 5000; do
  for bsz in 512 2048; do
    i=$((i+1)); mkdir "$D/mnt/d$i"
    M=200; [ "$n" -gt 300 ] && M=$n; "$D/readdir" "$D/mnt/d$i" "$n" "$M" "$bsz"
    echo "  (directory d$i after: $(lsattr -d "$D/mnt/d$i" | cut -d" " -f1), $(stat -c %s "$D/mnt/d$i") bytes)"
  done
done
sudo umount "$D/mnt"; sudo losetup -d "$L"
