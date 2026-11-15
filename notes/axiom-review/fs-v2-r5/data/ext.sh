#!/bin/bash
# fs-v2-r5 (c): an extension past the block holding the end, after a crash left stale bytes on
# disk past the recovered size in that block. Impl.lean's OsFile.resized/written: the bytes
# between the old size and the new one read zeros ("stale bytes included"); fs-v2-f3/f3.sh
# measured it only for extensions inside the end block (to 4 bytes).
#
# 1. (f3.sh's make-stale) a synced 1-byte file 00; pwrite 07 at 1; its page written back with the
#    size not committed (commit=300); the image copied (the crash). On disk: size 1, block 00 07.
# 2. The copy recovered by the kernel (mount replays the journal), the file extended by EXT, and
#    bytes 0-3 read, then again after sync and drop_caches (what the disk now holds).
# Usage: ext.sh WORKDIR EXT
#   EXT: trunc8192 | write5000 | falloc8192 | falloc4096+4096 | keep-write5000 | write4095
set -u
H=$(cd "$(dirname "$0")" && pwd)
. "$H/../../fs-config/mkfs-mount.sh"
D=${1:?workdir}; EXT=${2:?ext}
mkdir -p "$D"
sudo umount "$D/mnt" "$D/mnt2" 2>/dev/null
IMG=$D/c.img
L=$(c_mkfs "$IMG")
c_mount "$L" "$D/mnt" commit=300
c_check "$D/mnt" || exit 1
F=$D/mnt/f
printf '\x00' > "$F"; sync "$F"; sudo sync
xfs_io -c "pwrite -S 0x07 1 1" -c "sync_range -abw 0 0" "$F" >/dev/null
sudo cp --sparse=always "$IMG" "$IMG.crash"
sudo umount "$D/mnt"; sudo losetup -d "$L"
L2=$(sudo losetup --find --show "$IMG.crash")
c_mount "$L2" "$D/mnt2"
F2=$D/mnt2/f
B=$(sudo debugfs -R "bmap /f 0" "$L2" 2>/dev/null | tail -1)
echo "recovered: size $(stat -c %s "$F2"), block $B on disk: $(sudo dd if="$L2" bs=4096 skip="$B" count=1 2>/dev/null | od -An -tx1 -N4)"
case $EXT in
  trunc8192) xfs_io -c "truncate 8192" "$F2" ;;
  write5000) xfs_io -c "pwrite -S 0x09 5000 1" "$F2" >/dev/null ;;
  write4095) xfs_io -c "pwrite -S 0x09 4095 1" "$F2" >/dev/null ;;
  falloc8192) xfs_io -c "falloc 0 8192" "$F2" ;;
  falloc4096+4096) xfs_io -c "falloc 4096 4096" "$F2" ;;
  keep-write5000) xfs_io -c "falloc -k 0 8192" -c "pwrite -S 0x09 5000 1" "$F2" >/dev/null ;;
  *) echo "unknown $EXT"; exit 2 ;;
esac
echo "after $EXT: size $(stat -c %s "$F2"), bytes 0-3: $(od -An -tx1 -N4 "$F2")"
sync; echo 3 | sudo tee /proc/sys/vm/drop_caches >/dev/null
echo "after sync and drop_caches: bytes 0-3: $(od -An -tx1 -N4 "$F2")"
sudo umount "$D/mnt2"; sudo losetup -d "$L2"
