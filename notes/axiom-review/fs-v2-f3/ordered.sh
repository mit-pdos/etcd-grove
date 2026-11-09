#!/bin/bash
# Does ext4 data=ordered commit a size grown by a change before the change's data?
# (notes/axiom-review/fs-v2.md, F3: the crash rule's ordering of sizes and sector versions)
#
# Usage: ordered.sh WORKDIR CHANGE [FS]
#   CHANGE  append-alloc: pwrite 05 at offset 1 of a synced one-byte file (inside its allocated block)
#           append-new:   pwrite 07 at offset 4096 of a synced one-byte file (a new block)
#           append-gap:   pwrite 09 at offset 3 of a synced one-byte file (inside its allocated block)
#           truncate:     ftruncate a synced one-byte file to 4096
#           falloc:       fallocate(0, 8192) of a synced one-byte file
#   STALE=1 in the environment: the one-byte file holds 00 07 on disk past its size first, as a
#   crash leaves it (f3.sh)
# Periodic writeback is switched off (vm.dirty_writeback_centisecs=0, restored after) and the
# journal commits every second (commit=1): a commit that is not ordered after the data commits the
# size alone (xfs: the log is forced, `shutdown -f`). After 3 s a copy of the mounted image is the crash; its journal is replayed and the
# copy's size and raw bytes are printed.
set -u
D=${1:?workdir}
CH=${2:?change}
FS=${3:-ext4}
mkdir -p "$D/mnt" "$D/mnt2"
IMG=$D/img.$FS
# configuration C (../fs-config/README.md); FS=xfs is a contrast outside C
. "$(dirname "$0")/../fs-config/mkfs-mount.sh"
rm -f "$IMG.crash"
if [ "$FS" = ext4 ]; then LOOP=$(c_mkfs "$IMG"); OPTS=commit=300; c_mount "$LOOP" "$D/mnt" $OPTS
  c_check "$D/mnt" || exit 1
else rm -f "$IMG"; truncate -s 512M "$IMG"; LOOP=$(sudo losetup --find --show "$IMG")
  sudo mkfs.xfs -q -f "$LOOP"; OPTS=nouuid; sudo mount -o $OPTS "$LOOP" "$D/mnt"; fi
sudo chmod 777 "$D/mnt"
F=$D/mnt/f
printf '\x00' > "$F"; sudo sync
if [ "${STALE:-0}" = 1 ]; then
  # stale 07 past the size, as a crash leaves it (f3.sh)
  sudo xfs_io -c "pwrite -S 0x07 1 1" "$F" >/dev/null
  sudo xfs_io -c "sync_range -abw 0 0" "$F"
  sudo cp "$IMG" "$IMG.pre"; sudo umount "$D/mnt"; sudo losetup -d "$LOOP"
  mv "$IMG.pre" "$IMG"
  LOOP=$(sudo losetup --find --show "$IMG")
  if [ "$FS" = ext4 ]; then
    sudo e2fsck -fy "$LOOP" >/dev/null 2>&1
    BLK=$(sudo debugfs -R "bmap /f 0" "$LOOP" 2>/dev/null | tail -1)
    echo "$FS: start: block 0 at $BLK: raw $(sudo dd if="$IMG" bs=4096 skip="$BLK" count=1 2>/dev/null | od -An -tx1 -N2)"
  fi
  sudo mount -o $OPTS "$LOOP" "$D/mnt"
  echo "$FS: start: size $(stat -c %s "$F")"
fi
OLD=$(cat /proc/sys/vm/dirty_writeback_centisecs)
sudo sysctl -q vm.dirty_writeback_centisecs=0
[ "$FS" = ext4 ] && sudo mount -o remount,commit=1 "$D/mnt"
case $CH in
  append-alloc) sudo xfs_io -c "pwrite -S 0x05 1 1" "$F" >/dev/null ;;
  append-gap) sudo xfs_io -c "pwrite -S 0x09 3 1" "$F" >/dev/null ;;
  append-new) sudo xfs_io -c "pwrite -S 0x07 4096 1" "$F" >/dev/null ;;
  truncate) sudo xfs_io -c "truncate 4096" "$F" ;;
  falloc) sudo xfs_io -c "falloc 0 8192" "$F" ;;
esac
echo "$FS: in memory: size $(stat -c %s "$F")"
python3 -c 'import time; time.sleep(3)'
# xfs: force the log to disk and stop the filesystem (its log has no periodic commit to wait for)
[ "$FS" = xfs ] && sudo xfs_io -x -c "shutdown -f" "$D/mnt"
sudo cp "$IMG" "$IMG.crash"
sudo sysctl -q vm.dirty_writeback_centisecs="$OLD"
sudo umount "$D/mnt"; sudo losetup -d "$LOOP"
LOOP2=$(sudo losetup --find --show "$IMG.crash")
if [ "$FS" = ext4 ]; then
  sudo e2fsck -fy "$LOOP2" >/dev/null 2>&1
  SZ=$(sudo debugfs -R 'stat /f' "$LOOP2" 2>/dev/null | awk '/Size:/ {print $NF; exit}')
  echo "$FS: crash image: size $SZ; extents: $(sudo debugfs -R 'ex /f' "$LOOP2" 2>/dev/null | tail -n +2 | tr -s ' ' | tr '\n' ';')"
  for L in 0 1; do
    BLK=$(sudo debugfs -R "bmap /f $L" "$LOOP2" 2>/dev/null | tail -1)
    [ "$BLK" != 0 ] && echo "$FS:   block $L at $BLK: raw $(sudo dd if="$IMG.crash" bs=4096 skip="$BLK" count=1 2>/dev/null | od -An -tx1 -N4)"
  done
fi
sudo mount -o $OPTS "$LOOP2" "$D/mnt2"
F2=$D/mnt2/f
echo "$FS: after recovery: size $(stat -c %s "$F2"), bytes 0-3 $(od -An -tx1 -N4 "$F2"), byte 4096 $(od -An -tx1 -j4096 -N1 "$F2")"
sudo umount "$D/mnt2"; sudo losetup -d "$LOOP2"
