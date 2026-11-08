#!/bin/bash
# F3 crash test (notes/axiom-review/fs-v2.md, F3): can bytes a crash left on disk past a file's
# recovered size be seen after the file is extended?
#
# Usage: f3.sh WORKDIR EXTEND [FS]
#   WORKDIR  a scratch directory (a 256 MiB image file and two mount points go there)
#   EXTEND   truncate | write | falloc: how the recovered file is extended
#   FS       ext4 (default) or xfs
# Needs root (losetup, mount) and xfs_io, e2fsprogs.
#
# 1. A one-byte file holding 00, synced (block allocated, size 1 committed).
# 2. pwrite 07 at offset 1 (in the same block), not synced.
# 3. sync_file_range writes the data page back without committing the journal (commit=300 keeps
#    the periodic commit away): on disk, the block holds 00 07 and the inode's size is 1.
# 4. The crash: a copy of the image taken while mounted, then the journal replayed (e2fsck).
# 5. The copy mounted, the file extended, bytes 0-3 read.
set -u
D=${1:?workdir}
EXT=${2:?truncate|write|falloc}
FS=${3:-ext4}
mkdir -p "$D/mnt" "$D/mnt2"
IMG=$D/img.$FS
rm -f "$IMG" "$IMG.crash"; truncate -s 256M "$IMG"
LOOP=$(sudo losetup --find --show "$IMG")
if [ "$FS" = ext4 ]; then sudo mkfs.ext4 -q -F "$LOOP"; OPTS=data=ordered,commit=300
else sudo mkfs.xfs -q -f "$LOOP"; OPTS=nouuid; fi
sudo mount -o $OPTS "$LOOP" "$D/mnt"
sudo chmod 777 "$D/mnt"
F=$D/mnt/f
printf '\x00' > "$F"; sudo sync
sudo xfs_io -c "pwrite -S 0x07 1 1" "$F" >/dev/null
sudo xfs_io -c "sync_range -abw 0 0" "$F"
echo "$FS: in memory: size $(stat -c %s "$F"), bytes $(od -An -tx1 -N2 "$F")"
sudo cp "$IMG" "$IMG.crash"
sudo umount "$D/mnt"; sudo losetup -d "$LOOP"
LOOP2=$(sudo losetup --find --show "$IMG.crash")
if [ "$FS" = ext4 ]; then
  sudo e2fsck -fy "$LOOP2" >/dev/null 2>&1   # replays the journal
  BLK=$(sudo debugfs -R "bmap /f 0" "$LOOP2" 2>/dev/null | tail -1)
  SZ=$(sudo debugfs -R 'stat /f' "$LOOP2" 2>/dev/null | awk '/Size:/ {print $NF; exit}')
  RAW=$(sudo dd if="$IMG.crash" bs=4096 skip="$BLK" count=1 2>/dev/null | od -An -tx1 -N2)
  echo "$FS: crash image: size $SZ, raw bytes of block $BLK: $RAW"
fi
sudo mount -o $OPTS "$LOOP2" "$D/mnt2"
F2=$D/mnt2/f
echo "$FS: after recovery: size $(stat -c %s "$F2")"
case $EXT in
  truncate) sudo xfs_io -c "truncate 4" "$F2" ;;
  write) sudo xfs_io -c "pwrite -S 0x09 3 1" "$F2" >/dev/null ;;
  falloc) sudo xfs_io -c "falloc 0 4" "$F2" ;;
esac
echo "$FS: after $EXT to 4 bytes: bytes $(od -An -tx1 -N4 "$F2")"
sudo umount "$D/mnt2"; sudo losetup -d "$LOOP2"
