#!/bin/bash
# fs-v2-r5 (c): the durable-zeros rule (Impl.lean: diskSec, OsFile.ofDisk, OsFile.synced,
# CrashFile) against configuration C. One scenario on a C filesystem behind dm-log-writes; then
# dreplay.py rebuilds the disk after every logged write (each prefix of the writes in completion
# order: the states a crash leaves on a device that honours flushes and writes in order), recovers
# each as the kernel does at mount (journal replay and orphan cleanup, no e2fsck), and checks the
# file against what the model allows; then extends the recovered file and checks that the bytes
# past its size read zeros (the model's extension), which exposes any written block a crash left
# past the size.
# Usage: data.sh WORKDIR SCENARIO [MOUNTOPTS (default commit=1)]
# Scenarios (from a synced file f; the model's allowed images in dreplay.py):
#   trunc-race   8192 bytes 'a'; pwrite 'b' over page 1; start its writeback; ftruncate 100 at once
#   shrink       8192 bytes 'a'; ftruncate 100 (no sync)
#   falloc0      4096 bytes 'a'; fallocate(0, 0, 16384)
#   keep-past    100 bytes 'a'; fallocate(KEEP_SIZE, 0, 16384), fsync; pwrite 'b' at 8192
#   gap          100 bytes 'a'; pwrite 'b'x10 at 5000
#   seglog       empty; seglog's Segment and ZeroToEnd: fallocate(0,0,65536); pwrite data at 0;
#                fallocate(KEEP_SIZE,0,65536); fdatasync; ftruncate 8; fallocate(0,0,65536)
#   grow-sync    16384 bytes 'a' (minibolt's four pages); ftruncate 32768; fsync; pwrite 'b'
#                over page 4; fdatasync; pwrite 'c' over page 0
set -u
H=$(cd "$(dirname "$0")" && pwd)
. "$H/../../fs-config/mkfs-mount.sh"
D=${1:?workdir}; SC=${2:?scenario}; OPTS=${3:-commit=1}
mkdir -p "$D"
sudo umount "$D/mnt" 2>/dev/null; sudo dmsetup remove r5lw 2>/dev/null
L=$(c_mkfs "$D/c.img")
c_mount "$L" "$D/mnt"
F=$D/mnt/f
case $SC in
  trunc-race|shrink) head -c 8192 /dev/zero | tr '\0' a > "$F" ;;
  falloc0) head -c 4096 /dev/zero | tr '\0' a > "$F" ;;
  keep-past|gap) head -c 100 /dev/zero | tr '\0' a > "$F" ;;
  seglog) : > "$F" ;;
  grow-sync) head -c 16384 /dev/zero | tr '\0' a > "$F" ;;
  *) echo "unknown $SC"; exit 2 ;;
esac
sync; sudo umount "$D/mnt"
sudo cp --sparse=always "$D/c.img" "$D/base.img"
rm -f "$D/log.img"; truncate -s 2G "$D/log.img"
LL=$(sudo losetup --find --show "$D/log.img")
SZ=$(sudo blockdev --getsz "$L")
echo "0 $SZ log-writes $L $LL" | sudo dmsetup create r5lw
c_mount /dev/mapper/r5lw "$D/mnt" "$OPTS"
c_check "$D/mnt" || exit 1
X() { xfs_io "${@/#/-c}" "$F" >/dev/null; }
SYNCED() { sudo dmsetup message r5lw 0 mark sync; }   # after a sync returned
case $SC in
  trunc-race) X "pwrite -S 0x62 4096 4096" "sync_range -w 4096 4096" "truncate 100" ;;
  shrink) X "truncate 100" ;;
  falloc0) X "falloc 0 16384" ;;
  keep-past) X "falloc -k 0 16384" fsync; SYNCED; X "pwrite -S 0x62 8192 1" ;;
  gap) X "pwrite -S 0x62 5000 10" ;;
  seglog) X "falloc 0 65536" "pwrite -S 0x64 0 8" "falloc -k 0 65536" fdatasync; SYNCED
          X "truncate 8" "falloc 0 65536" ;;
  grow-sync) X "truncate 32768" fsync; SYNCED; X "pwrite -S 0x62 16384 4096" fdatasync; SYNCED
             X "pwrite -S 0x63 0 4096" ;;
esac
sleep 4; sync; sleep 1
sudo umount "$D/mnt"
sudo dmsetup remove r5lw
sudo losetup -d "$L"
sudo python3 -I "$H/dreplay.py" "$D/base.img" "$LL" "$SC" "$D"
sudo losetup -d "$LL"
