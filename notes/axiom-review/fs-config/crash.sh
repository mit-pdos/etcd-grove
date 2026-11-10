#!/bin/bash
# A crash of configuration C (README.md) with the journal's writes on disk and the data's not:
# the interleaving where ext4 has committed metadata (sizes, extents) whose data is still in
# flight. A dm table maps the journal's blocks linearly and every other block through dm-delay
# (writes held $DELAY ms; reads and flushes pass), so commits reach the backing file at once and
# data does not; a copy of the backing file taken then is the crash, and c_recover replays it (a kernel mount, as a boot).
#
# Usage: crash.sh WORKDIR SCENARIO [MOUNTOPTS]
# Scenarios (each from a synced file f; the outcome the Fs v2 crash rule allows in brackets):
#   append-new    f = 4096 zero bytes; pwrite 07 at 4096 (a new block)
#                 [size 4096, or 4097 with byte 4096 = 00 (the page's durable zeros) or 07]
#   empty-write   f empty; pwrite 07 at 0
#                 [size 0, or 1 with byte 0 = 00 or 07]
#   append-end    f = 1 byte 00 whose block holds 00 07 on disk past the size (a crash left it:
#                 make-stale below); pwrite 05 at 2, in the block holding the end
#                 [size 1, or 3 with bytes 00 {07 or 00} {00 or 05}: the end page's sectors keep
#                  their on-disk bytes, stale ones included]
#   keep-size     f = 4096 zero bytes, fallocate(KEEP_SIZE, 4096, 4096) synced; pwrite 07 at 4096
#                 [size 4096, or 4097 with byte 4096 = 00 or 07]
#   shrink-grow   f = 8192 bytes 0a; ftruncate 100; fsync; ftruncate 8192
#                 [size 100, or 8192 with bytes 100.. = 00]
# MOUNTOPTS: extra mount options (default commit=1); a non-C option (dioread_lock) is a contrast.
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
. "$HERE/mkfs-mount.sh"
D=${1:?workdir}
SC=${2:?scenario}
OPTS=${3:-commit=1}
DELAY=${DELAY:-20000}
mkdir -p "$D"
IMG=$D/c.img
sudo umount "$D/mnt" "$D/mnt2" 2>/dev/null; sudo dmsetup remove cdelay 2>/dev/null
L=$(c_mkfs "$IMG")
F0=$D/mnt/f
if [ "$SC" = append-end ]; then
  # make-stale: a synced 1-byte file 00, then 07 at 1 written back without its size committed
  # (commit=300 holds the journal), copied (the crash) and recovered: size 1, block 00 07
  c_mount "$L" "$D/mnt" commit=300
  printf '\x00' > "$F0"; sync "$F0"; sudo sync
  xfs_io -c "pwrite -S 0x07 1 1" "$F0" >/dev/null
  xfs_io -c "sync_range -abw 0 0" "$F0"
  sudo cp "$IMG" "$IMG.pre"; sudo umount "$D/mnt"; sudo losetup -d "$L"
  mv "$IMG.pre" "$IMG"; L=$(sudo losetup --find --show "$IMG")
  c_recover "$L"
  B=$(sudo debugfs -R "bmap /f 0" "$L" 2>/dev/null | tail -1)
  echo "start: size $(sudo debugfs -R 'stat /f' "$L" 2>/dev/null | awk '/Size:/ {print $NF; exit}'), block $B on disk: $(sudo dd if="$IMG" bs=4096 skip="$B" count=1 2>/dev/null | od -An -tx1 -N3)"
fi
# the journal's extent (inode 8), in 4 KiB blocks
J=$(sudo debugfs -R "ex <8>" "$L" 2>/dev/null | awk 'NR>1 && $0 ~ /-/ {print}' | head -1)
JS=$(echo "$J" | awk '{print $(NF-3)}'); JE=$(echo "$J" | awk '{print $(NF-1)}')
[ -z "$JS" ] && { echo "no journal extent: $J"; exit 1; }
TOT=$(sudo blockdev --getsz "$L"); S0=$((JS*8)); S1=$(((JE+1)*8))
sudo dmsetup create cdelay <<EOF
0 $S0 delay $L 0 0 $L 0 $DELAY $L 0 0
$S0 $((S1-S0)) linear $L $S0
$S1 $((TOT-S1)) delay $L $S1 0 $L $S1 $DELAY $L $S1 0
EOF
c_mount /dev/mapper/cdelay "$D/mnt" "$OPTS"
CHK=""; case ",$OPTS," in *,dioread_lock,*) CHK="--allow dioread_nolock" ;; esac
c_check "$D/mnt" $CHK || { [ -z "$CHK" ] && exit 1; }
F=$D/mnt/f
case $SC in
  append-new|keep-size) head -c 4096 /dev/zero > "$F" ;;
  empty-write) : > "$F" ;;
  shrink-grow) head -c 8192 /dev/zero | tr '\0' '\n' > "$F" ;;
  append-end) ;;
  *) echo "unknown scenario $SC"; exit 2 ;;
esac
[ "$SC" = keep-size ] && xfs_io -c "falloc -k 4096 4096" "$F"
sync "$F"; sudo sync
python3 -c "import time; time.sleep($DELAY/1000+2)"
OLD=$(cat /proc/sys/vm/dirty_writeback_centisecs)
sudo sysctl -q vm.dirty_writeback_centisecs=0
case $SC in
  append-new|keep-size) xfs_io -c "pwrite -S 0x07 4096 1" "$F" >/dev/null ;;
  empty-write) xfs_io -c "pwrite -S 0x07 0 1" "$F" >/dev/null ;;
  append-end) xfs_io -c "pwrite -S 0x05 2 1" "$F" >/dev/null ;;
  shrink-grow) xfs_io -c "truncate 100" -c fsync -c "truncate 8192" "$F" ;;
esac
xfs_io -c "sync_range -w 0 0" "$F"
python3 -c 'import time; time.sleep(4)'
echo "live: size $(stat -c %s "$F"); $(sudo filefrag -v "$F" | grep -E '^ +[0-9]+:' | tr -s ' ' | tr '\n' ';')"
sudo cp "$IMG" "$IMG.crash"
sudo sysctl -q vm.dirty_writeback_centisecs="$OLD"
sudo umount "$D/mnt"; sudo dmsetup remove cdelay; sudo losetup -d "$L"
L2=$(sudo losetup --find --show "$IMG.crash")
c_recover "$L2"
echo "crash image: size $(sudo debugfs -R 'stat /f' "$L2" 2>/dev/null | awk '/Size:/ {print $NF; exit}'); extents: $(sudo debugfs -R 'ex /f' "$L2" 2>/dev/null | tail -n +2 | tr -s ' ' | tr '\n' ';')"
c_mount "$L2" "$D/mnt2"
F2=$D/mnt2/f
echo "after recovery ($SC${3:+, $3}): size $(stat -c %s "$F2"); bytes 0-3: $(od -An -tx1 -N4 "$F2"); bytes 96-103: $(od -An -tx1 -j96 -N8 "$F2"); byte 4096: $(od -An -tx1 -j4096 -N1 "$F2")"
sudo umount "$D/mnt2"; sudo losetup -d "$L2"
