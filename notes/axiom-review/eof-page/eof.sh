#!/bin/bash
# The bytes of the block holding EOF past the size (notes/axiom-review/eof-page.md): what ext4 on
# configuration C (../fs-config/README.md) does with them in the page cache and on disk.
#
# Usage: eof.sh WORKDIR SCENARIO
#
# Start (every scenario): f holds 0x41 below SZ (5000, or 9000 for zerotoend) and the STALE byte
# 0x53 from SZ to the end of its block, on disk, size SZ, synced: the state a crash leaves after an
# append whose data reached disk and whose size did not (fs-v2-f3/f3.sh measured it; here it is
# planted directly: the file written to the end of the block, synced, unmounted, its size set with
# `debugfs -w sif`, remounted).
#
# Synced scenarios (the change, then fsync, unmount, the raw block read back):
#   none          nothing (fsync of a clean file)
#   trunc-eq      ftruncate(SZ)            (the same size: ZeroToEnd at the end)
#   trunc-down    ftruncate(SZ-500)
#   trunc-up-in   ftruncate(SZ+1000)       (inside the block)
#   trunc-up-past ftruncate(8192+1000)     (past the block)
#   falloc-in     fallocate(0, 0, SZ+1000) (inside the block)
#   falloc-past   fallocate(0, 0, 8192+1000)
#   falloc-keep   fallocate(KEEP_SIZE, SZ, 4096)
#   write-append  pwrite 0x42 x10 at SZ    (from the end: no gap)
#   write-gap     pwrite 0x42 x10 at SZ+1000
#   zerotoend     SZ=9000; etcd's ZeroToEnd at 100: ftruncate(100), fallocate(0, 0, 9000); fdatasync
# Power-loss scenarios (crash.sh's method: the journal's blocks linear, every other block behind
# dm-delay, DELAY ms; commit=1; the image copied 4 s after the change, and again DELAY+6 s after):
#   pl-append        pwrite 0x42 x10 at SZ
#   pl-trunc-append  ftruncate(SZ), then pwrite 0x42 x10 at SZ (ZeroToEnd at the end, then a Save)
#   pl-wb-zero       pwrite 0x42 x10 at SZ, fsync (its writeback zeroes the block past SZ+10 on
#                    disk); then pwrite 0x43 x10 at SZ+10
#   pl-wb-zero-bg    the same with no fsync: sync_file_range(WRITE) starts the page's writeback
#                    (as background writeback would), then pwrite 0x43 x10 at SZ+10
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
. "$HERE/../fs-config/mkfs-mount.sh"
D=${1:?workdir}
SC=${2:?scenario}
DELAY=${DELAY:-20000}
mkdir -p "$D"
IMG=$D/c.img
sudo umount "$D/mnt" "$D/mnt2" 2>/dev/null; sudo dmsetup remove cdelay 2>/dev/null
SZ=5000; [ "$SC" = zerotoend ] && SZ=9000
END=$(( (SZ + 4095) / 4096 * 4096 ))
K=$(( SZ / 4096 ))   # the block holding EOF
L=$(c_mkfs "$IMG")
c_mount "$L" "$D/mnt"
F=$D/mnt/f
xfs_io -f -c "pwrite -S 0x41 0 $SZ" -c "pwrite -S 0x53 $SZ $((END - SZ))" -c fsync "$F" >/dev/null
sudo umount "$D/mnt"
sudo debugfs -w -R "sif /f size $SZ" "$L" >/dev/null 2>&1
mread() { python3 -I "$HERE/mread.py" "$@"; }
# raw IMAGE DEV: the block holding EOF, read from IMAGE, at the offsets that matter
raw() {
  local b; b=$(sudo debugfs -R "bmap /f $K" "$2" 2>/dev/null | tail -1)
  if [ "$b" = 0 ]; then echo "block $K: none"; return; fi
  local o=$(( SZ % 4096 ))
  echo "block $K ($b) raw: @SZ-2 $(sudo dd if="$1" bs=4096 skip="$b" count=1 2>/dev/null | od -An -tx1 -j$((o-2)) -N6)" \
    "| @SZ+998 $(sudo dd if="$1" bs=4096 skip="$b" count=1 2>/dev/null | od -An -tx1 -j$((o+998)) -N4)" \
    "| @end-2 $(sudo dd if="$1" bs=4096 skip="$b" count=1 2>/dev/null | od -An -tx1 -j4094 -N2)"
}
case $SC in pl-*) ;; *)
  c_mount "$L" "$D/mnt"
  c_check "$D/mnt" >/dev/null || { c_check "$D/mnt"; exit 1; }
  echo "$SC: start: size $(stat -c %s "$F"); page cache past EOF (mapping) @SZ: $(mread "$F" $SZ 4)"
  case $SC in
    none) ;;
    trunc-eq) xfs_io -c "truncate $SZ" "$F" ;;
    trunc-down) xfs_io -c "truncate $((SZ - 500))" "$F" ;;
    trunc-up-in) xfs_io -c "truncate $((SZ + 1000))" "$F" ;;
    trunc-up-past) xfs_io -c "truncate $((END + 1000))" "$F" ;;
    falloc-in) xfs_io -c "falloc 0 $((SZ + 1000))" "$F" ;;
    falloc-past) xfs_io -c "falloc 0 $((END + 1000))" "$F" ;;
    falloc-keep) xfs_io -c "falloc -k $SZ 4096" "$F" ;;
    write-append) xfs_io -c "pwrite -S 0x42 $SZ 10" "$F" >/dev/null ;;
    write-gap) xfs_io -c "pwrite -S 0x42 $((SZ + 1000)) 10" "$F" >/dev/null ;;
    zerotoend) xfs_io -c "truncate 100" -c "falloc 0 $SZ" "$F" ;;
    *) echo "unknown scenario $SC"; exit 2 ;;
  esac
  N=$(stat -c %s "$F")
  echo "$SC: after: size $N; read @SZ-2: $(od -An -tx1 -j$((SZ-2)) -N6 "$F");" \
    "@SZ+998: $(od -An -tx1 -j$((SZ+998)) -N4 "$F"); mapping @SZ: $(mread "$F" $SZ 4)" \
    "$( [ $(( (N + 4095) / 4096 * 4096 )) -ge $((SZ + 1002)) ] && echo "@SZ+998: $(mread "$F" $((SZ + 998)) 4)")"
  if [ "$SC" = zerotoend ]; then xfs_io -c fdatasync "$F"; else xfs_io -c fsync "$F"; fi
  sudo umount "$D/mnt"
  echo "$SC: on disk after the sync: size $(sudo debugfs -R 'stat /f' "$L" 2>/dev/null | awk '/Size:/ {print $NF; exit}'); extents: $(sudo debugfs -R 'ex /f' "$L" 2>/dev/null | tail -n +2 | tr -s ' ' | tr '\n' ';')"
  echo "$SC: $(raw "$IMG" "$L")"
  sudo losetup -d "$L"
  exit 0 ;;
esac
# power loss: crash.sh's dm table
J=$(sudo debugfs -R "ex <8>" "$L" 2>/dev/null | awk 'NR>1 && $0 ~ /-/ {print}' | head -1)
JS=$(echo "$J" | awk '{print $(NF-3)}'); JE=$(echo "$J" | awk '{print $(NF-1)}')
[ -z "$JS" ] && { echo "no journal extent: $J"; exit 1; }
TOT=$(sudo blockdev --getsz "$L"); S0=$((JS*8)); S1=$(((JE+1)*8))
sudo dmsetup create cdelay <<EOF
0 $S0 delay $L 0 0 $L 0 $DELAY $L 0 0
$S0 $((S1-S0)) linear $L $S0
$S1 $((TOT-S1)) delay $L $S1 0 $L $S1 $DELAY $L $S1 0
EOF
c_mount /dev/mapper/cdelay "$D/mnt" commit=1
c_check "$D/mnt" >/dev/null || { c_check "$D/mnt"; exit 1; }
echo "$SC: start: size $(stat -c %s "$F"); mapping @SZ: $(mread "$F" $SZ 4)"
OLD=$(cat /proc/sys/vm/dirty_writeback_centisecs)
sudo sysctl -q vm.dirty_writeback_centisecs=0
case $SC in
  pl-append) xfs_io -c "pwrite -S 0x42 $SZ 10" "$F" >/dev/null ;;
  pl-trunc-append) xfs_io -c "truncate $SZ" -c "pwrite -S 0x42 $SZ 10" "$F" >/dev/null ;;
  pl-wb-zero-bg) xfs_io -c "pwrite -S 0x42 $SZ 10" -c "sync_range -w 0 0" -c "pwrite -S 0x43 $((SZ + 10)) 10" "$F" >/dev/null ;;
  pl-wb-zero) xfs_io -c "pwrite -S 0x42 $SZ 10" -c fsync -c "pwrite -S 0x43 $((SZ + 10)) 10" "$F" >/dev/null ;;
  *) echo "unknown scenario $SC"; exit 2 ;;
esac
echo "$SC: live: size $(stat -c %s "$F"); read @SZ-2: $(od -An -tx1 -j$((SZ-2)) -N24 "$F")"
python3 -c 'import time; time.sleep(4)'
sudo cp "$IMG" "$IMG.crash1"
python3 -c "import time; time.sleep($DELAY/1000+2)"
sudo cp "$IMG" "$IMG.crash2"
sudo sysctl -q vm.dirty_writeback_centisecs="$OLD"
sudo sync; sudo umount "$D/mnt" || { sleep 5; sudo umount "$D/mnt"; }; sudo dmsetup remove cdelay; sudo losetup -d "$L"
for c in 1 2; do
  L2=$(sudo losetup --find --show "$IMG.crash$c")
  c_recover "$L2"
  echo "$SC: crash image $c ($( [ $c = 1 ] && echo 4 s || echo "$((DELAY/1000+6)) s")): size $(sudo debugfs -R 'stat /f' "$L2" 2>/dev/null | awk '/Size:/ {print $NF; exit}'); $(raw "$IMG.crash$c" "$L2")"
  c_mount "$L2" "$D/mnt2"
  echo "$SC: crash image $c after recovery: size $(stat -c %s "$D/mnt2/f"); read @SZ-2: $(od -An -tx1 -j$((SZ-2)) -N24 "$D/mnt2/f")"
  sudo umount "$D/mnt2"; sudo losetup -d "$L2"
done
