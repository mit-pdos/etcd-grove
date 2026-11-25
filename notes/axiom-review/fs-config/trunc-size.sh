#!/bin/bash
# An ftruncate's size is exact at a crash (examples/osfs/semantics/data_truncate_size_exact.go), on
# configuration C (README.md). A file synced at 16384 bytes; then a loop of ftruncates (no sync) to the
# targets below, growing and shrinking, not page-aligned; meanwhile the device (a dm linear table over
# the loop device) is frozen at random moments (`dmsetup suspend --nolockfs`: the in-flight requests
# finish, no new one starts, nothing is flushed from the page cache: the device's contents at that
# moment, as a power loss leaves them), copied and resumed. Each copy is recovered as a boot does
# (c_recover: a kernel mount replays the journal and the orphan list) and its size read with debugfs.
# Prints each recovered size and exits 1 if one is neither 16384 nor a target.
#
# Usage: trunc-size.sh WORKDIR [N]   (N crashes, default 40)
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
. "$HERE/mkfs-mount.sh"
D=${1:?workdir}; N=${2:-40}
TARGETS="20007 24581 28673 32768 18000 40961 16384 4097"
mkdir -p "$D"; IMG=$D/c.img
sudo umount "$D/mnt" 2>/dev/null; sudo dmsetup remove ctrunc 2>/dev/null
L=$(c_mkfs "$IMG")
TOT=$(sudo blockdev --getsz "$L")
echo "0 $TOT linear $L 0" | sudo dmsetup create ctrunc
c_mount /dev/mapper/ctrunc "$D/mnt" commit=1
c_check "$D/mnt" || exit 1
F=$D/mnt/f
head -c 16384 /dev/urandom > "$F"; sync "$F"; sudo sync
( while :; do for t in $TARGETS; do truncate -s "$t" "$F"; done; done ) &
LOOP=$!
for k in $(seq 1 "$N"); do
  python3 -c "import random, time; time.sleep(random.uniform(0.05, 1.5))"
  sudo dmsetup suspend --nolockfs ctrunc
  sudo cp --sparse=always "$IMG" "$D/crash$k.img"
  sudo dmsetup resume ctrunc
done
kill $LOOP; wait $LOOP 2>/dev/null
sudo umount "$D/mnt"; sudo dmsetup remove ctrunc; sudo losetup -d "$L"
bad=0; seen=""
for k in $(seq 1 "$N"); do
  L2=$(sudo losetup --find --show "$D/crash$k.img")
  c_recover "$L2"
  SZ=$(sudo debugfs -R 'stat /f' "$L2" 2>/dev/null | awk '/Size:/ {print $NF; exit}')
  sudo losetup -d "$L2"; sudo rm -f "$D/crash$k.img"
  case " 16384 $TARGETS " in *" $SZ "*) ;; *) echo "crash $k: size $SZ: NOT a target"; bad=1 ;; esac
  seen="$seen $SZ"
done
echo "recovered sizes:$seen"
echo "distinct: $(echo $seen | tr ' ' '\n' | sort -n | uniq -c | tr -s ' ' | tr '\n' ';')"
rm -f "$IMG"
exit $bad
