#!/bin/bash
# C-I2 case 2 (the .snap.db recovery) on configuration C (../fs-config/README.md): power losses while
# received snapshots are saved as the fork's SaveDBFrom does (temporary file, fsync, link to
# <k>.snap.db, remove the temporary, directory fsync), each followed by a WAL record fdatasynced in
# another directory (the raft loop's SaveSnap) and the release of <k-2>.snap.db (ReleaseSnapDBs: no
# directory sync). Method as ../c-i1-nopath/rename-window.sh: a dm linear device over the loop
# device, frozen at a random moment (`dmsetup suspend --nolockfs`), the image and the step log
# copied, resumed; each copy recovered as a boot does (c_recover) and checked by `snapdbcrash check`:
# no .snap.db torn or partial, none missing whose directory sync returned or whose WAL record
# survived, unless released. Prints one line per crash and exits 1 if one is BAD.
#
# Usage: snapdb-crash.sh BIN WORKDIR [N] [MOUNTOPTS]   (BIN: the built snapdbcrash; N default 30)
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
. "$HERE/../fs-config/mkfs-mount.sh"
BIN=${1:?bin}; D=${2:?workdir}; N=${3:-30}; OPTS=${4:-}
mkdir -p "$D"; IMG=$D/c.img
sudo umount "$D/mnt" 2>/dev/null; sudo dmsetup remove csd 2>/dev/null
L=$(c_mkfs "$IMG")
TOT=$(sudo blockdev --getsz "$L")
echo "0 $TOT linear $L 0" | sudo dmsetup create csd
c_mount /dev/mapper/csd "$D/mnt" $OPTS
c_check "$D/mnt" || exit 1
for k in $(seq 1 "$N"); do
  "$BIN" setup "$D/mnt/r$k"; sync
  rm -f "$D/log$k"
  "$BIN" run "$D/mnt/r$k" "$D/log$k" & P=$!
  python3 -c "import random, time; time.sleep(random.uniform(0.05, 2.5))"
  sudo dmsetup suspend --nolockfs csd
  cp "$D/log$k" "$D/log$k.crash"
  sudo cp --sparse=always "$IMG" "$D/crash$k.img"
  sudo dmsetup resume csd
  kill -9 $P; wait $P 2>/dev/null
  rm -rf "$D/mnt/r$k"
done
sudo umount "$D/mnt"; sudo dmsetup remove csd; sudo losetup -d "$L"
bad=0
for k in $(seq 1 "$N"); do
  L2=$(sudo losetup --find --show "$D/crash$k.img")
  c_recover "$L2" $OPTS
  M=$(mktemp -d)
  sudo mount -t ext4 -o ro "$L2" "$M"
  out=$("$BIN" check "$M/r$k" "$D/log$k.crash")
  echo "crash $k: $out"
  case "$out" in BAD*) bad=1 ;; esac
  sudo umount "$M"; rmdir "$M"; sudo losetup -d "$L2"; sudo rm -f "$D/crash$k.img"
done
rm -f "$IMG"
exit $bad
