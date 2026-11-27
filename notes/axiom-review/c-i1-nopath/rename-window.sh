#!/bin/bash
# The T10 rename window of C-I1 on configuration C (../fs-config/README.md): power losses while an
# old bbolt database keeps committing to DIR/db after a synced bbolt file DIR/snap.db was renamed
# onto DIR/db (etcd's OpenSnapshotBackend, before the old backend's Close), the new file opened by
# the name and committing, and the directory synced after a random delay (the fork's syncDir).
# Method as trunc-size.sh: a dm linear device over the loop device, frozen at a random moment
# (`dmsetup suspend --nolockfs`), the image and the step log copied, resumed; each copy recovered as
# a boot does (c_recover) and checked by `renamewindow check` against the restated dbCrash:
#   * the name: before RENAMED, db is the old file; after DIRSYNC, the new; in between either, and
#     snap.db exists exactly when db is the old file;
#   * the old file, when named, holds Dl, Dn or the announced commit (last returned - 1, last
#     returned, last announced); the new file the same of its own commits.
# Prints one line per crash and exits 1 if one is BAD.
#
# Usage: rename-window.sh BIN WORKDIR [N] [MOUNTOPTS]   (BIN: the built renamewindow; N default 30)
# RW_FORK=1 (exported): the fork's order, rename, directory sync, then the new open (main.go).
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
. "$HERE/../fs-config/mkfs-mount.sh"
BIN=${1:?bin}; D=${2:?workdir}; N=${3:-30}; OPTS=${4:-}
mkdir -p "$D"; IMG=$D/c.img
sudo umount "$D/mnt" 2>/dev/null; sudo dmsetup remove crw 2>/dev/null
L=$(c_mkfs "$IMG")
TOT=$(sudo blockdev --getsz "$L")
echo "0 $TOT linear $L 0" | sudo dmsetup create crw
c_mount /dev/mapper/crw "$D/mnt" $OPTS
c_check "$D/mnt" || exit 1
rnd() { python3 -c "import random; print(random.randint($1, $2))"; }
for k in $(seq 1 "$N"); do
  "$BIN" setup "$D/mnt/r$k"; sync
  T1=$(rnd 0 200); T2=$(rnd 200 1500)
  rm -f "$D/log$k"
  "$BIN" run "$D/mnt/r$k" "$D/log$k" "$T1" "$T2" & P=$!
  python3 -c "import random, time; time.sleep(random.uniform(0.02, 1.2))"
  sudo dmsetup suspend --nolockfs crw
  cp "$D/log$k" "$D/log$k.crash"
  sudo cp --sparse=always "$IMG" "$D/crash$k.img"
  sudo dmsetup resume crw
  kill -9 $P; wait $P 2>/dev/null
done
sudo umount "$D/mnt"; sudo dmsetup remove crw; sudo losetup -d "$L"
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
