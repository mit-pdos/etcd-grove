#!/bin/bash
# fs-link: run one linkops scenario (snap.SaveDBFrom's calls) on a filesystem of configuration C
# behind dm-log-writes, then lreplay.py rebuilds the disk at every flush/FUA point of the log (the
# states a crash can leave on a device that honours flushes), recovers each by a kernel mount (as
# a boot), and checks it against the SaveDBFrom axiom's link assumptions
# (examples/osfs/semantics/meta_link_crash.go, meta_link_shared_inode.go). The method is
# fs-v2-r5/meta/meta.sh's (round 5, B1), with this scenario.
# Needs: sudo, a loop device, device-mapper with the log-writes target (dm-log-writes), go.
# Usage: link.sh WORKDIR SCENARIO [MOUNTOPTS (default commit=1)] [SLEEP_MS]
#   SCENARIO: snapsave | snapsave-exist (linkops.go)
set -u
H=$(cd "$(dirname "$0")" && pwd)
. "$H/../fs-config/mkfs-mount.sh"
D=${1:?workdir}; SC=${2:?scenario}; OPTS=${3:-commit=1}; SLEEP=${4:-}
mkdir -p "$D"
sudo umount "$D/mnt" 2>/dev/null; sudo dmsetup remove lklw 2>/dev/null
(cd "$H" && GOTOOLCHAIN=go1.27.3 go build -o "$D/linkops" linkops.go) || exit 1
L=$(c_mkfs "$D/c.img")
# the starting state, made durable before the log starts
c_mount "$L" "$D/mnt"
R=$D/mnt
case $SC in
  snapsave-exist) printf 'old' > "$R/0000000000000005.snap.db" ;;
esac
sync; sudo umount "$D/mnt"
sudo cp --sparse=always "$D/c.img" "$D/base.img"
rm -f "$D/log.img"; truncate -s 2G "$D/log.img"
LL=$(sudo losetup --find --show "$D/log.img")
SZ=$(sudo blockdev --getsz "$L")
echo "0 $SZ log-writes $L $LL" | sudo dmsetup create lklw
c_mount /dev/mapper/lklw "$D/mnt" "$OPTS"
c_check "$D/mnt" || exit 1
sudo dmsetup message lklw 0 mark start
sudo env LWMARK=lklw "$D/linkops" "$D/mnt" "$SC" $SLEEP > "$D/ops.$SC.txt" || exit 1
sleep 3
sudo umount "$D/mnt"
sudo dmsetup message lklw 0 mark end 2>/dev/null
sudo dmsetup remove lklw
sudo losetup -d "$L"
sudo python3 -I "$H/lreplay.py" "$D/base.img" "$LL" "$SC" "$D/ops.$SC.txt" "$D"
sudo losetup -d "$LL"
