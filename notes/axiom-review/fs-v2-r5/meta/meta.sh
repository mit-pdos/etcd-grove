#!/bin/bash
# fs-v2-r5 (b): run one metaops scenario on a filesystem of configuration C behind dm-log-writes,
# then replay.py rebuilds the disk at every flush/FUA point of the log (the states a crash can
# leave on a device that honours flushes), recovers each by a kernel mount (as a boot), and checks it against the
# model's journal order.
# Usage: meta.sh WORKDIR SCENARIO [MOUNTOPTS (default commit=1)] [SLEEP]
set -u
H=$(cd "$(dirname "$0")" && pwd)
. "$H/../../fs-config/mkfs-mount.sh"
D=${1:?workdir}; SC=${2:?scenario}; OPTS=${3:-commit=1}; SLEEP=${4:-}
mkdir -p "$D"
sudo umount "$D/mnt" 2>/dev/null; sudo dmsetup remove r5lw 2>/dev/null
(cd "$H" && GOTOOLCHAIN=go1.27.3 go build -o "$D/metaops" metaops.go) || exit 1
L=$(c_mkfs "$D/c.img")
# the starting state, made durable before the log starts
c_mount "$L" "$D/mnt"
R=$D/mnt
case $SC in
  segdir) printf 'garbage!' > "$R/seg.tmp" ;;
  replace) printf 'old.....' > "$R/target" ;;
  overlap) mkdir "$R/a" "$R/b" ;;
  xrename) mkdir "$R/a" "$R/b" "$R/c"; for k in $(seq 0 399); do : > "$R/a/f$k"; : > "$R/b/f$k"; done ;;
esac
sync; sudo umount "$D/mnt"
sudo cp --sparse=always "$D/c.img" "$D/base.img"
rm -f "$D/log.img"; truncate -s 2G "$D/log.img"
LL=$(sudo losetup --find --show "$D/log.img")
SZ=$(sudo blockdev --getsz "$L")
echo "0 $SZ log-writes $L $LL" | sudo dmsetup create r5lw
c_mount /dev/mapper/r5lw "$D/mnt" "$OPTS"
c_check "$D/mnt" || exit 1
sudo dmsetup message r5lw 0 mark start
MARK=r5lw; case $SC in overlap|xrename) MARK= ;; esac
sudo env LWMARK=$MARK "$D/metaops" "$D/mnt" "$SC" $SLEEP > "$D/ops.$SC.txt" || exit 1
sleep 3
sudo umount "$D/mnt"
sudo dmsetup message r5lw 0 mark end 2>/dev/null
sudo dmsetup remove r5lw
sudo losetup -d "$L"
sudo python3 -I "$H/replay.py" "$D/base.img" "$LL" "$SC" "$D/ops.$SC.txt" "$D"
sudo losetup -d "$LL"
