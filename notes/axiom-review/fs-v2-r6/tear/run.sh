#!/bin/bash
# fs-v2-r6 (a): run tear (main.go) on a filesystem of configuration C under tear.bt, with a loop
# writing /proc/sys/vm/compact_memory beside it (COMPACT=0 to omit it).
# Usage: run.sh WORKDIR SKEW WSIZE SECONDS [POOLMIB]
set -u
H=$(cd "$(dirname "$0")" && pwd)
. "$H/../../fs-config/mkfs-mount.sh"
D=${1:?workdir}; SKEW=${2:?skew}; WS=${3:?wsize}; SECS=${4:?seconds}; POOL=${5:-256}
mkdir -p "$D"
sudo umount "$D/mnt" 2>/dev/null
L=$(c_mkfs "$D/c.img")
c_mount "$L" "$D/mnt"
c_check "$D/mnt" || exit 1
(cd "$H" && GOTOOLCHAIN=go1.27.3 go build -o "$D/tear" main.go) || exit 1
OUT=$D/bt.$SKEW.$WS.out
sudo bpftrace -q "$H/tear.bt" tear > "$OUT" 2>&1 &
BT=$!
sleep 3
CP=""
if [ "${COMPACT:-1}" = 1 ]; then
  ( while :; do echo 1 | sudo tee /proc/sys/vm/compact_memory >/dev/null; done ) &
  CP=$!
fi
"$D/tear" "$D/mnt/f" "$SKEW" "$WS" "$SECS" "$POOL"
[ -n "$CP" ] && { kill $CP; wait $CP 2>/dev/null; }
sleep 1; sudo kill -INT $BT; wait $BT 2>/dev/null
echo "skew $SKEW, wsize $WS, ${SECS}s, COMPACT=${COMPACT:-1}:"; grep -v '^$' "$OUT"
sudo umount "$D/mnt"; sudo losetup -d "$L"
