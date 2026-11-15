#!/bin/bash
# fs-v2-r5 (a): run notear (main.go) on a filesystem of configuration C under notear.bt, in each
# mode; with COMPACT=1, a loop writes /proc/sys/vm/compact_memory beside it (migration of the
# process's anonymous pages: the one way a page the program wrote can be absent on C, which has
# no swap, NUMA balancing off on one node, KSM off, THP "madvise" and Go not madvising its heap).
# Usage: run.sh WORKDIR MODE ITERS
set -u
H=$(cd "$(dirname "$0")" && pwd)
. "$H/../../fs-config/mkfs-mount.sh"
D=${1:?workdir}; MODE=${2:?mode}; IT=${3:-20000}
mkdir -p "$D"
sudo umount "$D/mnt" 2>/dev/null
L=$(c_mkfs "$D/c.img")
c_mount "$L" "$D/mnt"
c_check "$D/mnt" || exit 1
(cd "$H" && GOTOOLCHAIN=go1.27.3 go build -o "$D/notear" main.go)
sudo bpftrace -q "$H/notear.bt" > "$D/bt.$MODE.out" 2>&1 &
BT=$!
sleep 3
CP=""
if [ "${COMPACT:-0}" = 1 ]; then
  ( while :; do echo 1 | sudo tee /proc/sys/vm/compact_memory >/dev/null; done ) &
  CP=$!
fi
"$D/notear" "$D/mnt/f" "$MODE" "$IT"
[ -n "$CP" ] && { kill $CP; wait $CP 2>/dev/null; }
sleep 1; sudo kill -INT $BT; wait $BT 2>/dev/null
echo "mode $MODE${COMPACT:+, compaction loop}, $IT writes:"; grep -v '^$' "$D/bt.$MODE.out"
sudo umount "$D/mnt"; sudo losetup -d "$L"
