#!/bin/bash
# fs-v2-r6 wal: count writes into a folio under writeback (wb.bt) on a C filesystem (no log):
# the positive control (../e2e's tearw writers, which rewrite a page without syncing) and the WAL
# (walw writers, with RESTART as run.sh), each beside a tight sync_file_range syncer.
# Usage: wbcount.sh WORKDIR SECS tearw|walw [NW]     Env: RESTART=0, RGAP=0, MINB=50, MAXB=6000
set -u
H=$(cd "$(dirname "$0")" && pwd)
. "$H/../../fs-config/mkfs-mount.sh"
D=${1:?workdir}; SECS=${2:?seconds}; WHO=${3:?tearw|walw}; NW=${4:-8}
MINB=${MINB:-50}; MAXB=${MAXB:-6000}
mkdir -p "$D"; sudo umount "$D/mnt" 2>/dev/null
(cd "$H/walw" && GOTOOLCHAIN=go1.27.3 go build -o "$D/walw" .) || exit 1
(cd "$H/../e2e" && GOTOOLCHAIN=go1.27.3 go build -o "$D/tearw" tearw.go) || exit 1
L=$(c_mkfs "$D/c.img" 16G)
c_mount "$L" "$D/mnt"; c_check "$D/mnt" || exit 1
sudo bpftrace -q "$H/wb.bt" "$WHO" > "$D/wb.out" 2>&1 &
BT=$!; sleep 4
PIDS=""
if [ "$WHO" = tearw ]; then
  "$D/tearw" init "$D/mnt" "$NW"; sync
  "$D/tearw" sync "$D/mnt" "$NW" "$SECS" & PIDS="$PIDS $!"
  for j in $(seq 0 $((NW-1))); do "$D/tearw" write "$D/mnt/f$j" 0 "$SECS" 64 once > /dev/null & PIDS="$PIDS $!"; done
else
  DIRS=""; for j in $(seq 0 $((NW-1))); do DIRS="$DIRS $D/mnt/w$j"; done
  "$D/walw" sync "$SECS" $DIRS & PIDS="$PIDS $!"
  for j in $(seq 0 $((NW-1))); do RESTART=${RESTART:-0} RGAP=${RGAP:-0} "$D/walw" run "$D/mnt/w$j" "$SECS" "$j" "$MINB" "$MAXB" & PIDS="$PIDS $!"; done
fi
wait $PIDS
sudo kill -INT $BT; wait $BT 2>/dev/null
grep -v '^$' "$D/wb.out"
sudo umount "$D/mnt"; sudo losetup -d "$L"; rm -f "$D/c.img"
