#!/bin/bash
# fs-v2-r6 e2e: catch a torn page on disk. One round: a C filesystem (fs-config/mkfs-mount.sh,
# check.sh) with NW files of one page each, synced; then, behind dm-log-writes, NW writers
# (tearw write: page 0 of f<j> overwritten by one 4096-byte pwrite at a time from a source at
# addr % 4096 = SKEW, never synced), NSYNC syncers (tearw sync: sync_file_range(WRITE) of every
# file's page 0 in a tight loop), a loop writing /proc/sys/vm/compact_memory (COMPACT=0 omits it)
# and tear.bt, for SECS seconds; then scan.py checks every write in the log for a torn page 0 and
# recovers and boots the first torn images.
#
# Usage: e2e.sh WORKDIR SKEW SECS [ROUNDS] [NW] [NSYNC]
# Env: COMPACT=1 (compaction loop), STABLE=0 (1: set the dm device's stable_writes before the
#      mount, so writeback is stable: not C's device, a contrast), MAXIMG=3, POOL=256 (MiB),
#      CHURN=0 (MiB: a tearw churn process, another process's memory churn, beside the loop)
#      FILL=once (each: the writer fills each source slot just before its write)
set -u
H=$(cd "$(dirname "$0")" && pwd)
. "$H/../../fs-config/mkfs-mount.sh"
D=${1:?workdir}; SKEW=${2:?skew}; SECS=${3:?seconds}; ROUNDS=${4:-1}; NW=${5:-4}; NSYNC=${6:-2}
COMPACT=${COMPACT:-1}; STABLE=${STABLE:-0}; MAXIMG=${MAXIMG:-3}; POOL=${POOL:-256}; CHURN=${CHURN:-0}; FILL=${FILL:-once}
mkdir -p "$D"
sudo umount "$D/mnt" 2>/dev/null; sudo dmsetup remove e2elw 2>/dev/null
(cd "$H" && GOTOOLCHAIN=go1.27.3 go build -o "$D/tearw" tearw.go && GOTOOLCHAIN=go1.27.3 go build -o "$D/boot" boot.go) || exit 1
echo "e2e: skew $SKEW, ${SECS}s x $ROUNDS rounds, $NW writers, $NSYNC syncers, COMPACT=$COMPACT STABLE=$STABLE CHURN=$CHURN POOL=$POOL FILL=$FILL"
for r in $(seq 1 "$ROUNDS"); do
  rm -f "$D"/write.*.out "$D"/sync.*.out "$D"/churn.out
  L=$(c_mkfs "$D/c.img")
  c_mount "$L" "$D/mnt"
  "$D/tearw" init "$D/mnt" "$NW" || exit 1
  sync; sudo umount "$D/mnt"
  BL=""
  for j in $(seq 0 $((NW-1))); do
    b=$(sudo debugfs -R "bmap /f$j 0" "$L" 2>/dev/null | tail -1); BL="$BL${BL:+,}$b"
  done
  sudo cp --sparse=always "$D/c.img" "$D/base.img"
  rm -f "$D/log.img"; truncate -s 20G "$D/log.img"
  LL=$(sudo losetup --find --show "$D/log.img")
  SZ=$(sudo blockdev --getsz "$L")
  echo "0 $SZ log-writes $L $LL" | sudo dmsetup create e2elw
  DM=$(basename "$(readlink -f /dev/mapper/e2elw)")
  [ "$STABLE" = 1 ] && echo 1 | sudo tee /sys/block/"$DM"/queue/stable_writes >/dev/null
  c_mount /dev/mapper/e2elw "$D/mnt"
  c_check "$D/mnt" || exit 1
  echo "round $r: blocks $BL; $DM stable_writes $(cat /sys/block/"$DM"/queue/stable_writes), loop $(cat /sys/block/"$(basename "$L")"/queue/stable_writes)"
  sudo dmsetup message e2elw 0 mark start
  sudo bpftrace -q "$H/tear.bt" > "$D/bt.$r.out" 2>&1 &
  BT=$!
  sleep 4
  CP=""
  if [ "$COMPACT" = 1 ]; then
    ( while :; do echo 1 | sudo tee /proc/sys/vm/compact_memory >/dev/null; done ) &
    CP=$!
  fi
  PIDS=""
  [ "$CHURN" != 0 ] && { "$D/tearw" churn "$CHURN" "$SECS" > "$D/churn.out" & PIDS="$PIDS $!"; }
  for s in $(seq 1 "$NSYNC"); do "$D/tearw" sync "$D/mnt" "$NW" "$SECS" > "$D/sync.$s.out" & PIDS="$PIDS $!"; done
  for j in $(seq 0 $((NW-1))); do "$D/tearw" write "$D/mnt/f$j" "$SKEW" "$SECS" "$POOL" "$FILL" > "$D/write.$j.out" & PIDS="$PIDS $!"; done
  wait $PIDS
  [ -n "$CP" ] && { kill $CP; wait $CP 2>/dev/null; }
  sleep 1; sudo kill -INT $BT; wait $BT 2>/dev/null
  cat "$D"/write.*.out "$D"/sync.*.out "$D"/churn.out 2>/dev/null
  grep -v '^$' "$D/bt.$r.out" | grep -v '^WB-TORN' ; echo "WB-TORN lines: $(grep -c '^WB-TORN' "$D/bt.$r.out")"
  sudo umount "$D/mnt"
  sudo dmsetup message e2elw 0 mark end 2>/dev/null
  sudo dmsetup remove e2elw
  sudo losetup -d "$L" "$LL"
  echo "log: $(du -h "$D/log.img" | cut -f1)"
  sudo python3 -I "$H/scan.py" "$D/base.img" "$D/log.img" "$BL" "$D" "$SKEW" "$MAXIMG" "$D/boot"
  rm -f "$D/log.img"
done
