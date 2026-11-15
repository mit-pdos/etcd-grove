#!/bin/bash
# fs-v2-r6 wal: etcd's real WAL under ../e2e's harness. One round: a C filesystem
# (fs-config/mkfs-mount.sh, check.sh), empty, as the base image; then, behind dm-log-writes, NW
# walw writers (walw run: wal.Create + Save in a loop, each in its own directory w<j>, a
# dm-log-writes mark after every synced Save), NSYNC syncers (walw sync: sync_file_range(WRITE) of
# every WAL segment in a tight loop), a loop writing /proc/sys/vm/compact_memory (COMPACT=0 omits
# it) and wal.bt, for SECS seconds; then the final WAL files and their block maps are taken and
# scan.py checks every logged write of a WAL page and recovers and checks crash images.
#
# Usage: run.sh WORKDIR SECS [ROUNDS] [NW] [NSYNC] [MINB] [MAXB]
# Env: COMPACT=1, STABLE=0 (1: the dm device's stable_writes set before the mount: not C's device,
#      a contrast), MAXIMG=50 (anomalous crash points recovered), NSAMPLE=40 (ordinary crash
#      points recovered, spread over the log), IMG=8G, NOLOG=0 (1: no dm-log-writes, no marks, no
#      scan: the C filesystem mounted directly, for wal.bt's page-cache counts over long runs)
#      RESTART=0 (N: each writer closes and reopens its WAL, wal.Open + ReadAll, every N synced Saves), RGAP=0
#      (us: after each reopen, a random wait up to RGAP before the next Save), ATTR (content: scan.py
#      attributes logged blocks to WAL pages by content, for RESTART runs), KEEPLOG, KEEP (images)
set -u
H=$(cd "$(dirname "$0")" && pwd)
. "$H/../../fs-config/mkfs-mount.sh"
D=${1:?workdir}; SECS=${2:?seconds}; ROUNDS=${3:-1}; NW=${4:-8}; NSYNC=${5:-1}; MINB=${6:-50}; MAXB=${7:-6000}
RESTART=${RESTART:-0}; NOLOG=${NOLOG:-0}; COMPACT=${COMPACT:-1}; STABLE=${STABLE:-0}; MAXIMG=${MAXIMG:-50}; NSAMPLE=${NSAMPLE:-40}; IMG=${IMG:-8G}
mkdir -p "$D"
sudo umount "$D/mnt" 2>/dev/null; sudo dmsetup remove walfslw 2>/dev/null
(cd "$H/walw" && GOTOOLCHAIN=go1.27.3 go build -o "$D/walw" .) || exit 1
echo "wal: ${SECS}s x $ROUNDS rounds, $NW writers ($MINB..$MAXB data bytes a Save), $NSYNC syncers, COMPACT=$COMPACT STABLE=$STABLE"
for r in $(seq 1 "$ROUNDS"); do
  rm -f "$D"/run.*.out "$D"/sync.*.out
  L=$(c_mkfs "$D/c.img" "$IMG")
  c_mount "$L" "$D/mnt"; sync; sudo umount "$D/mnt"
  sudo cp --sparse=always "$D/c.img" "$D/base.img"
  if [ "$NOLOG" = 1 ]; then
    c_mount "$L" "$D/mnt"; c_check "$D/mnt" || exit 1; MK=""
    echo "round $r: no log; loop stable_writes $(cat /sys/block/"$(basename "$L")"/queue/stable_writes)"
  else
  rm -f "$D/log.img"; truncate -s 40G "$D/log.img"
  LL=$(sudo losetup --find --show "$D/log.img")
  SZ=$(sudo blockdev --getsz "$L")
  echo "0 $SZ log-writes $L $LL" | sudo dmsetup create walfslw
  DM=$(basename "$(readlink -f /dev/mapper/walfslw)")
  [ "$STABLE" = 1 ] && echo 1 | sudo tee /sys/block/"$DM"/queue/stable_writes >/dev/null
  c_mount /dev/mapper/walfslw "$D/mnt"
  c_check "$D/mnt" || exit 1
  echo "round $r: $DM stable_writes $(cat /sys/block/"$DM"/queue/stable_writes), loop $(cat /sys/block/"$(basename "$L")"/queue/stable_writes)"
  sudo dmsetup message walfslw 0 mark start
  MK=walfslw
  fi
  sudo bpftrace -q "$H/wal.bt" > "$D/bt.$r.out" 2>&1 &
  BT=$!
  sleep 4
  CP=""
  if [ "$COMPACT" = 1 ]; then
    ( while :; do echo 1 | sudo tee /proc/sys/vm/compact_memory >/dev/null; done ) &
    CP=$!
  fi
  PIDS=""
  DIRS=""; for j in $(seq 0 $((NW-1))); do DIRS="$DIRS $D/mnt/w$j"; done
  for s in $(seq 1 "$NSYNC"); do sudo "$D/walw" sync "$SECS" $DIRS > "$D/sync.$s.out" & PIDS="$PIDS $!"; done
  for j in $(seq 0 $((NW-1))); do sudo RESTART="$RESTART" RGAP="${RGAP:-0}" "$D/walw" run "$D/mnt/w$j" "$SECS" "$j" "$MINB" "$MAXB" $MK > "$D/run.$j.out" & PIDS="$PIDS $!"; done
  wait $PIDS
  [ -n "$CP" ] && { kill $CP; wait $CP 2>/dev/null; }
  sleep 1; sudo kill -INT $BT; wait $BT 2>/dev/null
  cat "$D"/run.*.out "$D"/sync.*.out
  grep -v '^$' "$D/bt.$r.out" | grep -v '^WB-TORN' ; echo "WB-TORN lines: $(grep -c '^WB-TORN' "$D/bt.$r.out")"
  # the final WAL files (Close synced them) and their block maps
  if [ "$NOLOG" = 1 ]; then sudo umount "$D/mnt"; sudo losetup -d "$L"; continue; fi
  rm -rf "$D/maps"; mkdir -p "$D/maps"
  for j in $(seq 0 $((NW-1))); do
    f=$(sudo ls "$D/mnt/w$j" | grep "\.wal$"); echo "w$j/$f" > "$D/maps/path.$j"
    sudo cp "$D/mnt/w$j/$f" "$D/maps/final.$j"
  done
  sudo umount "$D/mnt"
  sudo dmsetup message walfslw 0 mark end 2>/dev/null
  sudo dmsetup remove walfslw
  for j in $(seq 0 $((NW-1))); do
    sudo debugfs -R "ex /$(cat "$D/maps/path.$j")" "$L" 2>/dev/null > "$D/maps/ex.$j"
  done
  sudo losetup -d "$L" "$LL"
  echo "log: $(du -h "$D/log.img" | cut -f1)"
  sudo ATTR="${ATTR:-}" python3 -I "$H/scan.py" "$D/base.img" "$D/log.img" "$D/maps" "$NW" "$D" "$MAXIMG" "$NSAMPLE" "$D/walw"
  [ -z "${KEEPLOG:-}" ] && rm -f "$D/log.img"
done
