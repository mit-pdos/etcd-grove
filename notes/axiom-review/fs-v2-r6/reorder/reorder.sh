#!/bin/bash
# fs-v2-r6 (d): round 5's scenario run (fs-v2-r5/meta/meta.sh or fs-v2-r5/data/data.sh, which make
# a C filesystem behind dm-log-writes, run the scenario, and replay in completion order), then
# reorder.py on the same log: every subset of the writes since the last flush (sampled).
# Usage: reorder.sh meta|data WORKDIR SCENARIO [R]
set -u
H=$(cd "$(dirname "$0")" && pwd)
K=${1:?meta|data}; D=${2:?workdir}; SC=${3:?scenario}; R=${4:-6}
R5=$H/../../fs-v2-r5
if [ "$K" = meta ]; then
  SL=2500; case $SC in overlap|xrename) SL=10000 ;; esac
  "$R5/meta/meta.sh" "$D" "$SC" commit=1 "$SL" | grep -E 'crash points|VIOLATION'
else
  "$R5/data/data.sh" "$D" "$SC" | grep -E 'crash points|VIOLATION'
fi
LL=$(sudo losetup --find --show "$D/log.img")
if [ "$K" = meta ]; then
  sudo python3 -I "$H/reorder.py" meta "$D/base.img" "$LL" "$SC" "$D/ops.$SC.txt" "$D" "$R"
else
  sudo python3 -I "$H/reorder.py" data "$D/base.img" "$LL" "$SC" "$D" "$R"
fi
sudo losetup -d "$LL"
