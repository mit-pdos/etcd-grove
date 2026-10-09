#!/bin/bash
# Compile the tool modules into the shared directory toolsbuild/ (done once; read-only afterwards).
src="$(cd "$(dirname "$0")" && pwd)"
SNAP=/home/ubuntu/.claude/jobs/f5d25fd8/tmp/exp/snap
OUT=${OUT:-/home/ubuntu/.claude/jobs/f5d25fd8/tmp/exp/toolsbuild}
export LEAN_PATH=$SNAP/perennial:$SNAP/iris:$SNAP/qq:$SNAP/batteries:$SNAP/btree:$OUT
export PATH=$HOME/.elan/bin:$PATH
cd "$src" || exit 1
for m in Tools/WordGuard Tools/CompactGoals BtreeLib/ListAuto/Attr BtreeLib/ListAuto GroveTactics GroveTools; do
  mkdir -p "$OUT/$(dirname "$m")"
  echo "== $m"
  s=$(date +%s.%N)
  lean "$m.lean" -o "$OUT/$m.olean" -i "$OUT/$m.ilean" || exit 1
  echo "   $(echo "$(date +%s.%N) - $s" | bc) s"
done
