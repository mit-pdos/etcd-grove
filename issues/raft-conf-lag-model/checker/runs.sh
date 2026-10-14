#!/bin/sh
# The runs of notes/reconfiguration-model-check.md, one after another (each under
# 25 GB of memory and 90 minutes; the frontier is spilled to OUTDIR/spill).
# Usage: [ONLY="name ..."] runs.sh BINARY OUTDIR
set -u
bin=$1; out=$2
mkdir -p "$out/spill"
run() {
	name=$1; shift
	if [ -n "${ONLY:-}" ] && ! echo " $ONLY " | grep -q " $name "; then return; fi
	echo "== $name: $*"
	GOMEMLIMIT=24GiB timeout 5400 "$bin" -workers 12 "$@" > "$out/$name.txt" 2>&1
	echo "exit $?"; grep -v '^depth' "$out/$name.txt" | tail -n 3; rm -f "$out"/spill/*
}
B="-tablelog 31 -noparents -spill $out/spill"
# validation: counterexamples in the lagging and crash modes, and the read-index bugs
run lag-all-lc   -n 4 -mode lag -maxt 2 -maxlog 4 -maxconf 2 -maxval 1 -tablelog 30
run lag-1-sms    -n 4 -mode lag -lagnodes 1 -inv sms -maxt 2 -maxlog 4 -maxconf 2 -maxval 1 -tablelog 30
run crash-sms    -n 4 -mode crash -inv sms -maxt 2 -maxlog 4 -maxconf 2 -maxval 1 -tablelog 30
run read-noterm  -n 3 -mode faithful -maxt 2 -maxlog 3 -maxconf 0 -maxval 1 -read -read-no-term-check -tablelog 26
run read-single-a -n 2 -init 2 -mode faithful -maxt 2 -maxlog 4 -maxconf 1 -maxval 1 -read -read-singleton-bug -remself -tablelog 24
run read-single-b -n 3 -mode faithful -maxt 2 -maxlog 4 -maxconf 2 -maxval 1 -read -read-singleton-bug -remself -nostepdown -tablelog 26
# exhaustive, faithful mode
run f-n4-t2-l4-c2-v1        -n 4 -mode faithful -maxt 2 -maxlog 4 -maxconf 2 -maxval 1 -tablelog 30
run f-n3-t3-l5-c2-v1        -n 3 -mode faithful -maxt 3 -maxlog 5 -maxconf 2 -maxval 1 $B
run fj-n4-t2-l5-c1-v1       -n 4 -mode faithful -joint -maxt 2 -maxlog 5 -maxconf 1 -maxval 1 $B
run f-n3-t3-l5-c2-v1-rs     -n 3 -mode faithful -maxt 3 -maxlog 5 -maxconf 2 -maxval 1 -remself -nostepdown -read $B
run f-n4-t2-l4-c2-v1-rs     -n 4 -mode faithful -maxt 2 -maxlog 4 -maxconf 2 -maxval 1 -remself $B
run f-n4-t2-l4-c2-v1-read   -n 4 -mode faithful -maxt 2 -maxlog 4 -maxconf 2 -maxval 1 -read $B
run f-n4-t3-l4-c2-v1        -n 4 -mode faithful -maxt 3 -maxlog 4 -maxconf 2 -maxval 1 $B
run f-n4-t2-l5-c2-v1        -n 4 -mode faithful -maxt 2 -maxlog 5 -maxconf 2 -maxval 1 $B
run f-n5-t2-l4-c2-v1        -n 5 -mode faithful -maxt 2 -maxlog 4 -maxconf 2 -maxval 1 $B
run fj-n4-t2-l5-c2-v0       -n 4 -mode faithful -joint -maxt 2 -maxlog 5 -maxconf 2 -maxval 0 $B
# guard-fix mode
run fix-n4-t2-l4-c2-v1      -n 4 -mode fix -maxt 2 -maxlog 4 -maxconf 2 -maxval 1 $B
run fix1-n4-t2-l4-c2-v1     -n 4 -mode fix -lagnodes 1 -maxt 2 -maxlog 4 -maxconf 2 -maxval 1 $B
run fixj1-n4-t2-l5-c1-v1    -n 4 -mode fix -lagnodes 1 -joint -maxt 2 -maxlog 5 -maxconf 1 -maxval 1 $B
# three nodes, no addable node: the lag mode still fails, the guard-fix mode is exhaustive
run lag-n3-sms              -n 3 -mode lag -inv sms -maxt 2 -maxlog 4 -maxconf 2 -maxval 1 -tablelog 30
run fix-n3-t2-l4-c2-v1      -n 3 -mode fix -maxt 2 -maxlog 4 -maxconf 2 -maxval 1 $B
run fix-n3-t3-l5-c2-v1      -n 3 -mode fix -maxt 3 -maxlog 5 -maxconf 2 -maxval 1 $B
