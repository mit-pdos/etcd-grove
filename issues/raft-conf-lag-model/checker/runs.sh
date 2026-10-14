#!/bin/sh
# The runs of notes/reconfiguration-model-check.md, one after another (each under
# 25 GB of memory and 90 minutes; the frontier is spilled to OUTDIR/spill). Usage: runs.sh BINARY OUTDIR [NAME...]
set -u
bin=$1; out=$2; shift 2
mkdir -p "$out/spill"
run() {
	name=$1; shift
	if [ $# -gt 0 ] && [ -n "${ONLY:-}" ] && ! echo " $ONLY " | grep -q " $name "; then return; fi
	echo "== $name: $*"
	GOMEMLIMIT=24GiB timeout 5400 "$bin" -workers 12 "$@" > "$out/$name.txt" 2>&1
	echo "exit $?"; tail -n 3 "$out/$name.txt"; rm -f "$out"/spill/*
}
# validation: the counterexamples (lagging and crash modes)
run lag-all-lc   -n 4 -mode lag -maxt 2 -maxlog 4 -maxconf 2 -maxval 1 -tablelog 30
run lag-1-sms    -n 4 -mode lag -lagnodes 1 -inv sms -maxt 2 -maxlog 4 -maxconf 2 -maxval 1 -tablelog 30
run crash-sms    -n 4 -mode crash -inv sms -maxt 2 -maxlog 4 -maxconf 2 -maxval 1 -tablelog 30
# exhaustive, faithful mode
run f-n4-t2-l4-c2-v1        -n 4 -mode faithful -maxt 2 -maxlog 4 -maxconf 2 -maxval 1 -tablelog 30
run f-n3-t3-l5-c2-v1        -n 3 -mode faithful -maxt 3 -maxlog 5 -maxconf 2 -maxval 1 -tablelog 31 -noparents -spill "$out/spill"
run fj-n4-t2-l5-c1-v1       -n 4 -mode faithful -joint -maxt 2 -maxlog 5 -maxconf 1 -maxval 1 -tablelog 31 -noparents -spill "$out/spill"
run fix-n4-t2-l4-c2-v1      -n 4 -mode fix -maxt 2 -maxlog 4 -maxconf 2 -maxval 1 -tablelog 31 -noparents -spill "$out/spill"
run f-n4-t3-l4-c2-v1        -n 4 -mode faithful -maxt 3 -maxlog 4 -maxconf 2 -maxval 1 -tablelog 31 -noparents -spill "$out/spill"
run f-n4-t2-l5-c2-v1        -n 4 -mode faithful -maxt 2 -maxlog 5 -maxconf 2 -maxval 1 -tablelog 31 -noparents -spill "$out/spill"
run f-n4-t2-l4-c2-v1-read   -n 4 -mode faithful -maxt 2 -maxlog 4 -maxconf 2 -maxval 1 -read -tablelog 31 -noparents -spill "$out/spill"
run f-n5-t2-l4-c2-v1        -n 5 -mode faithful -maxt 2 -maxlog 4 -maxconf 2 -maxval 1 -tablelog 31 -noparents -spill "$out/spill"
run fj-n4-t2-l5-c2-v0       -n 4 -mode faithful -joint -maxt 2 -maxlog 5 -maxconf 2 -maxval 0 -tablelog 31 -noparents -spill "$out/spill"
run fixj-n4-t2-l5-c1-v1     -n 4 -mode fix -joint -maxt 2 -maxlog 5 -maxconf 1 -maxval 1 -tablelog 31 -noparents -spill "$out/spill"
