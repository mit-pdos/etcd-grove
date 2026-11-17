#!/bin/bash
# Repeated runs of the k8s etcd3 driver with watchers (7f-6 Go): cluster and partition modes, several k.
# Usage: watchruns.sh R "k1 k2 ..." (BIN: the test binary from go test -c; OUT: the log directory;
# K8SETCD3_DECODE passes through). Run it under systemd-run --scope -q -p MemoryMax=32G.
R=$1; KS=$2
BIN=${BIN:-/shared/tmp/k8s7f6/k8setcd3.test}
OUT=${OUT:-/shared/tmp/k8s7f6/runs}
export TMPDIR=/shared/tmp GOWORK=off
mkdir -p $OUT; cd $OUT
for r in $(seq 1 $R); do
  for k in $KS; do
    for sched in cluster isolate election blackhole drop mixed noleader; do
      if [ $sched = cluster ]; then run='^TestMainClusterWatch$'; s=""; else run="^TestMainPartitionWatch\$/^$sched\$"; s=$sched; fi
      if [ $k = 1 ] && [ $sched = noleader ]; then continue; fi
      log=$OUT/r$r-k$k-$sched.log
      start=$(date +%s)
      K8SETCD3_K=$k K8SETCD3_SCHED=$s timeout 600 $BIN -test.run "$run" -test.v -test.count=1 -test.timeout 590s > $log 2>&1
      st=$?
      echo "r=$r k=$k $sched exit=$st $(( $(date +%s) - start ))s $(grep -c -- '--- PASS' $log) pass"
    done
  done
done
