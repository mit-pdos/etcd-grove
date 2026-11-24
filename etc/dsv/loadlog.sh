#!/bin/bash
# loadlog.sh RUN (as root, DSV_LAB set; experiment.sh starts it with nohup): one line a minute in
# runs/RUN/load.log (load average, lean processes, how many in RUN's container) while RUN's container
# runs
L=${DSV_LAB:?set DSV_LAB}/runs/$1/load.log
S=/sys/fs/cgroup/machine.slice/dsverify-$1.scope
while [ -d "$S" ]; do
    n=0; s=0
    for p in $(pgrep -x lean); do n=$((n+1)); grep -q "dsverify-$1" /proc/$p/cgroup 2>/dev/null && s=$((s+1)); done
    echo "$(date -u +%H:%M) load $(cut -d' ' -f1 /proc/loadavg) lean $n (this run $s)"
    sleep 60
done >>"$L"
