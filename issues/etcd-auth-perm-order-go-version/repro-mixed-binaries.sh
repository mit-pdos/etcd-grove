#!/usr/bin/env bash
# Mixed-version 2-member etcd cluster (member 1: v3.5.7, Go 1.17.13; member 2: v3.5.9, Go 1.19.9),
# as during a rolling upgrade. A role gets the same grant sequence on both members; a user with it
# then puts key c. Compares the members' KV state and role records.
# Usage: repro.sh ETCD357_DIR ETCD359_DIR RUN_DIR   (each *_DIR holds etcd and etcdctl)
set -u
B1=$1; B2=$2; RUN=$3
mkdir -p "$RUN"
LOG=$RUN/log.txt; : > "$LOG"
EP1=http://127.0.0.1:23791; EP2=http://127.0.0.1:23792
CLUSTER=m1=http://127.0.0.1:23801,m2=http://127.0.0.1:23802
CTL="$B2/etcdctl"

start() { # name bin client peer
  "$2/etcd" --name "$1" --data-dir "$RUN/$1.etcd" \
    --listen-client-urls "$3" --advertise-client-urls "$3" \
    --listen-peer-urls "$4" --initial-advertise-peer-urls "$4" \
    --initial-cluster "$CLUSTER" --initial-cluster-state new \
    --initial-cluster-token permorder >"$RUN/$1.log" 2>&1 &
  echo $!
}
run() { echo "\$ $*" >>"$LOG"; "$@" >>"$LOG" 2>&1; echo "[exit $?]" >>"$LOG"; }

P1=$(start m1 "$B1" $EP1 http://127.0.0.1:23801)
P2=$(start m2 "$B2" $EP2 http://127.0.0.1:23802)
echo "started m1 (v3.5.7) pid $P1, m2 (v3.5.9) pid $P2" >>"$LOG"
for i in $(seq 1 60); do
  $CTL --endpoints=$EP1,$EP2 endpoint health >/dev/null 2>&1 && break; sleep 0.5
done
run "$B1/etcd" --version
run "$B2/etcd" --version
run $CTL --endpoints=$EP1,$EP2 endpoint status -w table

R="$CTL --endpoints=$EP1"
run $R user add root --new-user-password=rootpw
run $R role add root
run $R user grant-role root root
run $R user add u --new-user-password=upw
run $R role add r
run $R user grant-role u r
run $R auth enable
RR="$R --user=root:rootpw"
# The grant sequence (sorttyped seq 0): [key,end) R = read, RW = readwrite.
GRANTS="f,g,RW b,e,R a,c,R b,c,R c,d,R d,e,R f,h,RW e,f,RW a,d,RW d,f,R b,e,RW f,i,RW b,d,R b,e,R c,f,R a,d,R a,d,R f,i,R b,d,R a,c,RW b,e,R"
for g in $GRANTS; do
  IFS=, read -r k e t <<<"$g"
  case $t in R) T=read;; RW) T=readwrite;; esac
  run $RR role grant-permission r $T $k $e
done
sleep 1
run $CTL --endpoints=$EP1 --user=root:rootpw role get r
run $CTL --endpoints=$EP2 --user=root:rootpw role get r
run $CTL --endpoints=$EP1,$EP2 --user=root:rootpw endpoint status -w table

echo "### as u: put c through each member" >>"$LOG"
run $CTL --endpoints=$EP1 --user=u:upw put c via-m1
run $CTL --endpoints=$EP2 --user=u:upw put c via-m2
sleep 1
echo "### compare (serializable reads are member-local)" >>"$LOG"
run $CTL --endpoints=$EP1,$EP2 --user=root:rootpw endpoint status -w table
run $CTL --endpoints=$EP1,$EP2 --user=root:rootpw endpoint hashkv -w table
run $CTL --endpoints=$EP1 --user=root:rootpw get c --consistency=s -w json
run $CTL --endpoints=$EP2 --user=root:rootpw get c --consistency=s -w json
run $CTL --endpoints=$EP1 --user=root:rootpw get c --consistency=s
run $CTL --endpoints=$EP2 --user=root:rootpw get c --consistency=s
run $CTL --endpoints=$EP1 --user=root:rootpw get c --consistency=l
run $CTL --endpoints=$EP2 --user=root:rootpw get c --consistency=l
run $CTL --endpoints=$EP1 --user=root:rootpw role get r
run $CTL --endpoints=$EP2 --user=root:rootpw role get r

kill "$P1" "$P2"; wait "$P1" "$P2" 2>/dev/null
echo "stopped pids $P1 $P2" >>"$LOG"
