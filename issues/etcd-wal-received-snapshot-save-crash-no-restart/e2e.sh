#!/bin/bash
# A three-member cluster of etcd built with failpoints. Member 3 is killed, the others write past
# their snapshot, and member 3 is restarted: the leader sends it a snapshot. Failpoint sleeps slow
# member 3's raft loop (raftBeforeSave, raftBeforeAdvance) and the snapshot's receipt
# (snapDBRenameBeforeDirSync) so that the snapshot and the leader's next MsgApp land in one Ready;
# writes made while the snapshot is received give that MsgApp > 128 KiB of entries. walBeforeSync
# is set to sleep while the loop sleeps before that Ready's SaveSnap (raftBeforeSaveSnap), and
# member 3 is killed (kill -9) during that sleep, after the Ready's entries reached the WAL file
# and before its hard state did. Member 3 then fails to restart, every time.
BIN=${BIN:?set BIN to the bin/ of an etcd build with failpoints (gofail enable server/etcdserver/ server/etcdserver/api/snap/ server/storage/wal/)}
D=${D:-$PWD/run}
VAL=${VAL:-60000}
rm -rf "$D"; mkdir -p "$D"
CL="m1=http://127.0.0.1:32380,m2=http://127.0.0.1:32480,m3=http://127.0.0.1:32580"
start() { # name idx extra-env...
  local n=$1 i=$2; shift 2
  env "$@" $BIN/etcd --name $n --data-dir $D/$n --listen-client-urls http://127.0.0.1:32${i}79 \
    --advertise-client-urls http://127.0.0.1:32${i}79 --listen-peer-urls http://127.0.0.1:32${i}80 \
    --initial-advertise-peer-urls http://127.0.0.1:32${i}80 --initial-cluster $CL \
    --initial-cluster-state ${STATE:-new} --snapshot-count 20 --snapshot-catchup-entries 5 --log-level ${LOGLEVEL:-info} \
    >>$D/$n.log 2>&1 &
  echo $! > $D/$n.pid
}
EP=http://127.0.0.1:32379,http://127.0.0.1:32479
start m1 3; start m2 4; start m3 5
sleep 3
$BIN/etcdctl --endpoints $EP put warm x >/dev/null || exit 2
kill -9 $(cat $D/m3.pid); sleep 3
put() { for r in 1 2 3 4 5; do $BIN/etcdctl --endpoints $EP --command-timeout 10s put "$@" >/dev/null 2>&1 && return 0; sleep 1; done; return 1; }
V=$(head -c $VAL /dev/zero | tr '\0' 'v')
for k in $(seq 1 60); do put k$k "$V" || { echo put failed; exit 2; }; done
# idle the cluster right after the leader's snapshot: its applied index = its raft snapshot index
# (then the merged snapshot it sends has the index raft probes from: MsgApp(prev = snapshot index))
lead_ep() { $BIN/etcdctl --endpoints $EP endpoint status -w json | python3 -c '
import json,sys
for e in json.load(sys.stdin):
    st=e["Status"]
    if st["header"]["member_id"]==st["leader"]: print(e["Endpoint"], st["raftAppliedIndex"])'; }
for k in $(seq 200 260); do
  put s$k x
  sleep 0.3
  read LE AI < <(lead_ep)
  LN=m1; [ "$LE" = http://127.0.0.1:32479 ] && LN=m2
  SI=$(grep '"saved snapshot to disk"' $D/$LN.log | tail -1 | grep -o '"snapshot-index":[0-9]*' | cut -d: -f2)
  [ "$SI" = "$AI" ] && { echo "leader $LN idle at snapshot $SI"; break; }
done
STATE=existing start m3 5 GOFAIL_HTTP=127.0.0.1:32590 \
  GOFAIL_FAILPOINTS="raftBeforeSave=sleep(${S1:-1500});raftBeforeAdvance=sleep(${S2:-400});raftBeforeSaveSnap=sleep(3000);snapDBRenameBeforeDirSync=sleep(${D3:-900})"
# once the snapshot is being received, give the leader new entries (> 128 KiB) to send after it
for t in $(seq 1 600); do grep -q '"receiving database snapshot"' $D/m3.log && break; sleep 0.02; done
PP=""; for k in 1 2 3 4; do put n$k "$V" & PP="$PP $!"; done
# arm walBeforeSync (a sleep) once the apply goroutine has the snapshot (the raft loop sleeps before SaveSnap)
for t in $(seq 1 600); do
  if grep -q '"applying snapshot"' $D/m3.log; then
    curl -s -X PUT -d 'sleep(8000)' http://127.0.0.1:32590/walBeforeSync; echo "armed at $t"
    # SaveSnap follows in 3 s (raftBeforeSaveSnap), then the Save, which blocks before its fsync:
    # kill -9 inside that window (a gofail panic would run raftNode's deferred WAL Close, which flushes)
    sleep 6; kill -9 $(cat $D/m3.pid); echo "killed m3"; break; fi
  sleep 0.05
done
wait $PP
sleep 6
echo "--- m3 first run tail"; grep -E 'panic|applying snapshot|saved snapshot' $D/m3.log | cut -c1-300 | tail -5
kill -9 $(cat $D/m3.pid) 2>/dev/null; sleep 1
mv $D/m3.log $D/m3.run1.log; cp -a $D/m3/member/wal $D/wal-crash
STATE=existing start m3 5
sleep 6
echo "--- m3 restart"; grep -E '"level":"(fatal|panic)"|failed to|slice bounds' $D/m3.log | cut -c1-400 | head -5
kill -9 $(cat $D/m1.pid) $(cat $D/m2.pid) $(cat $D/m3.pid) 2>/dev/null
