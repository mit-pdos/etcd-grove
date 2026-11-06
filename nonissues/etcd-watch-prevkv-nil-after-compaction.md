---
upstream: known
checked: 2026-11-06
links:
  - etcd-io/etcd#10681 issue open: this behavior ("prevKV not being returned if the previous KV was compacted is suprising behavior"), proposes canceling the watch with ErrCompacted instead; kept open as a known etcd behavior
  - kubernetes/kubernetes#76624 issue closed: the Kubernetes symptom (pod reflector getting DELETE events with a nil object)
  - kubernetes/kubernetes#76675 pr merged: Kubernetes' workaround, its etcd3 watcher's parseEvent turns a non-create event with a nil PrevKv into a watch error
  - kubernetes/kubernetes#131862 pr merged: the apiserver watches storage without PrevKV (merged 2026-10-29), removing Kubernetes' dependency on it
  - etcd-io/etcd#18158 pr closed: robustness-test check that prevKV may be nil for any event once a compaction happened (treats it as an invariant to keep), not merged
  - etcd-io/etcd#17450 pr merged: the earlier robustness check of the same condition; reverted by etcd-io/etcd#17471 (test runtime)
  - etcd-io/etcd#15820 issue open: codifying the Kubernetes-etcd contract, which lists prevKV
blocks-proof: no
---

# v3rpc: a watch with prevKV delivers modifications and deletions with no PrevKv after a compaction

A watch created with `WithPrevKV` that is behind the writes (its events queued on the server)
receives, after a compaction at a revision at or above a queued event's, that event with
`PrevKv == nil`, although the event is a PUT of an existing key or a DELETE; the watch is not
(necessarily) canceled. The send loop reads each event's previous key-value only when it sends
the event (`sws.watchable.Range(..., Rev: ModRevision-1)`,
[watch.go#L446-L456](https://github.com/etcd-io/etcd/blob/cda871cc952195664ebec450b77709c12f2d2a88/server/etcdserver/api/v3rpc/watch.go#L446-L456)),
and drops that read's `ErrCompacted`
([kvstore_txn.go#L81-L83](https://github.com/etcd-io/etcd/blob/cda871cc952195664ebec450b77709c12f2d2a88/server/storage/mvcc/kvstore_txn.go#L81-L83)).

**Why not an issue:** documented behavior: `WithPrevKV` says "If the previous KV is already
compacted, nothing will be returned"
([op.go#L540-L541](https://github.com/etcd-io/etcd/blob/cda871cc952195664ebec450b77709c12f2d2a88/client/v3/op.go#L540-L541)),
as does `WatchCreateRequest.prev_kv`
([rpc.proto#L809-L811](https://github.com/etcd-io/etcd/blob/cda871cc952195664ebec450b77709c12f2d2a88/api/etcdserverpb/rpc.proto#L809-L811)),
and upstream already tracks it as a design question (#10681). The reproduction below is valid
(the real client against an integration-test member, no failpoints), so it is the test #10681 lacks.

**Reproduction:** `TestWatchPrevKVAfterCompaction` in
[`nonissues/etcd-watch-prevkv-nil-after-compaction/watch_prevkv_compact_test.go`](etcd-watch-prevkv-nil-after-compaction/watch_prevkv_compact_test.go),
copied into `tests/integration` at etcd-io/etcd@cda871cc952195664ebec450b77709c12f2d2a88
(2026-11-05), go1.27.3 linux/amd64. One member; 50 keys created; 100 prefix watches with
`WithPrevKV` on one client (one gRPC stream, as a client's watches share it); 16 goroutines
overwrite the keys 2000 times; then `Compact` at the current revision (what a periodic compactor
does), and the watches are read to the end.

```
$ go test ./integration/ -run '^TestWatchPrevKVAfterCompaction$' -count=1
--- FAIL: TestWatchPrevKVAfterCompaction (0.66s)
    watch_prevkv_compact_test.go:147: watch 34: PUT event of existing key "/registry/pods/p040" at revision 847 has no PrevKv (compaction at 2051, applied after the event)
    watch_prevkv_compact_test.go:149: 95024 of 190544 events from 100 watches with WithPrevKV (64 canceled as compacted) had a nil PrevKv, 32789 of them on watches never canceled
FAIL
```

It failed in 40 of 40 runs (two batches of `-count=20`), each delivering 19k to 101k nil-PrevKv
events; in most runs every watch is afterwards canceled as compacted, in at least 2 of the 40 runs (one
shown above) 36 and 57 watches were never canceled. With a single watch (`nwatches = 1`) it
passed 20 of 20 runs: the watch keeps up with the writes.

The interleaving needs no control: the watches' events queue in the server's send loop (100
watches on one stream, each event costing a range read and a send per watch), so the compaction,
applied through raft after the writes, overtakes the queued events. Most lagging watches are later
canceled as compacted too (they turn into unsynced watchers below the compaction), but only after
delivering the nil-PrevKv events; some are never canceled.

## Proof

no: the watch server's proof excludes `prev_kv` (`watchReqOk`,
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvWatchStream.lean`: the send loop's
`PrevKv` read is not modeled), and the Kubernetes etcd3 contract fixes `prevKV` false
(`notes/k8s-etcd3-plan.md`, "4. For the watcher, later"). Lifting that restriction would need a
spec that allows a nil `PrevKv` once the compaction revision passes the event's.

## Notes

For Kubernetes (until #131862, which stops asking for prevKV), the outcome is a spurious watch
error from `parseEvent` (`etcd event received with PrevKv=nil`) and a re-established watch, not
a lost DELETE, since #76675. A fix in etcd would be #10681's proposal: cancel the watch with
`ErrCompacted` (compact revision set) when the previous key-value read fails, instead of sending
the event without it.
