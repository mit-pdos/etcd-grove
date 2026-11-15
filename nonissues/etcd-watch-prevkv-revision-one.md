---
upstream: none
checked: 2026-11-14
links: []
blocks-proof: no
---

# v3rpc: a `prev_kv` watch event at revision 1 would read the current value as its previous one

`sendWatch` reads an event's previous key-value with `Range(key, nil, RangeOptions{Rev:
ModRevision - 1})` (`server/etcdserver/api/v3rpc/watch.go:445-450`). For an event of revision 1
that is `Rev: 0`, which `rangeKeys` reads as the current revision (`rangeRev`), so the event would
carry the key's current record as its `PrevKv`, not the (empty) state before revision 1.

**Why not an issue:** a precondition etcd meets: no event has revision 1. `NewStore` starts at
revision 1 with nothing written (`currentRev = 1`), and the first write is revision 2; mvcc's
model has revisions `0` and `1` empty (`mvcc.api.mvccStart`, kept by every step,
`MvccReachable`). Found by code reading while proving the send loop's `PrevKv` write (k8s 7f-3b);
no test.

## Proof

no: the send loop's fact about a written previous key-value (`v3rpc.pkWritten`,
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvWatch.lean`) states the key's record at
the revision before only for revisions of at least `2`, with the certified log's revision `1`
empty (`v3rpc.reach_rev1`, from `mvccState_reachable.law`), so a reader of a log event (revision
`1` empty) excludes the other case.
