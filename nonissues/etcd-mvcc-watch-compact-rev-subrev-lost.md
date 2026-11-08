---
upstream: none
checked: 2026-11-03
links:
  - etcd-io/etcd#18274 pr merged: related, not this bug (keeps a key's tombstone at the compaction revision; one change of the key there)
  - etcd-io/etcd#19179 issue closed: related, not this bug (a delete event missing from a watch opened at the compaction revision, one change of the key there; fixed by #19188)
  - etcd-io/etcd#22377 pr open: related; with it, a from-key delete then put of a key in the compacted revision keeps the put, and a watch from that revision misses the delete (this behavior)
  - etcd-io/etcd#22395 pr open: related; rejects that transaction at the gRPC layer
blocks-proof: no
---

# mvcc: a watch from exactly the compaction revision loses the earlier changes of a key changed twice in that revision

When one revision `c` changes a key twice (`{c,0}` and `{c,1}`), a compaction at `c` keeps only the
key's last change there, `{c,1}`, yet a watch from `c` is not told it is compacted (only a start
below the compaction revision is): it reads revision `c` from the backend and gets one event where
it got two before the compaction.

**Why not an issue:** a precondition etcd means to meet: a revision changes each key at most once,
which the gRPC layer's `checkIntervals` enforces (a txn putting a key twice, or putting and deleting
it, is rejected as `duplicate key`). The test writes such a revision through mvcc's `TxnWrite`, which
no etcd caller does. The gRPC paths that break the precondition are their own findings:
`issues/etcd-txn-check-intervals-sibling.md` (a put and a delete in sibling nested txns; its watch
test shows this consequence through the client) and the from-key delete then put of
`issues/etcd-compaction-delete-then-put.md` (#22395), where on `main` the compaction loses the value
first (#22376).

## Proof

no: `wsRecvOk` states a watcher's events exactly only for a store whose revisions change each key at
most once, or while the compaction revision is below the watcher's first
(`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/ApiState.lean`); etcd's side of it is
`checkIntervals`'s no-duplicate guarantee, whose gap is `etcd-txn-check-intervals-sibling`'s
(`blocks-proof: yes` there, premise `ReqOp.siblingSafeL`); the tester never compacts.

## Notes

`TestWatchFromCompactRevSameKeyTwice` in
[`nonissues/etcd-mvcc-watch-compact-rev-subrev-lost/watch_from_compact_rev_test.go`](etcd-mvcc-watch-compact-rev-subrev-lost/watch_from_compact_rev_test.go)
(copied as `zz_watch_from_compact_rev_test.go` into `server/storage/mvcc`) fails at
etcd-io/etcd@4b0b745025716b893c64dbee443e3f969931a16b (2026-11-03, go1.27.3):

```
$ (cd server && go test ./storage/mvcc -run '^TestWatchFromCompactRevSameKeyTwice$' -count=1)
--- FAIL: TestWatchFromCompactRevSameKeyTwice (1.02s)
    zz_watch_from_compact_rev_test.go:72: watch from the compaction revision 2: 2 events before the compaction, 1 after
FAIL
```

Where: `keyIndex.doCompact` keeps the first revision with `Main <= atRev` from the newest
([key_index.go#L257-L279](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/storage/mvcc/key_index.go#L257-L279));
`syncWatchers` sends a compaction response only for `w.minRev < compactionRev`
([watchable_store.go#L371](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/storage/mvcc/watchable_store.go#L371)).
If mvcc should hold without the precondition: report a watch from `c` as compacted when `c` had
several changes of one key in its range, or keep every sub-revision of `c` at compaction.
