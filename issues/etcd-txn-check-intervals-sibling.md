---
upstream: known
checked: 2026-11-01
links:
  - etcd-io/etcd#16380 issue closed: same bug (put in an earlier nested txn vs delete in a later sibling passes; reversed order rejected); confirmed by ahrtr, closed not planned (stale) in 2025
  - etcd-io/etcd#16395 pr closed: fix for #16380, never merged; ahrtr found its pairwise check too costly and asked for the expected semantics first
  - etcd-io/etcd#22395 pr open: related, not this bug (checkIntervals and from-key deletes)
blocks-proof: yes
---

# etcdserver: a txn may put a key in one nested txn and delete it in a later sibling, though it may not modify a key twice

`Txn` rejects a transaction that modifies one key twice ("duplicate key given in txn request"),
including a delete in one nested transaction and a put in a later one, but accepts the same two
operations in the other order: `Then(OpTxn(nil, [Put(k)], nil), OpTxn(nil, [Delete(k)], nil))`
succeeds and writes a put and a delete of `k` in one revision, so watchers see a put event whose
value never was the key's value at that revision. A compaction at that revision then keeps only the
delete, so a watch from the compaction revision (where a client re-watches from after
`ErrCompacted`) misses the put event it reported before the compaction.

**Reproduction:** `TestTxnSiblingPutThenDelete` in
[`issues/etcd-txn-check-intervals-sibling/txn_sibling_put_delete_test.go`](etcd-txn-check-intervals-sibling/txn_sibling_put_delete_test.go),
copied (as `zz_txn_sibling_put_delete_test.go`) into `tests/integration/clientv3` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28), go1.27.3; the flat txn and the
reversed order are rejected, the last case is not:

```
$ (cd tests && go test ./integration/clientv3 -run '^TestTxnSiblingPutThenDelete$' -count=1)
    zz_txn_sibling_put_delete_test.go:48:
        	Error:      	Expected error with "etcdserver: duplicate key given in txn request" in chain but got nil.
        	Test:       	TestTxnSiblingPutThenDelete
        	Messages:   	txn(put), txn(delete)
FAIL
```

The watch consequence: `TestWatchFromCompactRevAfterSiblingPutDelete` in
[`issues/etcd-txn-check-intervals-sibling/watch_after_compact_test.go`](etcd-txn-check-intervals-sibling/watch_after_compact_test.go),
copied (as `zz_watch_after_compact_test.go`) into `tests/integration/clientv3` at
etcd-io/etcd@a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5 (2026-11-02), go1.27.3 (event types: 0 `PUT`,
1 `DELETE`):

```
$ (cd tests && go test ./integration/clientv3 -run '^TestWatchFromCompactRevAfterSiblingPutDelete$' -count=1)
    zz_watch_after_compact_test.go:66:
        	Error:      	Not equal:
        	            	expected: []mvccpb.Event_EventType{0, 1}
        	            	actual  : []mvccpb.Event_EventType{1}
        	Messages:   	events of revision 3 for a watch from it, before and after compacting at it
FAIL
```

## Proof

yes: what `checkIntervals` gives the transaction's run (each key written at most once per revision,
`v3rpc.check_gives_nodup`, `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/CheckNodup.lean`)
needs the premise `ReqOp.siblingSafeL`, which etcd does not enforce; the client's watch is verified
under it (`srvNoDupKeys`, `Proof/go_etcd_io/etcd/client/v3/InvWatch.lean`).

## Fix

**Branch**: `txn-check-intervals-investigate` in `~/etcd-fixes/txn-check-intervals-investigate` (upamanyus/etcd, not pushed): fc6254021 test and fix
**Base**: etcd-io/etcd@3aaab3479b6c4f5fe1b2b8f33437093c2caae88a

A reverse pass over the level's nested transactions checks each one's puts against the deletes of
the transactions after it (the forward pass already checks the earlier ones), never against its own
else branch: linear in the operations, answering #16395's cost objection (+25 lines in `key.go`;
`siblings` benchmark +32%, only for two or more nested txns at one level).

## Notes

Low impact for reads: a read at that revision sees the delete, and the reverse order, which does
corrupt compaction (`etcd-compaction-delete-then-put`), is rejected. Not harmless to watches,
though (2026-11-01, found by this repository's review of watches across a compaction,
`notes/watch-compaction-plan.md`): `keyIndex.doCompact` keeps one revision of the key at or below the
compaction revision, the tombstone, and `scheduleCompaction` deletes the put's backend key, so a
watch from that revision gets the `DELETE` alone. The root cause is the same (a revision with two
changes of one key), and the cheap fix removes both. With the watch consequence, a follow-up comment
on #16380 has more to say than the cost argument.
