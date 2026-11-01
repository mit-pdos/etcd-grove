---
upstream: known
checked: 2026-11-01
links:
  - etcd-io/etcd#22376 issue open: same bug (compaction at a delete-and-recreate revision loses the live value)
  - etcd-io/etcd#22377 pr open: fix for #22376 (keyIndex.doCompact; a regression from #18274)
  - etcd-io/etcd#22395 pr open: related; closes the gRPC path to the bug (from-key delete then put in one txn)
blocks-proof: yes
---

# mvcc: compacting at the revision of a txn that deletes a key and puts it again loses the key's value

A transaction that deletes a key and puts it again (accepted through gRPC when the delete is a
from-key delete, `Then(OpDelete(k, WithFromKey()), OpPut(k, v))`), followed by a compaction at
exactly its revision (`etcdctl compact`, or auto-compaction landing on it), deletes the key's live
value from the backend while the index still names it: the next read of the key makes every member
exit (`range failed to find revision pair`), and after a restart the acknowledged value is gone.

**Reproduction:** `TestCompactAtDeleteThenPutRevision` in
[`issues/etcd-compaction-delete-then-put/compact_delete_then_put_test.go`](etcd-compaction-delete-then-put/compact_delete_then_put_test.go),
copied (as `zz_compact_delete_then_put_test.go`) into `tests/integration/clientv3` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28), go1.27.3 (`-v`, since the member
exits the test process):

```
$ (cd tests && go test ./integration/clientv3 -run '^TestCompactAtDeleteThenPutRevision$' -count=1 -v)
    logger.go:146: ... INFO	m0	finished scheduled compaction	{"member": "m0", "compact-revision": 3, ..., "number-of-keys-compacted": 2, ...}
    logger.go:146: ... FATAL	m0	range failed to find revision pair	{"member": "m0", "revision-main": 3, "revision-sub": 1, "revision-current": 3, ...}
FAIL	go.etcd.io/etcd/tests/v3/integration/clientv3	0.264s
```

## Proof

yes: `store.Compact`'s spec takes the premise that the compaction revision does not delete and
re-put one key (`NoDelPutAt`, `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/store__Compact.lean`),
which the gRPC checks give only for transactions without from-key deletes (`noFromKeyDelL`,
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/CheckNodup.lean`).

## Notes

The gRPC path closes with #22395 (or this repository's `etcd-txn-delete-then-ignore-put` fix);
mvcc's own API (`store.Write`: `DeleteRange` then `Put` of one key) stays affected until #22377.
