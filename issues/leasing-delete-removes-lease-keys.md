---
upstream: known
checked: 2026-10-17
links:
  - etcd-io/etcd#22083 issue open: this bug (a WithFromKey delete through the leasing KV deletes the protocol keys)
  - etcd-io/etcd#22118 pr open: rejects deletes intersecting the prefix (verified on branch pr-verify/etcd-22118)
---

# leasing: a delete through the leasing KV can delete the lease keys, and cached reads go stale

**Status**: bug (a wrong result: stale linearizable reads), reported upstream as etcd-io/etcd#22083.

**Where**: `client/v3/leasing/kv.go` at the pinned etcd revision `09669450f`: `delete` (`kv.go:390`)
and `deleteRange`/`deleteRangeRPC` (`kv.go:373`, `kv.go:350`) forward the user's range unchanged;
transactions (`txn.go`, `serverTxn`) do the same. The lease keys live under the prefix given to
`NewKV` (`doc.go`), in the same keyspace as the user's keys, and nothing reserves it.

**What happens**: `lkv.Delete(ctx, "b", clientv3.WithFromKey())` deletes `["b", "\x00")`, which
contains `pfx/...` whenever `pfx > "b"`: every lease key goes. The holder of a deleted lease key
keeps its cache entry (its `monitorLease` ignores events whose value is not `"REVOKE"`,
`kv.go:180`, and a delete's is empty), and another client's write of the key finds no lease key
to revoke (`revoke`'s `If(CreateRevision(pfx+key) < rev+1)` succeeds, `kv.go:425`), so it is
applied without the holder knowing: the holder's `Get` keeps returning the old value. Reproduction:
`TestLeasingDeleteFromKeyStaleRead` in `notes/pr-verify/etcd-22118/leasing_prefix_put_test.go`
on branch `pr-verify/etcd-22118` (fails at the pin: `expected: "new"`, `actual: "old"`; passes
at the PR's head).

**Expected**: a linearizable `Get` through the leasing KV returns the latest value; user operations
should not touch the protocol's keys (the issue suggests rejecting or splitting such ranges).

**How the proof handles it**: the specs state what the code does: `leasingKV.delete.spec_old`
(`deleteCommitted`) deletes every key of the range, lease keys included. The cached-read
theorem (`leasing_cached_get_stable`, `Proof/go_etcd_io/etcd/client/v3/leasing/Results.lean`)
holds only while the lease key keeps its incarnation (`leased_value_stable`'s `hlv`/`hlb`/`hc`,
`InvLeasingModel.lean`), which this delete ends; nothing claims the cache is fresh after it.

**Possible fixes**: reject deletes whose range intersects `[pfx, GetPrefixRangeEnd(pfx))`
(etcd#22118, proved on branch `pr-verify/etcd-22118`: a successful delete has no key with the
prefix in its range, `LeaseDeleteGuard`), or split the range around the prefix.

**Found**: 2026-10-17, while verifying etcd-io/etcd#22118 (the existing delete spec permits it).
