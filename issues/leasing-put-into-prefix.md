---
upstream: unchecked
checked: 2026-10-17
links:
  - etcd-io/etcd#22083 issue open: related, not this bug (the delete case)
  - etcd-io/etcd#22118 pr open: reserves the prefix for deletes only; this case remains
---

# leasing: a put through the leasing KV into its prefix overwrites a lease key, and writers of the key hang

**Status**: bug (a liveness failure: writes block until their context ends), and an unstated
precondition (the prefix given to `NewKV` is reserved, `doc.go` does not say so; etcd#22118 adds
the sentence for deletes only).

**Where**: `client/v3/leasing/kv.go` at the pinned etcd revision `09669450f`: `put` (`kv.go:246`)
accepts any key, including `pfx + k`; `monitorLease` (`kv.go:159`, the loop at `kv.go:175-187`)
returns without rescinding on a `"REVOKE"` whose lease is not its own; `revoke`/`waitRescind`
(`kv.go:423`, `kv.go:207`) wait for the lease key's deletion.

**What happens**: client 1 holds `b` (lease key `pfx/b` with its session lease). Client 2 runs
`lkv2.Put(ctx, "pfx/b", "x")`: the leasing put treats `pfx/b` as a data key, and the write
replaces the lease key with a record of lease `0`, keeping its create revision. Then
`lkv2.Put(ctx, "b", "v2")`: `revoke` writes `"REVOKE"` to `pfx/b` with `WithIgnoreLease` (lease
still `0`); client 1's `monitorLease` sees a lease that is not its own and returns without
rescinding; `waitRescind` waits for a delete of `pfx/b` that never comes (the record has no
lease, so no session expiry removes it either). The put of `b` blocks until its context ends,
for every leasing client, for as long as `pfx/b` exists. Reproduction:
`TestLeasingPutIntoPrefixBlocksWriters` in `notes/pr-verify/etcd-22118/leasing_prefix_put_test.go`
on branch `pr-verify/etcd-22118` (`context deadline exceeded` after 5 s, at the pin and at
etcd#22118's head); the same through a leasing `Txn` put, with the holder's `Get` stale:
`TestReview22118TxnPutIntoPrefix` in `notes/pr-verify/etcd-22118/leasing_review22118_test.go`.

**Expected**: a put of a user key completes; the leasing KV keeps users out of its protocol
keys, or documents that keys under the prefix must not be written through it.

**How the proof handles it**: the protocol premise (`LeasingStepOk` (2),
`Proof/go_etcd_io/etcd/client/v3/leasing/InvLeasingModel.lean:83`) assumes a lease key that keeps
its create revision keeps its lease; the leasing KV's own `put` of `pfx ++ k` breaks it, so the
deployment premise `LeasingProtocol` excludes this run. The put's spec (`leasingKV.put.spec`,
`putCommitted`) states the write as it happens; the liveness of `waitRescind` is not specified
(its spec allows waiting until the context is done).

**Possible fixes**: reject puts (and transactions with puts) whose key has the prefix, as
etcd#22118 does for deletes; or document the reservation for every write.

**Found**: 2026-10-17, while verifying etcd-io/etcd#22118 (checking what the PR's reservation of
the prefix leaves out).
