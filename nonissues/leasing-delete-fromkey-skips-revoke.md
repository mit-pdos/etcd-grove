---
upstream: none
checked: 2026-11-09
links:
  - etcd-io/etcd#20704 issue closed: related, not this bug (our leasing report, closed by the stale bot; does not list this)
blocks-proof: no
---
# clientv3/leasing: a `WithFromKey` (or empty-key `WithPrefix`) delete does not revoke other clients' leases

A delete through the leasing KV of an open-ended range (`WithFromKey`, or `WithPrefix` of `""`,
whose range end is `"\x00"`) does not make other leasing clients give up the keys they cache in
the range: they keep serving the deleted values.

**Why not an issue:** found by code reading, confirmed by a second reader; no test run yet. Recipe:
two leasing KVs `lkv1`, `lkv2` on one prefix; `Put(ctx, "k", "v")` through a plain client;
`lkv1.Get(ctx, "k")` (caches it); `lkv2.Delete(ctx, "", WithPrefix())`; `lkv1.Get(ctx, "k")` still
returns `v`. Cause: [`revokeRange`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/client/v3/leasing/kv.go) reads the lease keys in `[pfx+key,
pfx+"\x00")`, an empty range for every key at or above `"\x00"` (`inRange` treats `"\x00"` as
open-ended, `revokeRange` does not), so nothing is revoked, and `deleteRangeRPC`'s guard over the
same empty range holds; the delete then also removes the other clients' lease keys, whose
`monitorLease` ignores deletes. The same in a transaction's `guardRanges`. Move to `issues/` with
that test.

## Proof

no: the leasing contract claims for another client's cached key only a past state's record
(W0's serializable read), which a stale entry still is.
