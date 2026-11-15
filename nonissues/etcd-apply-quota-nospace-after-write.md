---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# apply: a put, a write transaction or a lease grant over the backend quota is applied and answered `ErrNoSpace`

The quota applier (`server/etcdserver/apply/quota.go`, `quotaApplierV3.Put`, `Txn`, `LeaseGrant`)
asks the quota whether the request fits, **applies the request anyway**, and replaces a `nil` error
by `ErrNoSpace` when it did not fit:

```go
ok := a.q.Available(p)
resp, trace, err := a.applierV3.Put(p)
if err == nil && !ok {
	err = errors.ErrNoSpace
}
```

So a client whose write lands while the backend is over its quota (before the `NOSPACE` alarm that
`applyEntryNormal` then proposes is applied) receives `etcdserver: mvcc: database space exceeded`
for a write that took effect: a later read sees it. The client cannot tell this answer from the
same error returned before proposing (the gRPC quota interceptor, `quotaKVServer`), after which
nothing was written; the capped applier's (after the alarm) also writes nothing. Whether the answer
appears also depends on the member's backend size, which differs between members (each defragments
on its own), so it is not a function of the replicated state.

**Why not an issue:** found by code reading (batch 3a of the specs-only branch, 2026-11-09); no test,
upstream not searched. The behavior looks deliberate (the alarm must be raised by an entry, and the
write is already in the log), but etcd's documentation of `ErrNoSpace` does not say the request may
have been applied. A test could promote it: an integration cluster with a small
`--quota-backend-bytes`, puts until the first `ErrNoSpace`, then a `Get` of that key.

## Proof

no: the specs model it. `SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/apply/Api.lean`'s `resMatch`
lets a member's result carry `ErrNoSpace` in place of a write's successful answer (the model's state
moves by the write either way); the client's model must then treat `ErrNoSpace` as not settling
whether the request took effect (requested of W0: `notes/specs-only/req/go_etcd_io_etcd_api_v3.md`,
"from 3a").
