---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/etcd#20729 pr merged: related, not this bug (the 2^48 event window comment in idutil)
blocks-proof: no
---

# etcdserver: a member can issue the request id 0, which raft's bootstrap conf changes carry

A member whose id has 0 low 16 bits, started in the last millisecond of a `2^40` ms period (next:
2039-09-07), issues the request id 0 as its 256th request, the id of raft's bootstrap conf changes;
if such a request is waiting when a bootstrap conf change is applied, the conf change's response
is delivered to it and the request panics in its response type assertion.

**Why not an issue:** negligible probability (a member id with 16 zero bits, started in one
particular millisecond, with a request registered before the member is ready, which embed's client
listeners never do); the test shows only the generator's id 0.

## Proof

no: the top-level adequacy proof needs no fix on the goosed fork for it; the apply side asks that no KV request be registered under a committed conf change's id
(`entryWaitOk`, `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvRequest.lean`), so `NewServer.spec`
takes the premise that the member id's low 16 bits are not 0 (`pkg/v3/idutil/Defs.lean`,
`idNoZero`), which etcd does not ensure.

## Notes

Test: `TestIDZero` in
[`etcd-request-id-zero-bootstrap-confchange/id_zero_test.go`](etcd-request-id-zero-bootstrap-confchange/id_zero_test.go)
(package `idutil`) fails at etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-11-01):
`request 256 has the id 0`. Possible fixes: skip 0 in `Generator.Next`, or trigger the wait
registry only for ids the member registered.
