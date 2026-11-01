---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/etcd#20729 pr merged: related, not this bug (ours: the 2^48 event window comment in idutil; no cross-member collision)
blocks-proof: yes
---

# etcdserver: request ids of two members collide when their member ids agree in the low 16 bits

Every member's apply loop delivers each committed entry's result to whatever request of its own
waits under the entry's id, and request ids are unique across members only through a 16-bit
prefix: `NewServer` builds its generator from the member id truncated to 16 bits. Two members
whose ids agree in the low 16 bits (about 1 in 20000 for three random member ids) share a prefix,
and an earlier-started one reaches the later one's ids after 256 requests per millisecond of start
difference; then one member's `Put` can return another member's result (or panic in the response
type assertion if the request kinds differ).

**Why not an issue:** no test through etcd: the test shows only that two generators built as
`NewServer` builds them issue the same id; a wrong result needs, in addition, the colliding
request committed while the other member's request with that id is pending.

## Proof

yes: the apply side of the raft contract needs every committed entry's id claimed in one
cluster-wide map, i.e. the members' prefixes distinct (`batchCommitted`,
`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvRequest.lean`; `pkg/v3/idutil/Defs.lean`), which
etcd does not ensure.

## Notes

Test: `TestCrossMemberCollision` in
[`etcd-request-id-member-prefix/cross_member_collision_test.go`](etcd-request-id-member-prefix/cross_member_collision_test.go)
(package `idutil`) fails at etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-11-01):
`member A's request 257 has the id beef8bcfe5680101 of member B's first request`. An integration
test could promote it: member ids come from a hash of the peer URLs, the cluster token and (when
joining) the time, so a cluster token can be searched for two members agreeing in 16 bits, then
two clients writing through both. Possible fixes: reject member ids colliding in the low 16 bits
at member add, or check that a triggered result is for the waiter's own request.
