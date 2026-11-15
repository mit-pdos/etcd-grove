---
upstream: none
checked: 2026-11-09
links:
blocks-proof: no
---

# etcdserver: a member id equal to raft's reserved local ids is not refused

raft reserves two node ids for its own local messages: `LocalAppendThread = math.MaxUint64` and
`LocalApplyThread = math.MaxUint64 - 1` (`raft/raft.go`, the async-storage-writes targets), and `0`
(`None`) means "no node". etcd computes a member's id itself and never checks it against the two
reserved values:

* an initial member's id is the first 8 bytes of SHA-1 of its sorted peer URLs and the cluster
  token (`membership.computeMemberID`, `member.go:63-76`); `NewClusterFromURLsMap`
  (`cluster.go:81-95`) refuses a duplicate and `0`, not `2^64-1` or `2^64-2`;
* an added member's id is the same hash salted with the current time (`NewMember`, `member.go:73`);
  `MemberAdd` → `ValidateConfigurationChange` (`cluster.go:306-391`) checks for an existing or
  removed id, not for `0` or the reserved ones.

A member whose id is a reserved one would have its raft messages taken for raft's local storage
threads' (and an id `0` for "no node"); the outcome is not analyzed further.

**Why not an issue:** no test, found by code reading (verify round, A8 provability F4); the
probability is about 2^-63 per id (a SHA-1 prefix hitting one of three values), and a test cannot
choose the URLs that hash to it.

## Proof

no: the specs take it as a premise: raft's `cluster_alloc`/`freshIds_take` need `id ≠ 0` and
`isLocalTarget id = false`; etcd's `EtcdServer.cluster_alloc` (`ApiBoot.lean`) takes the same of the
initial members' ids (requested of the server's specs by the verify-round repair of the server-boot
group), and the membership add path's freshness rests on the same premise for `NewMember`'s ids.

## Notes

A fix: refuse (or re-draw, for `NewMember`'s time salt) an id in `{0, 2^64-2, 2^64-1}`, as
`NewClusterFromURLsMap` refuses `0`.
