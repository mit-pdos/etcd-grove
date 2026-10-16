---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#16002 issue closed: this bug (reported via DNS manipulation giving a new member a wrong ID; closed by the stale bot, not planned)
---

# membership: a committed `ClusterMemberAttrSet` for an unknown member ID panics every member

- **Status**: a bug (a reachable panic of every member, repeated on every restart, from a single
  committed entry). An undocumented precondition of `RaftCluster.UpdateAttributes`.
- **Where** (etcd pin `107edf7e4`):
  `server/etcdserver/api/membership/cluster.go:467-493` (`UpdateAttributes`: `lg.Panic("failed to
  update; member unknown")` at line 482 when `id` is neither in `c.members` nor in `c.removed`);
  called by `server/etcdserver/apply/backend.go:287` (`applierV3backend.ClusterMemberAttrSet`)
  for every applied `ClusterMemberAttrSet` request. The request is proposed by
  `server/etcdserver/server.go:1793` (`publishV3`, `Member_ID = s.MemberID()`) with no check of
  the ID, and none happens before commit. How a member can run under an ID the cluster does not
  know: `bootstrapExistingClusterNoWAL` (`bootstrap.go:343`) →
  `membership.ValidateClusterAndAssignIDs` (`cluster.go:755`), which matches local and existing
  members by DNS-resolved peer URLs (`netutil.URLStringsEqual`). An ambiguous match leaves the
  local member with an ID the cluster never added (the reporter's DNS case).
- **What happens**: the entry commits and every member panics in its apply goroutine. On restart
  it is replayed and panics again. Reproduction of the panic at the pin:
  `issues/etcd-membership-attrset-unknown-member-panic/update_attributes_unknown_member_test.go`
  (dropped into `server/etcdserver/api/membership/`; `go test ./etcdserver/api/membership/ -run
  TestUpdateAttributesUnknownMemberPanics -v` from `server/`)
  (passes at the pin: `PANIC failed to update; member unknown`). The end-to-end trigger (wrong
  DNS at a new member's start) is the reporter's and was not reproduced here.
- **Expected**: a member that applies a request for an unknown member does not crash the
  cluster. Either the request is rejected before it is proposed, or applying it is a no-op with a
  warning, as `RemoveMember` does for an absent member.
- **How the proof handles it**: it does not. The apply package's contract for the names-only
  `*membership.RaftCluster` (`isCluster`,
  `Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/Contracts.lean:339-343`) states that
  `UpdateAttributes` returns for every ID. That is false at the pin (a trust-base error,
  `notes/bug-triage/etcd-16002.md`). The server's apply results rest on it as a premise
  (`etcdserver/Results.lean`, "the components' contracts"). `rqOk` (`apply/Chain.lean:244`) has
  no case for `ClusterMemberAttrSet`, unlike `ClusterVersionSet` (`semverValid`).
- **Possible fixes**: in `UpdateAttributes`, warn and return on an unknown ID instead of panicking.
  Or validate `Member_ID` against the membership before proposing (`publishV3` and the leader's
  `processInternalRaftRequestOnce`). Or make `ValidateClusterAndAssignIDs` refuse ambiguous URL
  matches (two local members matching one existing member).
- **Found**: 2026-10-16, bug triage of etcd-io/etcd#16002 against the apply package's contracts.
