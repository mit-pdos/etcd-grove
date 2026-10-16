---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#16687 issue closed: this finding (closed by the stale bot; no fix)
  - etcd-io/etcd#14174 issue closed: a joining member failing to bootstrap from a member list that lacks it (the workaround is to retry)
  - etcd-io/etcd#14175 pr closed: "serve peer linearizable member list", not merged
  - etcd-io/etcd#16666 issue closed: the report #16687 was split out of
  - etcd-io/etcd#17100 pr closed: draft e2e test, related, not merged
  - etcd-io/etcd#17119 pr closed: draft, related, not merged
---

# etcdhttp: the peer `/members` handler serves the local, possibly stale, member list

- **Status**: possible bug, not shown to cause harm. The handler answers without a linearizable
  read barrier, so a member that is behind (lagging, or replaying its WAL after a restart) serves an
  old membership. The maintainers doubted it does harm, since the joining member then replays raft,
  and nobody showed a failure caused by it; recorded as the triage classified it (not shown to be a
  bug).
- **Where** (etcd pin `107edf7e4`): `server/etcdserver/api/etcdhttp/peer.go:108-123`
  (`peerMembersHandler.ServeHTTP`: `ms := h.cluster.Members()` at `:118`, encoded as the response
  with the local cluster ID). The consumer is a joining member's bootstrap:
  `bootstrapExistingClusterNoWAL` (`server/etcdserver/bootstrap.go:343`) →
  `GetClusterFromRemotePeers` (`bootstrap.go:351`; `server/etcdserver/cluster_util.go:64`, the first
  peer that answers wins) → `membership.ValidateClusterAndAssignIDs` (`bootstrap.go:355`;
  `server/etcdserver/api/membership/cluster.go:755`), which takes the cluster ID and the members'
  IDs from that list.
- **What happens**: a member returns `h.cluster.Members()` as of what it has applied. If the
  joining member asks a peer that has not yet applied the `MemberAdd` that added it, the list lacks
  it, and `ValidateClusterAndAssignIDs` fails (`member count is unequal`, `cluster.go:759`, or no
  URL match, `:774`): the new member exits at startup, and a retry against an up-to-date peer
  succeeds (#14174). The reporter reproduced the stale answer on a v3.4.20 branch with an
  integration test. No wrong result beyond a failed start has been shown. Reproduction here: none
  (it needs a cluster with a lagging or restarting member and a concurrent join).
- **Expected**: either the handler waits for a linearizable read barrier
  (`LinearizableReadNotify`) before answering, so the list includes every membership change
  committed before the request, or the endpoint is documented as a possibly stale view and the
  joiner retries.
- **How the proof handles it**: outside the verified code. `server/etcdserver/api/etcdhttp` is not
  translated, nor is `cluster_util.go` or `bootstrapExistingClusterNoWAL`. The one verified function
  on the path, `membership.RaftCluster.Members`
  (`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/RaftCluster__Members.lean:34`),
  promises fresh clones of the cluster object's members (`membersAt sl ms`) and says nothing about
  how current that object is relative to the committed membership, so no spec states or excludes the
  behavior (`notes/bug-triage/etcd-16687.md`, proposal `membership-read-barrier`).
- **Possible fixes**: guard the handler with `LinearizableReadNotify` (the shape of #14175), or
  have the joiner retry other peers when its own member is missing from the list.
- **Found**: 2026-10-16, bug triage of etcd-io/etcd#16687 (`notes/bug-triage/etcd-16687.md`).
