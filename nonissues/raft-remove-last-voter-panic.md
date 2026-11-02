---
upstream: none
checked: 2026-11-01
links:
  - etcd-io/etcd#13848 issue closed: the same raft panic ("removed all voters"), reached through `--force-new-cluster` on a removed member (or a replayed self-removal), not through a proposal; retitled a feature request, closed not planned (stale)
blocks-proof: no
---
# raft: a conf change removing the last voter is committed, then panics every node that applies it

The leader accepts a conf change that removes the only voter; it commits, and `ApplyConfChange`
on it panics with "removed all voters" on every node, again at every restart while the entry is in
the log. Nothing in raft documents such a proposal as invalid, and doc.go says every committed
conf change must be passed to `ApplyConfChange`.

**Why not an issue:** the panic only replaces the loss of the cluster the operator asked for (a
cluster whose last voter is removed cannot make progress either way), and etcd refuses the request
by default: `mayRemoveMember` rejects removing the only voting member unless
`--strict-reconfig-check=false` (server/etcdserver/server.go; `IsReadyToRemoveVotingMember`);
The 2026-10-23 review's Plan: "Skip for now" ("a self-inflicted loss of the cluster").

`TestRawNodeRemoveLastVoter` in
[`nonissues/raft-remove-last-voter-panic/remove_last_voter_test.go`](raft-remove-last-voter-panic/remove_last_voter_test.go)
(public `RawNode` API, each `Ready` applied before `Advance`) fails at etcd-io/raft@c51f010c851e,
go1.27.3: `Error: func (assert.PanicTestFunc)(0x74cac0) should not panic` / `Panic value: removed
all voters`.

## Proof

no: `raft.applyConfChange.spec` and `RawNode.ApplyConfChange.spec` require the change to apply
(`CCApplies`; `ccApplyM` models "removed all voters", `InvConfchange.lean`), which etcd meets in
its default configuration.

## Notes

Fixes, if wanted as hardening: in `stepLeader`, refuse (replace by an empty entry) a conf change
the `Changer` rejects on the leader's configuration; or document it on `ProposeConfChange`; in etcd,
refuse removing the last voting member in `mayRemoveMember` whatever `--strict-reconfig-check`
says. The same class: [`raft-joint-empty-transition-panic`](raft-joint-empty-transition-panic.md).
The test was written 2026-11-01 (the 2026-10-18 reproduction was not kept).
