---
upstream: none
checked: 2026-11-09
links:
  - etcd-io/etcd#13848 issue closed: the same raft panic ("removed all voters"), reached otherwise
blocks-proof: yes
---
# etcdserver: two concurrent RemoveMember calls can remove the last voter and panic every member

`mayRemoveMember` checks a removal against the proposing member's current membership
(`IsReadyToRemoveVotingMember`), but the conf change is validated again at apply only against the
membership's records (`ValidateConfigurationChange`), which does not check for the last voter. With
two voters A (leader) and B, two `RemoveMember` calls (of A, then of B) each validated against the
two-voter view can both be proposed: raft refuses a second conf change only while the first is
pending, so the second is accepted once the leader has applied the first. etcd runs raft with
`StepDownOnRemoval` off (`raftConfig`, `bootstrap.go:580`), so the removed leader A keeps leading
`{B}`, commits the removal of B with B's acknowledgement, and every member's `ApplyConfChange`
panics with "removed all voters" (as `nonissues/raft-remove-last-voter-panic.md`).

**Why not an issue:** found by code reading, no test; it needs two concurrent removals racing the
proposers' views, the second proposed after the leader applied the first.

## Proof

yes: 2d's `applyConfChange` decides an accepted change for the cluster with R1's `confDecide`, which
needs the change to apply in raft; this rests on a workload scope restriction (no two
`RemoveMember` calls in flight at once) until a fix (batch 2d, round 1, provability S6).

## Notes

Fixes: check the last voter in `ValidateConfigurationChange` (a refused change becomes a no-op in
raft, `NodeId := None`), or run raft with `StepDownOnRemoval`.
