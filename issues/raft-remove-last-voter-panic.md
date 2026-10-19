---
upstream: unchecked
checked:
links:
  - etcd-io/etcd#13848 issue closed: the same raft panic ("removed all voters"), reached through `--force-new-cluster` on a removed member, not through a proposal
---

# raft: a conf change removing the last voter is committed, then panics every node that applies it

- **Status**: undocumented precondition in raft (an application must not propose a conf change that leaves no
  voter; nothing in raft says so, and the leader accepts one); in etcd, reachable by code reading with
  `--strict-reconfig-check=false` (not the default) on a single-member cluster.
- **Where** (etcd-io/raft `main` 638f42739; the same in v3.7.0):
  - `raft.go:1326-1337` (`stepLeader`, `MsgProp`): a conf change is refused only when another one is pending or
    its shape does not fit the joint state; whether the `Changer` will accept it is not checked.
  - `confchange/confchange.go:170-172` (`Changer.apply`): "removed all voters" when the incoming config ends up
    empty; `raft.go:1965-1967` (`applyConfChange`) panics with it.
  - `doc.go:93-98`: every committed conf change must be passed to `ApplyConfChange` ("one way or the other"); the
    only way out is to cancel it by zeroing its `NodeId`. `ProposeConfChange` (`node.go:141-153`) and
    `ConfChangeV2`'s doc (`raftpb/raft.proto`) do not say which conf changes are invalid.
  - etcd (`main` 22cc5d9ac): `EtcdServer.mayRemoveMember` (`server/etcdserver/server.go:1602`) returns at once when
    `StrictReconfigCheck` is off; with it on, `IsReadyToRemoveVotingMember` (`api/membership/cluster.go:659-684`)
    refuses removing the only voting member (0 started of quorum 1). `ValidateConfigurationChange` at apply time
    accepts the removal of an existing member, so `applyConfChange` (`server.go:2023`) passes it to raft's
    `ApplyConfChange`.
- **What happens**: a single-voter `RawNode` leader is proposed `ConfChange{Type: RemoveNode, NodeId: 1}`;
  `ProposeConfChange` returns nil, the entry commits, and `ApplyConfChange` on it panics with `removed all voters`
  (temporary test, 2026-10-18, at 638f42739, applying committed conf changes before `Advance`:
  `Panic value: removed all voters`). Every node applies the entry, so every node panics, and again after a restart.
  In etcd (not reproduced): `etcdctl member remove <id>` on a single-member cluster started with
  `--strict-reconfig-check=false` should crash the member at apply, and at every restart while the entry is in the
  WAL.
- **Expected**: either the leader refuses the proposal (replacing it with an empty entry, as for the conf changes
  it refuses now), or raft documents that removing the last voter is the application's to avoid; etcd, that
  removing the last member is refused whatever `--strict-reconfig-check` says.
- **How the proof handles it**: `raft.applyConfChange.spec` and `RawNode.ApplyConfChange.spec` require
  `ccApplyM ... = some _` (`CCApplies`); `ccApplyM` models `Changer.apply`'s "removed all voters" error
  (`InvConfchange.lean:153`), so no node of the proof applies this entry.
- **Possible fixes**: in `stepLeader`, refuse a conf change that the `Changer` rejects on the leader's
  configuration; or document the precondition on `ProposeConfChange`; in etcd, refuse removing the last voting
  member in `mayRemoveMember` regardless of `StrictReconfigCheck`.
- **Found**: 2026-10-18, review of the `raft-joint-empty-transition-panic` candidate (the finding's "same class"
  item); raft part reproduced by a temporary Go test, etcd part by code reading.
