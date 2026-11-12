# Requirements on `go.etcd.io/raft/v3/confchange` and `tracker` (batch R4)

## from R1

R1's model (`SpecPlan/Spec/go_etcd_io/raft/v3/Model.lean`) declares, opaque, what a configuration change
does: `Membership.applyChange (c : ConfChangeI) (m : Membership) : Option Membership` (`c.AsV2()`
run through confchange's `Changer` -- `EnterJoint`, `LeaveJoint` or `Simple` by the transition and
the number of changes -- and the tracker's `checkInvariants`; `none` exactly where
`raft.applyConfChange` panics) and `Membership.Valid` (what `checkInvariants` accepts). Please make
both transparent in your model (or state them so that R1's are instances), and prove R1's laws
(`Api.lean`):
- `Membership.applyChange_valid.spec`, `Membership.simple_valid.spec`;
- `Membership.applyChange_v1.spec`: the legacy changes at a non-joint configuration, the ones
  etcd's server makes (node 0 and `UpdateNode` change nothing; `AddNode` makes a voter,
  `AddLearnerNode` a learner, `RemoveNode` removes, the last voter's removal fails).

Users: `node.ApplyConfChange.spec` (`Membership.applyChange c v.membership = some m'` is its
no-panic premise), `confDecide.spec`, the examples' own pre-checks (`examples/raft/kvreconf`
runs `confchange.Changer` itself before deciding: it needs your `Changer` specs to agree with
`Membership.applyChange`).

Also: `tracker.Config.Clone` and the `Progress` copies `getStatus` makes are fresh memory
(R1's opaque `statusOwn s` is the ownership of a `Status`'s maps).

## from R2

`raft.applyConfChange.spec` and the `appliedSnap` step (`raft.Step.spec`, `StepSrc.ack`) run
`Changer.LeaveJoint`/`EnterJoint`/`Simple` and `Restore` on the tracker:
- `Changer{Tracker, LastIndex}.X(...)` returns no error exactly when R1's
  `Membership.applyChange (.v2 c2) m` is `some m'`, and then the configuration `m'` with a progress
  map whose new entries start at `LastIndex + 1`;
- `Restore(Changer{..}, cs)` succeeds for a `ConfState` listing a valid `Membership` (R1's
  `confAt_valid`), giving that configuration (`assertConfStatesEquivalent` then passes).
