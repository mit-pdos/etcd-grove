/-
(2026-10-28, stage U0) The vocabulary `raft.Step`'s spec gained when the configuration's switch moved
to `appliedSnap` (the fork's `raft37-goose-lean-a2`): `SnapRoleBack` (a clause of `PreCandStep`),
`SnapAckOk` (the snapshot acknowledgement's premise), and the tactics that prove `PreCandStep` of a
concrete step (`pc1_tac`, `srb_tac`; `pc_tac` is the spec file's). Here, not in the spec file, which
exposes only its triple (`etc/api/raft-layout.txt`).
-/
module

public import Proof.go_etcd_io.raft.v3.StepGhostMode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

/-- (2026-10-28, stage U0) **A node that is no follower with a snapshot pending was one before**:
a step makes a follower a candidate or a pre-candidate only through `hup`, which checks that no
snapshot is pending (`promotable`), and keeps a non-follower's pending snapshot or clears it. What
keeps `SnapFol` (`InvRawnode.lean`: a pending snapshot is a follower's), which `appliedSnap`'s
rebuild of the tracker needs (`raft.Step`'s snapshot acknowledgement). -/
def SnapRoleBack [GooseExts] (s s' : NState) : Prop :=
  s'.role ≠ .follower → s'.logst.snap ≠ none → s.role ≠ .follower ∧ s.logst.snap ≠ none

/-- (2026-10-28, stage U0) What the acknowledgement of a snapshot `sv` needs of it, beyond the
log's facts: its `ConfState` well formed (`SnapScope`: `appliedSnap` rebuilds the tracker from
it) and, statically, the ghost state's voters, not joint, within the tracked bound (`CfgStatic`,
`TrackedOk`: the node is at that configuration afterwards). The `RawNode` has them from the
snapshot's certificate (`raftSnapCert`). (From 2026-10-20, D22 S-c, to stage U0 a `MsgSnap`'s
restore switched the configuration, `SnapCfgOut`.) -/
def SnapAckOk [GooseExts] (γ : RaftNames) (id : w64) (sv : SnapshotM) : Prop :=
  SnapScope sv sv.Metadata'.ConfState'.lists ∧
  CfgStatic γ (snapCfg sv sv.Metadata'.ConfState'.lists) ∧
  TrackedOk γ (snapCfg sv sv.Metadata'.ConfState'.lists) id

/-- (2026-10-28, stage U0) The snapshot/role clause of `PreCandStep` for a concrete end state:
a follower's, or the role and the pending snapshot kept. -/
macro "srb_tac" : tactic => `(tactic| first
  | (intro h1 h2; exact ⟨h1, h2⟩)
  | (intro h1 _; exact absurd rfl h1)
  | (intro h1 h2; simp only at h1 h2 ⊢; exact ⟨h1, h2⟩)
  | (intro h1; exfalso; apply h1; simp_all; done)
  | (intro h1 h2; simp_all))

/-- `PreCandStep` for a concrete end state: the role, term and log kept, or a role that is no
pre-candidate's (2026-10-17); and (stage U0) `srb_tac`. -/
macro "pc1_tac" : tactic => `(tactic| first
  | (intro h; exact ⟨rfl, .inl ⟨h, rfl, rfl, rfl, fun h => h, Int.le_refl _⟩⟩)
  | (intro h; cases h)
  | (intro h; exact absurd h (by decide))
  | (intro h; simp_all)
  | (intro h; exact ⟨rfl, .inl ⟨h, by simp_all [PreKeep]⟩⟩))

end EtcdGrove
end Perennial
