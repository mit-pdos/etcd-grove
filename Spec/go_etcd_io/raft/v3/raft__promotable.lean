/-
Port of election_proof/spec_raft__promotable.v (feb5c73d4).

Lean notes: `bool_decide (…)` is `decide (…)`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `r.promotable()`: true exactly when this node is a voter **and has no pending
snapshot** (`LogState.snap = none`; the third conjunct, `!hasNextOrInProgressSnapshot()`,
was constantly true until snapshots came into scope on 2026-10-02). It reads `r.id`,
`r.trk.Progress` and `r.raftLog`, so it is stated against the raft struct rather than
against three unrelated parameters.

**Proved** (`Proof/raft__promotable.lean`; Rocq `Qed` 2026-09-19). The generated body
(`raft.promotable.impl` in `Code/go_etcd_io/raft/v3.lean`) is

    pr := r.trk.Progress[r.id]
    return pr != nil && !pr.IsLearner &&
           !r.raftLog.hasNextOrInProgressSnapshot()

There were *two* obstacles to stating it this way, both cleared on 2026-09-16 and
recorded here because the statement depends on them:

- `hasNextOrInProgressSnapshot` needs `ownRaftLog` opened up. Since 2026-09-16
  `ownRaftLog` is a real **definition** (`InvRaftlog.lean`) carrying
  `unstable.snapshot = nil`, and `raftLog.wp_hasNextOrInProgressSnapshot` exists again
  and is proved -- it is a hypothesis of this proof, `raftLog.hasNextOrInProgressSnapshot.spec`.
- `ownProgress` (`InvTracker.lean`) did not record `pv.IsLearner' = false`, and without
  it the postcondition as stated is **not derivable**: a voter whose `Progress` had
  `IsLearner = true` would make `promotable` return `false` while `id ∈ cfg`. That
  conjunct was added on 2026-09-16 and is now `Hnolearner` in `ownProgress`; since 2026-10-02 it is
  part of `ownProgress`'s `progressAbs` (`Defs.lean`).

The statement is correct as written; do not weaken it. The proof is a case split on
`id ∈ cfg`: present, the `r.trk.Progress[r.id]` lookup (see
`wp_tracker_progress_lookup`, `InvTracker.lean`) yields a non-nil, non-learner
`Progress` and the call returns `false`; absent, the lookup yields `nil` and the `&&`
short-circuits. -/
abbrev raft.promotable.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysC c r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"promotable")) (Val #()))
  {{ (b : Bool), RET #b;
      ownRaftPhysC c r id s ∗
      ⌜b = decide (id ∈ c.voters ∧ s.logst.snap = none)⌝ }}

/-- The statement on `ownRaftPhys` (the simple configuration `cfg`) until 2026-10-13,
derived from `raft.promotable.spec` by `raft.promotable.spec_simple`. -/
abbrev raft.promotable.specS : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"promotable")) (Val #()))
  {{ (b : Bool), RET #b;
      ownRaftPhys cfg r id s ∗
      ⌜b = decide (id ∈ cfg ∧ s.logst.snap = none)⌝ }}

open Iris.ProofMode in
theorem raft.promotable.spec_simple
    (H : raft.promotable.spec (GF := GF) (hG := hG)) :
    raft.promotable.specS (GF := GF) (hG := hG) := by
  intro cfg r id s
  iintro %Φ ⟨#Hpkg, Hphys⟩ HΦ
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  iapply H _ r id s $$ [$Hpkg $Hphys]
  inext
  iintro %b ⟨Hphys, %Hb⟩
  ihave Hphys := ownRaftPhysC_toS $$ Hphys
  iapply HΦ
  iframe Hphys
  ipureintro; rw [Hb, CfgM.voters_simple]

end spec

end EtcdGrove
end Perennial
