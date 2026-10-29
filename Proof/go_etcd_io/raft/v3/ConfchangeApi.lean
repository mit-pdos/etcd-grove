/-
# `confchange` and `tracker` for clients (2026-10-29, stage U11; G4)

The importable specs of `tracker.MakeProgressTracker`, `confchange.Restore` and
`confchange.Changer.{Simple,EnterJoint,LeaveJoint}`, for an application that validates a change
the way raft does (kvreconf's `validConf`): `notes/spec-first-study/raft-node-unified-candidate.md`,
§4b. Their internal specs (`Spec/go_etcd_io/raft/v3/{tracker,confchange}/`) are over the tracker's
fields and `confchange`'s model (`InvConfchange.lean`); these are over a `Membership`:

* `Membership.applyGo` (sealed): what Go's `confchange` makes of a membership (the change as
  `AsV2` makes it, by `raft.applyConfChange`'s dispatch), with no bound on the tracked ids;
  `Membership.applyChange_eq_applyGo`: the API's `applyChange` is it, cut at `2^62` ids.
* `Membership.Restorable`: what `Restore` needs beyond `WellFormed` (no id `0`, no staged learner
  that is an incoming voter), which every membership `confchange` reaches has.
* `ownTrackerM trk m` (sealed): a tracker value at the membership `m` (`none`: a fresh one);
  `ownCfgPairM cfg prs m` (sealed): a `(Config, ProgressMap)` pair at `m`, what `Restore` and
  the `Changer` return. Laws: `ownTrackerM_assemble` (a fresh tracker with a pair written into its
  fields, as `trk.Config = cfg; trk.Progress = prs`), `ownCfgPairM_size` (the progress map has
  `m.ids.size` entries: a client's `len(prs)`).
* The specs `*.apiSpec`; their derivations from the internal specs are in
  `ConfchangeApiProof.lean`, their linked results in `Linked.lean`.
-/
module

public import Proof.go_etcd_io.raft.v3.ConfRule
public import Proof.go_etcd_io.raft.v3.InvPb
public import Proof.go_etcd_io.raft.v3.CCApply
import Proof.go_etcd_io.raft.v3.ConfchangeApiImpl
import all Proof.go_etcd_io.raft.v3.InvNode

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **What Go's `confchange` makes of a membership** (sealed): the change as `AsV2` makes it
(`ccV2Of`), applied as `raft.applyConfChange` dispatches it (`LeaveJoint` for an empty `Auto`
change, else `EnterJoint` or `Simple` as `ConfChangeV2.EnterJoint` says) by a `Changer` on a
tracker at `m`; `none` where the `Changer` errs. Unlike `applyChange`, no bound on the tracked ids. -/
@[no_expose] def Membership.applyGo (o : ConfChangeIM) (m : Membership) : Option Membership :=
  ApiImpl.memApplyGo o m

/-- **A membership `Restore` rebuilds**: no id `0` (which `Changer.apply` skips) and no staged
learner that is an incoming voter (which `Restore`'s `AddLearnerNode` would take out of the
incoming voters). Every membership `confchange` reaches has both; `Valid` does not say so. -/
def Membership.Restorable (m : Membership) : Prop :=
  W64 0 ∉ m.ids ∧ ∀ k, k ∈ m.learnersNext → k ∉ m.voters

theorem Membership.restorable_empty : Membership.empty.Restorable :=
  ⟨fun h => by
    simp only [Membership.ids, Membership.empty, GMap.elem_of_union] at h
    rcases h with ((h | h) | h) | h <;> exact GMap.not_elem_of_empty _ h,
   fun _ h => absurd h (GMap.not_elem_of_empty _)⟩

theorem Membership.restorable_simple (vs : GSet w64) (h : W64 0 ∉ vs) :
    (Membership.simple vs).Restorable :=
  ⟨fun h' => by
    simp only [Membership.ids, Membership.simple, GMap.elem_of_union] at h'
    rcases h' with ((h' | h') | h') | h'
    · exact h h'
    all_goals exact GMap.not_elem_of_empty _ h',
   fun _ h' => absurd h' (GMap.not_elem_of_empty _)⟩

/-- **A change keeps a well-formed membership restorable.** -/
theorem Membership.applyGo_restorable {o : ConfChangeIM} {m m' : Membership} :
    m.WellFormed → m.Restorable → Membership.applyGo o m = some m' → m'.Restorable := by
  intro hw hr h
  have hg : CCGood (ApiImpl.stOf m) := by
    rcases hw with rfl | hv
    · exact ApiImpl.ccGood_stOf_empty
    · exact hv.2
  exact ApiImpl.memApplyGo_restorable hg hr h

/-- **The API's `applyChange` is Go's `confchange`, cut at `2^62` tracked ids** (raft's bound:
`Valid`). -/
theorem Membership.applyChange_eq_applyGo (o : ConfChangeIM) (m : Membership) :
    Membership.applyChange o m =
      (Membership.applyGo o m).filter (fun m' => decide (GMap.size m'.ids < 2 ^ 62)) :=
  ApiImpl.memApply_eq_go o m

/-- What the cut means for one answer: `applyChange` answers `applyGo`'s result exactly when it
tracks fewer than `2^62` ids. -/
theorem Membership.applyChange_of_applyGo {o : ConfChangeIM} {m m' : Membership}
    (h : Membership.applyGo o m = some m') :
    Membership.applyChange o m = if GMap.size m'.ids < 2 ^ 62 then some m' else none := by
  rw [Membership.applyChange_eq_applyGo, h, Option.filter_some]
  by_cases hs : GMap.size m'.ids < 2 ^ 62 <;> simp [hs]

theorem Membership.applyChange_of_applyGo_none {o : ConfChangeIM} {m : Membership}
    (h : Membership.applyGo o m = none) : Membership.applyChange o m = none := by
  rw [Membership.applyChange_eq_applyGo, h]; rfl

/-- **A legacy change is its `AsV2`** (`ConfChangeM.asV2`, `(*ConfChange).AsV2`'s model): what
`confchange` makes of it. -/
theorem Membership.applyGo_asV2 (c : ConfChangeM) (m : Membership) :
    Membership.applyGo (.v1 c) m = Membership.applyGo (.v2 c.asV2) m := by
  unfold Membership.applyGo ApiImpl.memApplyGo; rfl

/-- **A legacy change is its `AsV2`** (the API's `applyChange`). -/
theorem Membership.applyChange_asV2 (c : ConfChangeM) (m : Membership) :
    Membership.applyChange (.v1 c) m = Membership.applyChange (.v2 c.asV2) m := by
  rw [Membership.applyChange_eq_applyGo, Membership.applyChange_eq_applyGo,
    Membership.applyGo_asV2]

/-- **A change keeps a well-formed membership restorable** (the API's `applyChange`). -/
theorem Membership.applyChange_restorable {o : ConfChangeIM} {m m' : Membership} :
    m.WellFormed → m.Restorable → Membership.applyChange o m = some m' → m'.Restorable := by
  intro hw hr h
  cases hg : Membership.applyGo o m with
  | none => rw [Membership.applyChange_of_applyGo_none hg] at h; cases h
  | some m1 =>
    rw [Membership.applyChange_of_applyGo hg] at h
    split at h
    · cases h; exact Membership.applyGo_restorable hw hr hg
    · cases h

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A `(Config, ProgressMap)` pair at the membership `m`** (sealed): what `confchange.Restore`
and the `Changer`'s methods return. -/
@[no_expose] def ownCfgPairM (cfg : tracker.Config) (prs : Loc) (m : Membership) : IProp GF :=
  ApiImpl.cfgPairBody cfg prs m

/-- **A tracker value at the membership `m`** (sealed): `none` for a fresh one (as
`MakeProgressTracker` builds it), `some m` for one holding a pair at `m` in its `Config` and
`Progress` fields; its `MaxInflight` within the bound a new `Progress`'s `Inflights` needs. -/
@[no_expose] def ownTrackerM (trk : tracker.ProgressTracker) (mo : Option Membership) :
    IProp GF :=
  iprop(⌜0 ≤ sint.Z trk.MaxInflight' ∧ sint.Z trk.MaxInflight' < 2 ^ 62⌝ ∗
    match mo with
    | none => ∃ v0 : Loc, ⌜trk.Config'.Voters'.arr = [v0, map.nil] ∧
          trk.Config'.Learners' = map.nil ∧ trk.Config'.LearnersNext' = map.nil ∧
          trk.Config'.AutoLeave' = false⌝ ∗
        v0 ↦$ (∅ : GMap w64 Unit) ∗ trk.Progress' ↦$ (∅ : GMap w64 Loc)
    | some m => ownCfgPairM trk.Config' trk.Progress' m)

end defs

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

open Iris.ProofMode in
/-- **Assembling a tracker**: a fresh tracker with a pair at `m` written into its fields
(`trk.Config = cfg; trk.Progress = prs`) is at `m`. -/
theorem ownTrackerM_assemble (trk : tracker.ProgressTracker) (cfg : tracker.Config) (prs : Loc)
    (m : Membership) :
    ownTrackerM (GF := GF) trk none ∗ ownCfgPairM cfg prs m ⊢
      ownTrackerM { trk with Config' := cfg, Progress' := prs } (some m) := by
  unfold ownTrackerM
  iintro ⟨⟨%Hmi, -⟩, Hp⟩
  isplitr
  · ipureintro; exact Hmi
  · iexact Hp

/-- **The size of a pair's progress map** is its membership's number of ids (a client's
`len(prs)`): the map, borrowed. -/
theorem ownCfgPairM_size (cfg : tracker.Config) (prs : Loc) (m : Membership) :
    ownCfgPairM (GF := GF) cfg prs m ⊢ ∃ (M : GMap w64 Loc) (dq : DFrac),
      prs ↦${dq} M ∗ ⌜GMap.size M = GMap.size m.ids⌝ ∗
      (prs ↦${dq} M -∗ ownCfgPairM cfg prs m) :=
  ApiImpl.cfgPairBody_size cfg prs m

end laws

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `tracker.MakeProgressTracker(maxInflight, maxBytes)`: a fresh tracker (`ownTrackerM _ none`),
for a `maxInflight` within the bound a new `Progress`'s `Inflights` needs. -/
abbrev tracker.MakeProgressTracker.apiSpec : Prop :=
  ∀ (maxInflight maxBytes : w64),
  0 ≤ sint.Z maxInflight ∧ sint.Z maxInflight < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker }}
    (App (App (Val #(functions tracker.MakeProgressTracker [])) (Val #maxInflight))
      (Val #maxBytes))
  {{ (tv : tracker.ProgressTracker), RET #tv; ownTrackerM tv none }}

/-- `confchange.Restore(chg, cs)` on a fresh tracker, for a `ConfState` reporting a well-formed
membership `m` that `Restore` rebuilds (`Restorable`): no error, and a pair at `m` (the fresh
tracker's own maps when `m` is empty). The tracker is consumed. -/
abbrev confchange.Restore.apiSpec : Prop :=
  ∀ (chg : confchange.Changer) (cs : Loc) (c : ConfStateM) (dq : DFrac) (m : Membership),
  confStateIs c m → m.WellFormed → m.Restorable →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ ownCSM cs dq c ∗
      ownTrackerM chg.Tracker' none }}
    (App (App (Val #(functions confchange.Restore [])) (Val #chg)) (Val #cs))
  {{ (cfg : tracker.Config) (prs : Loc), RET (PairV (PairV #cfg #prs) #interface.nil);
      ownCSM cs dq c ∗ ownCfgPairM cfg prs m }}

/-- `chg.Simple(ccs...)`, as raft's dispatch calls it for the change `o` (`AsV2`'s transition `t`
and changes `l`; not `LeaveJoint`'s empty `Auto` change; `ConfChangeV2.EnterJoint` says no):
`applyGo`'s answer, a pair at its membership or an error. The tracker is only read. -/
abbrev confchange.Changer.Simple.apiSpec : Prop :=
  ∀ (p : Loc) (chg : confchange.Changer) (m : Membership) (o : ConfChangeIM) (t : w32)
    (l : List ConfChangeSingleM) (al : Bool) (ccs : GoSlice) (ls : List Loc) (dq dqs : DFrac),
  ccV2Of o = (t, l) → ¬ (t = W32 0 ∧ l = []) → enterJointOf t l.length = some (al, false) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dq} chg ∗
      ccs ↦*{dqs} ls ∗ ([∗list] q;c ∈ ls;l, ccsRO q c) ∗ ownTrackerM chg.Tracker' (some m) }}
    (App (Val (p @!! go.GoType.PointerType confchange.Changer.ty @!! go!"Simple")) (Val #ccs))
  {{ (cfg : tracker.Config) (prs : Loc) (err : GoInterface),
      RET (PairV (PairV #cfg #prs) #err);
      p ↦{dq} chg ∗ ccs ↦*{dqs} ls ∗ ownTrackerM chg.Tracker' (some m) ∗
      ((∃ m', ⌜err = interface.nil ∧ Membership.applyGo o m = some m'⌝ ∗ ownCfgPairM cfg prs m') ∨
        ⌜err ≠ interface.nil ∧ Membership.applyGo o m = none⌝) }}

/-- `chg.EnterJoint(autoLeave, ccs...)`, as raft's dispatch calls it for the change `o`
(`ConfChangeV2.EnterJoint` says `(autoLeave, true)`): `applyGo`'s answer. -/
abbrev confchange.Changer.EnterJoint.apiSpec : Prop :=
  ∀ (p : Loc) (chg : confchange.Changer) (m : Membership) (o : ConfChangeIM) (t : w32)
    (l : List ConfChangeSingleM) (autoLeave : Bool) (ccs : GoSlice) (ls : List Loc)
    (dq dqs : DFrac),
  ccV2Of o = (t, l) → enterJointOf t l.length = some (autoLeave, true) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dq} chg ∗
      ccs ↦*{dqs} ls ∗ ([∗list] q;c ∈ ls;l, ccsRO q c) ∗ ownTrackerM chg.Tracker' (some m) }}
    (App (App (Val (p @!! go.GoType.PointerType confchange.Changer.ty @!! go!"EnterJoint"))
      (Val #autoLeave)) (Val #ccs))
  {{ (cfg : tracker.Config) (prs : Loc) (err : GoInterface),
      RET (PairV (PairV #cfg #prs) #err);
      p ↦{dq} chg ∗ ccs ↦*{dqs} ls ∗ ownTrackerM chg.Tracker' (some m) ∗
      ((∃ m', ⌜err = interface.nil ∧ Membership.applyGo o m = some m'⌝ ∗ ownCfgPairM cfg prs m') ∨
        ⌜err ≠ interface.nil ∧ Membership.applyGo o m = none⌝) }}

/-- `chg.LeaveJoint()`, as raft's dispatch calls it for the change `o` (an empty `Auto` change):
`applyGo`'s answer. -/
abbrev confchange.Changer.LeaveJoint.apiSpec : Prop :=
  ∀ (p : Loc) (chg : confchange.Changer) (m : Membership) (o : ConfChangeIM) (dq : DFrac),
  ccV2Of o = (W32 0, []) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dq} chg ∗
      ownTrackerM chg.Tracker' (some m) }}
    (App (Val (p @!! go.GoType.PointerType confchange.Changer.ty @!! go!"LeaveJoint")) (Val #()))
  {{ (cfg : tracker.Config) (prs : Loc) (err : GoInterface),
      RET (PairV (PairV #cfg #prs) #err);
      p ↦{dq} chg ∗ ownTrackerM chg.Tracker' (some m) ∗
      ((∃ m', ⌜err = interface.nil ∧ Membership.applyGo o m = some m'⌝ ∗ ownCfgPairM cfg prs m') ∨
        ⌜err ≠ interface.nil ∧ Membership.applyGo o m = none⌝) }}

end specs

end EtcdGrove
end Perennial
