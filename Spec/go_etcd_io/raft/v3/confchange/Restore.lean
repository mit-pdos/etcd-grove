/-
Port of `election_proof/spec_confchange_Restore.v` (feb5c73d4).

Lean notes:
* Rocq's `(#cfgv, #prsm, #interface.nil)` is the left-nested
  `PairV (PairV #cfgv #prsm) #interface.nil`.
* Rocq's `let tv := chg.(Tracker')` is inlined: `tv` is written `chg.Tracker'`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRestore
public import Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `confchange.Restore chg cs` for **any** `ConfState` (2026-10-14, reconfiguration stage B8):
joint (`VotersOutgoing` non-empty, `LearnersNext`, `AutoLeave`) or not. The answer is the model's,
`restoreM` (`InvRestore.lean`): one `Simple` per change when not joint; when joint, one
`Simple(AddNode)` per outgoing voter, then one `EnterJoint(cs.AutoLeave, in...)` -- the same
`simpleM`/`enterJointM` that `ccApplyM` (`raft.applyConfChange`'s model) is made of. On a
well-formed `ConfState` the answer is the configuration it denotes (`restoreM_wf`:
`cfgStateC (csCfgM ...)`).

Premises: the model answers (`restoreM ... = some s'`: no `Changer` error, which raft's callers
`panic` on); the empty tracker `MakeProgressTracker` builds (an empty voter map `v0`, the
progress map read-only and empty, no learner, not joint). (Until 2026-10-16,
stage R8b, also at least one voter: with none and no outgoing voter there is no op, and `chain`
returns the tracker's own maps, which the premise owns -- the result's first arm now, what a new
cluster's `newRaft` meets before `RawNode.Bootstrap` installs the peers, `specE`; with outgoing
voters but no voter `EnterJoint` errs anyway.)

Result: the configuration as `ownCfgCC` at `s'.cfg` (the incoming voter map owned, the other
three sets canonical, `AutoLeave`), the progress map with domain `s'.prs`'s, each `Progress`
owned with `IsLearner` as `s'.prs` says.

(2026-10-15, raft v3.7 retarget, stage R2: `cs` a `*pb.ConfState` owned at `dq` (`ownCSM`,
given back), its lists `c.Voters'`, `c.Learners'`, `c.VotersOutgoing'`, `c.LearnersNext'` and
`c.AutoLeave'` (read by `cs.GetAutoLeave()` in the `EnterJoint` closure), instead of a
`ConfState` value with the four lists at four fractions, three of them `ownIdList`.) -/
abbrev confchange.Restore.spec : Prop :=
  ∀ (chg : confchange.Changer) (cs : Loc) (c : ConfStateM) (dq : DFrac) (v0 : Loc)
    (s' : CCState),
  restoreM c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext' c.AutoLeave' = some s' →
  (0 ≤ sint.Z chg.Tracker'.MaxInflight' ∧ sint.Z chg.Tracker'.MaxInflight' < 2 ^ 62) →
  -- the empty configuration
  chg.Tracker'.Config'.Voters'.arr = [v0, map.nil] →
  chg.Tracker'.Config'.Learners' = map.nil →
  chg.Tracker'.Config'.LearnersNext' = map.nil →
  chg.Tracker'.Config'.AutoLeave' = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗
      ownCSM cs dq c ∗
      v0 ↦$ (∅ : GMap w64 Unit) ∗
      chg.Tracker'.Progress' ↦$□ (∅ : GMap w64 Loc) }}
    (App (App (Val #(functions confchange.Restore [])) (Val #chg)) (Val #cs))
  {{ (cfgv : tracker.Config) (prsm : Loc) (prs : GMap w64 Loc),
      RET (PairV (PairV #cfgv #prsm) #interface.nil);
      ownCSM cs dq c ∗
      v0 ↦$ (∅ : GMap w64 Unit) ∗
      chg.Tracker'.Progress' ↦$□ (∅ : GMap w64 Loc) ∗
      -- (2026-10-16, stage R8b) no op (a new cluster's empty conf state): the tracker's own maps
      -- come back, the premise's; else the fresh ones `chain` built
      ((⌜restoreSimpleOps c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext' = [] ∧
          cfgv = chg.Tracker'.Config' ∧ prsm = chg.Tracker'.Progress' ∧ prs = ∅⌝) ∨
       (⌜restoreSimpleOps c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext' ≠ []⌝ ∗
        ownCfgCC cfgv (DFrac.own 1) s'.cfg ∗
        prsm ↦$ prs ∗ ⌜domSet prs = domSet s'.prs⌝ ∗
        ([∗map] k ↦ pr ∈ prs, ∃ p, ownProgress pr p ∗ ⌜s'.prs !! k = some p.learner⌝))) }}

/-- `Restore` runs an op exactly when the conf state has a voter or an outgoing voter (2026-10-16,
stage R8b): with a voter, `restoreInCC` (not joint) holds its `AddNode`, `restoreOutCC` (joint)
the outgoing voters'. -/
theorem restoreSimpleOps_ne_nil_of_voters (vo v l ln : List w64) (hv : v ≠ []) :
    restoreSimpleOps vo v l ln ≠ [] := by
  unfold restoreSimpleOps
  split
  · intro h
    unfold restoreInCC at h
    simp only [List.append_eq_nil_iff, List.map_eq_nil_iff] at h
    exact hv h.1.1.2
  · intro h
    unfold restoreOutCC at h
    simp only [List.map_eq_nil_iff] at h
    exact ‹¬ vo = []› h

/-- No voter, no outgoing voter, no learner: no op. -/
theorem restoreSimpleOps_nil (vo v l ln : List w64) (hvo : vo = []) (hv : v = []) (hl : l = [])
    (hln : ln = []) : restoreSimpleOps vo v l ln = [] := by
  subst hvo hv hl hln; rfl

/-- `confchange.Restore chg cs` on an **empty** conf state (2026-10-16, stage R8b, D12: a new
cluster's, which `newRaft` reads before `RawNode.Bootstrap` installs the peers): no op runs, and
`chain` returns the tracker's own configuration and progress map -- the premise's resources,
unchanged. Derived from `spec`'s no-op arm. -/
abbrev confchange.Restore.specE : Prop :=
  ∀ (chg : confchange.Changer) (cs : Loc) (c : ConfStateM) (dq : DFrac) (v0 : Loc),
  c.Voters' = [] →
  c.VotersOutgoing' = [] →
  c.Learners' = [] →
  c.LearnersNext' = [] →
  (0 ≤ sint.Z chg.Tracker'.MaxInflight' ∧ sint.Z chg.Tracker'.MaxInflight' < 2 ^ 62) →
  -- the empty configuration
  chg.Tracker'.Config'.Voters'.arr = [v0, map.nil] →
  chg.Tracker'.Config'.Learners' = map.nil →
  chg.Tracker'.Config'.LearnersNext' = map.nil →
  chg.Tracker'.Config'.AutoLeave' = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗
      ownCSM cs dq c ∗
      v0 ↦$ (∅ : GMap w64 Unit) ∗
      chg.Tracker'.Progress' ↦$□ (∅ : GMap w64 Loc) }}
    (App (App (Val #(functions confchange.Restore [])) (Val #chg)) (Val #cs))
  {{ (cfgv : tracker.Config) (prsm : Loc),
      RET (PairV (PairV #cfgv #prsm) #interface.nil);
      ⌜cfgv = chg.Tracker'.Config' ∧ prsm = chg.Tracker'.Progress'⌝ ∗
      ownCSM cs dq c ∗
      v0 ↦$ (∅ : GMap w64 Unit) ∗
      chg.Tracker'.Progress' ↦$□ (∅ : GMap w64 Loc) }}

/-- The empty conf state's statement from the general one: no op, so `spec`'s first arm. -/
theorem confchange.Restore.spec_empty (H : confchange.Restore.spec (GF := GF) (hG := hG)) :
    confchange.Restore.specE (GF := GF) (hG := hG) := by
  intro chg cs c dq v0 Hv Hvo Hl Hln Hmi Harr Hlm Hlnm Hal
  iintro %Φ ⟨#Hpkg, Hcs, Hv0, #Hpm⟩ HΦ
  have Hm : restoreM c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext' c.AutoLeave' =
      some (cfgState ∅ ∅) := by
    rw [Hvo, Hv, Hl, Hln]; rfl
  iapply H chg cs c dq v0 _ Hm Hmi Harr Hlm Hlnm Hal $$ [$Hpkg $Hcs $Hv0 $Hpm]
  inext
  iintro %cfgv %prsm %prs ⟨Hcs, Hv0, -, (⟨-, %Hc1, %Hc2, -⟩ | ⟨%Hops, -⟩)⟩
  · iapply HΦ
    iframe Hcs Hv0 Hpm
    ipureintro; exact ⟨Hc1, Hc2⟩
  · exfalso; exact Hops (restoreSimpleOps_nil _ _ _ _ Hvo Hv Hl Hln)

end spec

end EtcdGrove
end Perennial
