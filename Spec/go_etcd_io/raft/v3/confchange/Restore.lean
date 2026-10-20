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
`panic` on); the empty tracker `MakeProgressTracker` builds, as in `specS`. (Until 2026-10-16,
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
  restoreM c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext' c.AutoLeave' c.Witness' = some s' →
  (0 ≤ sint.Z chg.Tracker'.MaxInflight' ∧ sint.Z chg.Tracker'.MaxInflight' < 2 ^ 62) →
  -- raft#168 (`notes/pr-verify/raft-168.md`): no voter `0` (`toConfChangeSingle`), and no
  -- witness in the empty configuration either
  W64 0 ∉ c.VotersOutgoing' → W64 0 ∉ c.Voters' →
  -- (2026-10-20) a joint conf state has no witness (`EnterJoint`'s premise)
  (c.VotersOutgoing' ≠ [] → c.Witness' = W64 0) →
  chg.Tracker'.Config'.Witnesses'.arr = [W64 0, W64 0] →
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
      ((⌜restoreSimpleOps c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext' c.Witness' = [] ∧
          cfgv = chg.Tracker'.Config' ∧ prsm = chg.Tracker'.Progress' ∧ prs = ∅⌝) ∨
       (⌜restoreSimpleOps c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext' c.Witness' ≠ []⌝ ∗
        ownCfgCC cfgv (DFrac.own 1) s'.cfg ∗
        prsm ↦$ prs ∗ ⌜domSet prs = domSet s'.prs⌝ ∗
        ([∗map] k ↦ pr ∈ prs, ∃ p, ownProgress pr p ∗
          ⌜s'.prs !! k = some p.learner ∧
            p.witness = decide (k = s'.cfg.wit ∧ s'.cfg.wit ≠ W64 0)⌝))) }}

/-- `Restore` runs an op exactly when the conf state has a voter or an outgoing voter (2026-10-16,
stage R8b): with a voter, `restoreInCC` (not joint) holds its `AddNode`, `restoreOutCC` (joint)
the outgoing voters'. -/
theorem restoreSimpleOps_ne_nil_of_voters (vo v l ln : List w64) (hv : v ≠ []) (w : w64 := W64 0) :
    restoreSimpleOps vo v l ln w ≠ [] := by
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
    (hln : ln = []) (w : w64 := W64 0) : restoreSimpleOps vo v l ln w = [] := by
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
  -- raft#168: no witness
  chg.Tracker'.Config'.Witnesses'.arr = [W64 0, W64 0] →
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
  intro chg cs c dq v0 Hv Hvo Hl Hln Hmi Hwit Harr Hlm Hlnm Hal
  iintro %Φ ⟨#Hpkg, Hcs, Hv0, #Hpm⟩ HΦ
  have Hm : restoreM c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext' c.AutoLeave' c.Witness' =
      some (cfgState ∅ ∅) := by
    rw [Hvo, Hv, Hl, Hln]; rfl
  iapply H chg cs c dq v0 _ Hm Hmi (by rw [Hvo]; simp) (by rw [Hv]; simp) (fun h => absurd Hvo h) Hwit Harr Hlm Hlnm Hal
    $$ [$Hpkg $Hcs $Hv0 $Hpm]
  inext
  iintro %cfgv %prsm %prs ⟨Hcs, Hv0, -, (⟨-, %Hc1, %Hc2, -⟩ | ⟨%Hops, -⟩)⟩
  · iapply HΦ
    iframe Hcs Hv0 Hpm
    ipureintro; exact ⟨Hc1, Hc2⟩
  · exfalso; exact Hops (restoreSimpleOps_nil _ _ _ _ Hvo Hv Hl Hln _)

/-- `confchange.Restore chg cs` replays a `ConfState` onto the empty configuration
`chg.Tracker` and returns the resulting `Config` and `ProgressMap`.

The statement of 2026-10-13, kept for raft's callers (`newRaft`, `raft.restore`) and derived
from the general `spec` (`spec_simple`; until 2026-10-14 this was `spec` and the general one
`specG`). (Until 2026-10-08 the package was not translated
and this triple was an axiom.) It is stated for a non-joint `ConfState` (voters and, since
2026-10-13, learners) applied to the empty tracker `MakeProgressTracker` builds; the
learners come after the voters (`toConfChangeSingle`), one `AddLearnerNode` each. Read
against the Go (`confchange/restore.go`, `confchange/confchange.go`) it says:

- `toConfChangeSingle` turns `cs` into no outgoing changes and one `AddNode id` per
  `id ∈ cs.Voters`, since `VotersOutgoing`, `Learners` and `LearnersNext` are empty;
- `chain` runs one `Changer.Simple(AddNode id)` per voter. Each `Simple` starts with
  `checkAndCopy`, which `Clone`s the config (a fresh `Voters[0]` map; `Voters[1]`,
  `Learners`, `LearnersNext` stay `nil`; `AutoLeave` is not copied, so `false`) and
  copies the progress map into a fresh one, each `Progress` shallow-copied into a fresh
  allocation. `makeVoter` on a new id calls `initProgress`, which adds `id` to
  `Voters[0]` and allocates a `Progress` with `State = StateProbe`, `IsLearner = false`
  and a fresh `NewInflights(MaxInflight, MaxInflightBytes)`; on a repeated id it only
  re-marks it a voter. `apply` **skips `NodeID = 0`**, hence the premise
  `0 ∉ voters`. No error is reachable: the config is never joint, one voter changes per
  step (`symdiff ≤ 1`), and `checkInvariants` holds throughout;
- so the result is a fresh voter map and a fresh progress map, both with domain
  `set voters`, each `Progress` owned exactly once (the intermediate copies are
  garbage, and so are the tracker's original maps, which are only read).

**`voters ≠ []` is load-bearing for soundness, not just for the caller.** With no
voters there are no ops, and `chain` returns `chg.Tracker.Config` and
`chg.Tracker.Progress` *themselves* -- the maps the premise already owns. A
postcondition handing out fresh points-tos for them would then duplicate ownership,
i.e. prove `False`.

`NoDup voters` is *not* needed here (`Restore` de-duplicates); it is needed by
`assertConfStatesEquivalent`, whose `Equivalent` check fails on a `ConfState` with a
repeated voter.

`MaxInflight`'s bound is what `ownProgress` (via `InflightsOk`) asks of the fresh
`Inflights`; see `spec_tracker_NewInflights.v`.

(2026-10-15, raft v3.7 retarget, stage R2: `cs` a `*pb.ConfState` owned at `dq` (`ownCSM`,
given back) holding `c`, whose `c.Voters'`, `c.Learners'` are the old `voters`, `learners`;
`c.VotersOutgoing' = []` and `c.LearnersNext' = []` replace `.len = W64 0` of the old slices.) -/
abbrev confchange.Restore.specS : Prop :=
  ∀ (chg : confchange.Changer) (cs : Loc) (c : ConfStateM) (dq : DFrac) (v0 : Loc),
  c.Voters' ≠ [] →
  W64 0 ∉ c.Voters' →
  -- (2026-10-13, stage L) the learners: none of them a voter, nor `0`
  W64 0 ∉ c.Learners' →
  (∀ k ∈ c.Learners', k ∉ c.Voters') →
  c.VotersOutgoing' = [] →
  c.LearnersNext' = [] →
  -- (2026-10-20) a conf state without a witness
  c.Witness' = W64 0 →
  (0 ≤ sint.Z chg.Tracker'.MaxInflight' ∧ sint.Z chg.Tracker'.MaxInflight' < 2 ^ 62) →
  -- raft#168: no witness
  chg.Tracker'.Config'.Witnesses'.arr = [W64 0, W64 0] →
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
  {{ (cfgv : tracker.Config) (prsm : Loc) (prs : GMap w64 Loc)
      (vref : Loc) (vm : GMap w64 Unit),
      RET (PairV (PairV #cfgv #prsm) #interface.nil);
      ownCSM cs dq c ∗
      v0 ↦$ (∅ : GMap w64 Unit) ∗
      chg.Tracker'.Progress' ↦$□ (∅ : GMap w64 Loc) ∗
      ⌜cfgv.Voters'.arr = [vref, map.nil] ∧
        cfgv.LearnersNext' = map.nil ∧
        cfgv.AutoLeave' = false ∧ cfgv.Witnesses'.arr = [W64 0, W64 0]⌝ ∗
      ownIdsetC cfgv.Learners' (DFrac.own 1) (GMap.listToSet c.Learners') ∗
      vref ↦$ vm ∗ ⌜domSet vm = GMap.listToSet c.Voters'⌝ ∗
      prsm ↦$ prs ∗ ⌜domSet prs = GMap.listToSet c.Voters' ∪ GMap.listToSet c.Learners'⌝ ∗
      ([∗map] k ↦ pr ∈ prs, ∃ p, ownProgress pr p ∗
        ⌜p.learner = decide (k ∉ GMap.listToSet c.Voters') ∧ p.witness = false⌝) }}

/-- The non-joint statement from the general one: with no outgoing voter and no staged learner
the model's answer is the voters and the learners (`simpleFold_restoreIn`). -/
theorem confchange.Restore.spec_simple (H : confchange.Restore.spec (GF := GF) (hG := hG)) :
    confchange.Restore.specS (GF := GF) (hG := hG) := by
  intro chg cs c dq v0 Hvne Hv0n Hl0n Hdis Hcvo Hcln Hcw Hmi Hwit Harr Hl Hln Hal
  iintro %Φ ⟨#Hpkg, Hcs, Hv0, #Hpm⟩ HΦ
  have Hm : restoreM c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext' c.AutoLeave' c.Witness' =
      some (cfgState (GMap.listToSet c.Voters') (GMap.listToSet c.Learners')) := by
    rw [Hcvo, Hcln, Hcw]
    unfold restoreM restoreSimpleOps
    simp only [↓reduceIte]
    exact simpleFold_restoreIn c.Voters' c.Learners' Hvne
      (fun x hx => hx.elim (fun h e => Hv0n (e ▸ h)) (fun h e => Hl0n (e ▸ h)))
      (fun x hx => Hdis x hx)
  iapply H chg cs c dq v0 _ Hm Hmi (by rw [Hcvo]; simp) Hv0n (fun h => absurd Hcvo h) Hwit Harr Hl Hln Hal
    $$ [$Hpkg $Hcs $Hv0 $Hpm]
  inext
  iintro %cfgv %prsm %prs ⟨Hcs, Hv0, -, (⟨%Hops, -⟩ | ⟨-, Hc, Hprsm, %Hdom, Hprogs⟩)⟩
  · exfalso; exact restoreSimpleOps_ne_nil_of_voters _ _ _ _ Hvne _ Hops
  icases ownCfgCC_elim _ _ _ $$ Hc with ⟨%vin, %vout, %Harr1, Hin, Hout, Hl1, Hln1, %Hal1, %Hwit1⟩
  icases ownIdsetC_nil_of _ _ (cfgState _ _).cfg.outgoing rfl $$ Hout with %Hvout
  icases ownIdsetC_nil_of _ _ (cfgState _ _).cfg.learnersNext rfl $$ Hln1 with %Hln1'
  iapply HΦ
  iframe Hcs Hv0 Hpm Hprsm
  isplitr
  · ipureintro; exact ⟨by rw [Harr1, Hvout], Hln1', Hal1, Hwit1.1⟩
  ihave Hl1 := (show ownIdsetC (GF := GF) cfgv.Learners' (DFrac.own 1)
    (cfgState (GMap.listToSet c.Voters') (GMap.listToSet c.Learners')).cfg.learners ⊢
    ownIdsetC cfgv.Learners' (DFrac.own 1) (GMap.listToSet c.Learners') from .rfl) $$ Hl1
  iframe Hl1 Hin
  isplitr
  · ipureintro; exact domSet_gset _
  isplitr
  · ipureintro
    rw [Hdom]
    apply GMap.set_eq; intro k
    rw [GMap.elem_of_dom', cfgState, cfgFlags_mem, GMap.elem_of_union]
  iapply BigSepM.bigSepM_mono ?_ $$ Hprogs
  intro k pr _
  iintro ⟨%p, Hp, %Hpl⟩
  iexists p
  iframe Hp
  ipureintro
  obtain ⟨Hpl, Hpw⟩ := Hpl
  refine ⟨?_, by rw [Hpw]; simp [cfgState, cfgM]⟩
  simp only [cfgState] at Hpl
  rw [cfgFlags_lookup] at Hpl
  by_cases hv : k ∈ GMap.listToSet c.Voters'
  · rw [ite_eq_left hv] at Hpl; rw [← Option.some.inj Hpl]; simp [hv]
  · rw [ite_eq_right hv] at Hpl
    by_cases hl : k ∈ GMap.listToSet c.Learners'
    · rw [ite_eq_left hl] at Hpl; rw [← Option.some.inj Hpl]; simp [hv]
    · rw [ite_eq_right hl] at Hpl; cases Hpl

end spec

end EtcdGrove
end Perennial
