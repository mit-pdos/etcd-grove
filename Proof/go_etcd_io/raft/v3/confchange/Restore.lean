/-
Proof of `Spec/go_etcd_io/raft/v3/confchange/Restore.lean`. (2026-10-15, raft v3.7 retarget,
stage R2: the `ConfState` a pointer, the changes `*pb.ConfChangeSingle` pointers; the joint
case's `chain` invariant also holds the `ConfState`, which the `EnterJoint` closure reads
through `GetAutoLeave`.)

Until 2026-10-08 this file was `axiom confchange.Restore.wp_proof` (the Rocq
`proof_confchange_Restore.v`'s `Axiom`): the package was not translated. It is now
proved from its callees (`toConfChangeSingle`, the `chg.Simple(cc)` and
`chg.EnterJoint(...)` closures, `chain`). Since 2026-10-14 (reconfiguration stage B8) for any
`ConfState` (`spec`, joint or not; until 2026-10-14 `specG`), each op a `Simple` or `EnterJoint` step of the
model (`restoreM`, `InvRestore.lean`) on the pair held as `ownCCSt`; the statement of 2026-10-13
(`specS`, non-joint) follows (`spec_simple`).
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.Restore
public import Spec.go_etcd_io.raft.v3.confchange.toConfChangeSingle
public import Spec.go_etcd_io.raft.v3.confchange.Changer__Simple
public import Spec.go_etcd_io.raft.v3.confchange.Changer__EnterJoint
public import Spec.go_etcd_io.raft.v3.confchange.chain
public import Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetAutoLeave

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

-- The theorems of this file are elaborated one at a time, a precaution: Perennial's `iframe ∗`
-- keeps a process-global reentrancy flag, so two of them framing at once can skip its prepass
-- (notes/flaky-stepleader-build.md). Delete with that file's stopgap.
set_option Elab.async false

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- What `ownProgress` holds besides the points-to: the inflight ring, and that the value
is a `Progress` of the record (a learner's or not, as the value says). -/
def progR2 (pv : tracker.Progress) : IProp GF :=
  iprop(∃ pp : Progress, ownInflights pv.Inflights' pp.infl ∗ ⌜progressAbs pv pp.infl = some pp⌝)

/-- A pair (`Config`, progress map) `Restore` has built so far, in the model's state `s`: the
configuration (`ownCfgCC`), the progress map at `prsm` with its `Progress` objects, each id's
`IsLearner` as `s.prs` says. -/
def ownCCSt (cfg : tracker.Config) (prsm : Loc) (s : CCState) : IProp GF :=
  iprop(∃ (prs : GMap w64 Loc) (pvs : GMap w64 tracker.Progress),
    ownCfgCC cfg (DFrac.own 1) s.cfg ∗ prsm ↦$ prs ∗
    ([∗map] _k ↦ pr;pv ∈ prs;pvs, pr ↦ pv) ∗ ([∗map] _k ↦ pv ∈ pvs, progR2 pv) ∗
    ⌜flagsOf pvs = s.prs⌝)

/-- A `Changer` step's result, its new `Progress` objects given the rings of the old ones
(copies) or their own (fresh). -/
theorem ownCCSt_of_result (chg : confchange.Changer) (base : GMap w64 tracker.Progress)
    (cfg : tracker.Config) (trk : Loc) (s : CCState) :
    ownCfgCC (GF := GF) cfg (DFrac.own 1) s.cfg ∗ ownPrsW chg base trk s.prs ∗
      ([∗map] _k ↦ pv ∈ base, progR2 pv) ⊢ ownCCSt cfg trk s := by
  iintro ⟨Hc, Hw, HR⟩
  unfold ownPrsW
  icases Hw with ⟨%prs, %pvs, Htrk, Hprs, %Hflags, Hnew⟩
  ihave HQ := ownNewPr_transfer chg base (fun _ pv => progR2 (GF := GF) pv)
      (fun _ pv => progR2 (GF := GF) pv) ?_ ?_ pvs $$ [$HR $Hnew]
  · intro k pv0 pv _ h1
    unfold progR2
    iintro ⟨%p, Hinfl, %Habs⟩
    iexists { p with learner := pv.IsLearner' }
    have Hinf : pv.Inflights' = pv0.Inflights' := by rw [h1]
    rw [Hinf]
    iframe Hinfl
    ipureintro
    obtain ⟨_, h2, h3, h4, h5, h7, h8⟩ := (progressAbs_Some _ _ _).1 Habs
    refine (progressAbs_Some _ _ _).2 ⟨rfl, ?_, ?_, ?_, ?_, ?_, h8⟩ <;>
      (rw [h1]; assumption)
  · intro k pv Hf
    unfold progR2
    iintro Hinfl
    iexists progressOf pv .probe (inflightsNew chg.Tracker'.MaxInflight'
      chg.Tracker'.MaxInflightBytes')
    isplitl [Hinfl]
    · simp only [progressOf]; iexact Hinfl
    ipureintro
    exact (progressAbs_Some _ _ _).2 ⟨rfl, Hf.2.2.2.1, rfl, rfl, rfl, rfl, rfl⟩
  unfold ownCCSt
  iexists prs, pvs
  iframe Hc Htrk Hprs HQ
  ipureintro; exact Hflags

/-- The model state of a tracker held as `ownCCSt`, as a `Changer` method reads it. -/
theorem ccState_flags (s : CCState) (pvs : GMap w64 tracker.Progress)
    (Hfl : flagsOf pvs = s.prs) : ({ cfg := s.cfg, prs := flagsOf pvs } : CCState) = s := by
  rw [Hfl]

/-- A `Changer` method (`Simple`, `EnterJoint`) on a tracker held as `ownCCSt s`, the model
answering `some s'`: the result is held as `ownCCSt s'`; the old configuration and progress map
come back (garbage once `chain` moves on). `M` is the model of the method, `call` its
expression, `Hspec` its triple at the tracker. -/
theorem ownCCSt_step (chg : confchange.Changer) (s' : CCState) (r : Option CCState)
    (Hr : r = some s') (cfg : tracker.Config) (trk : Loc) (err : GoInterface)
    (base : GMap w64 tracker.Progress) :
    ownResult (GF := GF) chg base r cfg trk err ∗ ([∗map] _k ↦ pv ∈ base, progR2 pv) ⊢
      ⌜err = interface.nil⌝ ∗ ownCCSt cfg trk s' := by
  subst Hr
  iintro ⟨Hres, HR⟩
  simp only [ownResult]
  icases Hres with ⟨%Herr, Hc, Hw⟩
  isplitr
  · ipureintro; exact Herr
  iapply ownCCSt_of_result chg base cfg trk s' $$ [$Hc $Hw $HR]

/-- `chg.Simple(ccs)` on a tracker holding `ownCCSt s`, the model answering `some s'`. -/
theorem wp_Simple_st (H : confchange.Changer.Simple.spec (GF := GF) (hG := hG))
    (p : Loc) (chg : confchange.Changer) (ccs : GoSlice) (ls : List Loc)
    (l : List ConfChangeSingleM) (s s' : CCState) (dq dqs : DFrac)
    (Hmi : 0 ≤ sint.Z chg.Tracker'.MaxInflight' ∧ sint.Z chg.Tracker'.MaxInflight' < 2 ^ 62)
    (Hm : simpleM l s = some s') :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dq} chg ∗
        ccs ↦*{dqs} ls ∗ ([∗list] q;c ∈ ls;l, ccsRO q c) ∗
        ownCCSt chg.Tracker'.Config' chg.Tracker'.Progress' s }}
      (App (Val (p @!! go.GoType.PointerType confchange.Changer.ty @!! go!"Simple")) (Val #ccs))
    {{ (cfg : tracker.Config) (trk : Loc), RET (PairV (PairV #cfg #trk) #interface.nil);
        p ↦{dq} chg ∗ ccs ↦*{dqs} ls ∗ ownCCSt cfg trk s' }} := by
  iintro %Φ ⟨#Hpkg, Hp, Hccs, #Hcl, Hst⟩ HΦ
  unfold ownCCSt
  icases Hst with ⟨%prs, %pvs, Hc, Hpm, Hpt, HR, %Hfl⟩
  ihave Htc : ownTrackerCC chg.Tracker' (DFrac.own 1) (DFrac.own 1) (DFrac.own 1)
      s.cfg prs pvs $$ [Hc Hpm Hpt]
  · unfold ownTrackerCC
    iframe
  iapply H p chg s.cfg prs pvs ccs ls l dq dqs (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) Hmi
    $$ [$Hpkg $Hp $Hccs $Hcl $Htc]
  inext
  iintro %cfg %trk %err ⟨Hp, Hccs, -, Hres⟩
  rw [ccState_flags s pvs Hfl]
  icases ownCCSt_step chg s' _ Hm cfg trk err pvs $$ [$Hres $HR] with ⟨%Herr, Hst⟩
  try subst Herr
  iapply HΦ
  iframe Hp Hccs
  iunfold ownCCSt at Hst
  iexact Hst

/-- `chg.EnterJoint(al, ccs)` on a tracker holding `ownCCSt s`, the model answering
`some s'`. -/
theorem wp_EnterJoint_st (H : confchange.Changer.EnterJoint.spec (GF := GF) (hG := hG))
    (p : Loc) (chg : confchange.Changer) (al : Bool) (ccs : GoSlice) (ls : List Loc)
    (l : List ConfChangeSingleM) (s s' : CCState) (dq dqs : DFrac)
    (Hmi : 0 ≤ sint.Z chg.Tracker'.MaxInflight' ∧ sint.Z chg.Tracker'.MaxInflight' < 2 ^ 62)
    (Hm : enterJointM al l s = some s') :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dq} chg ∗
        ccs ↦*{dqs} ls ∗ ([∗list] q;c ∈ ls;l, ccsRO q c) ∗
        ownCCSt chg.Tracker'.Config' chg.Tracker'.Progress' s }}
      (App (App (Val (p @!! go.GoType.PointerType confchange.Changer.ty @!! go!"EnterJoint"))
        (Val #al)) (Val #ccs))
    {{ (cfg : tracker.Config) (trk : Loc), RET (PairV (PairV #cfg #trk) #interface.nil);
        p ↦{dq} chg ∗ ccs ↦*{dqs} ls ∗ ownCCSt cfg trk s' }} := by
  iintro %Φ ⟨#Hpkg, Hp, Hccs, #Hcl, Hst⟩ HΦ
  unfold ownCCSt
  icases Hst with ⟨%prs, %pvs, Hc, Hpm, Hpt, HR, %Hfl⟩
  ihave Htc : ownTrackerCC chg.Tracker' (DFrac.own 1) (DFrac.own 1) (DFrac.own 1)
      s.cfg prs pvs $$ [Hc Hpm Hpt]
  · unfold ownTrackerCC
    iframe
  iapply H p chg s.cfg prs pvs al ccs ls l dq dqs (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) Hmi
    $$ [$Hpkg $Hp $Hccs $Hcl $Htc]
  inext
  iintro %cfg %trk %err ⟨Hp, Hccs, -, Hres⟩
  rw [ccState_flags s pvs Hfl]
  icases ownCCSt_step chg s' _ Hm cfg trk err pvs $$ [$Hres $HR] with ⟨%Herr, Hst⟩
  try subst Herr
  iapply HΦ
  iframe Hp Hccs
  iunfold ownCCSt at Hst
  iexact Hst

/-- `chg.Simple(ccs)` from the empty tracker `MakeProgressTracker` built (`cfgState ∅ ∅`): its
voter map `v0` and its (read-only) progress map come back. -/
theorem wp_Simple_empty (H : confchange.Changer.Simple.spec (GF := GF) (hG := hG))
    (p : Loc) (chg : confchange.Changer) (ccs : GoSlice) (ls : List Loc)
    (l : List ConfChangeSingleM) (v0 : Loc) (s' : CCState) (dq dqs : DFrac)
    (Hmi : 0 ≤ sint.Z chg.Tracker'.MaxInflight' ∧ sint.Z chg.Tracker'.MaxInflight' < 2 ^ 62)
    (Harr : chg.Tracker'.Config'.Voters'.arr = [v0, map.nil])
    (Hl : chg.Tracker'.Config'.Learners' = map.nil)
    (Hln : chg.Tracker'.Config'.LearnersNext' = map.nil)
    (Hal : chg.Tracker'.Config'.AutoLeave' = false)
    (Hm : simpleM l (cfgState ∅ ∅) = some s') :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dq} chg ∗
        ccs ↦*{dqs} ls ∗ ([∗list] q;c ∈ ls;l, ccsRO q c) ∗ v0 ↦$ (∅ : GMap w64 Unit) ∗
        chg.Tracker'.Progress' ↦$□ (∅ : GMap w64 Loc) }}
      (App (Val (p @!! go.GoType.PointerType confchange.Changer.ty @!! go!"Simple")) (Val #ccs))
    {{ (cfg : tracker.Config) (trk : Loc), RET (PairV (PairV #cfg #trk) #interface.nil);
        p ↦{dq} chg ∗ ccs ↦*{dqs} ls ∗ v0 ↦$ (∅ : GMap w64 Unit) ∗
        ownCCSt cfg trk s' }} := by
  iintro %Φ ⟨#Hpkg, Hp, Hccs, #Hcl, Hv0, #Hpm⟩ HΦ
  ihave Hprs0 : ([∗map] _k ↦ pr;pv ∈ (∅ : GMap w64 Loc);(∅ : GMap w64 tracker.Progress),
      (pr ↦ pv : IProp GF)) $$ []
  · iapply (BigSepM2.bigSepM2_empty _).2; iempintro
  ihave Htc : ownTrackerCC chg.Tracker' (DFrac.own 1) DFrac.discard (DFrac.own 1)
      (cfgM ∅ ∅) ∅ ∅ $$ [Hv0 Hprs0]
  · unfold ownTrackerCC
    iframe Hpm Hprs0
    ihave Hv0 := (show (v0 ↦$ (∅ : GMap w64 Unit) : IProp GF) ⊢ v0 ↦$ (cfgM ∅ ∅).incoming
      from .rfl) $$ Hv0
    iapply ownCfgCC_intro chg.Tracker'.Config' (DFrac.own 1) (cfgM ∅ ∅) v0 map.nil Harr Hal
      $$ Hv0 [] [] []
    · simp only [cfgM]; iapply ownIdsetC_nil
    · rw [Hl]; simp only [cfgM]; iapply ownIdsetC_nil
    · rw [Hln]; simp only [cfgM]; iapply ownIdsetC_nil
  iapply H p chg (cfgM ∅ ∅) ∅ ∅ ccs ls l dq dqs (DFrac.own 1) DFrac.discard (DFrac.own 1) Hmi
    $$ [$Hpkg $Hp $Hccs $Hcl $Htc]
  inext
  iintro %cfg %trk %err ⟨Hp, Hccs, Htc, Hres⟩
  have Hf0 : flagsOf (∅ : GMap w64 tracker.Progress) = cfgFlags ∅ ∅ := by
    apply GMap.map_eq; intro k
    rw [cfgFlags_lookup, ite_eq_right (GMap.not_elem_of_empty _), ite_eq_right (GMap.not_elem_of_empty _)]
    rfl
  rw [show ({ cfg := cfgM ∅ ∅, prs := flagsOf (∅ : GMap w64 tracker.Progress) } : CCState) =
      cfgState ∅ ∅ by rw [Hf0]; rfl]
  unfold ownTrackerCC
  icases Htc with ⟨Htcc, -, -⟩
  icases ownCfgCC_elim _ _ _ $$ Htcc with ⟨%vin0, %vout0, %Harr0, Hv0, -, -, -, -⟩
  have Hv0' : vin0 = v0 := by rw [Harr] at Harr0; injection Harr0 with h; exact h.symm
  subst Hv0'
  ihave HR0 : ([∗map] _k ↦ pv ∈ (∅ : GMap w64 tracker.Progress), progR2 (GF := GF) pv) $$ []
  · iapply BigSepM.bigSepM_empty.2; iempintro
  icases ownCCSt_step chg s' _ Hm cfg trk err ∅ $$ [$Hres $HR0] with ⟨%Herr, Hst⟩
  try subst Herr
  iapply HΦ
  iframe

/-- The values with their rings make `ownProgress`es, each record's `learner` as `P` says
of the value's `IsLearner`. -/
theorem progs_of_values (prs : GMap w64 Loc) (pvs : GMap w64 tracker.Progress)
    (P : w64 → Bool → Prop)
    (Hdom : ∀ k, (prs !! k).isSome ↔ (pvs !! k).isSome)
    (HP : ∀ k pv, pvs !! k = some pv → P k pv.IsLearner') :
    ([∗map] _k ↦ pr;pv ∈ prs;pvs, (pr ↦ pv : IProp GF)) ∗
      ([∗map] _k ↦ pv ∈ pvs, progR2 (GF := GF) pv) ⊢
      [∗map] k ↦ pr ∈ prs, ∃ pp, ownProgress pr pp ∗ ⌜P k pp.learner⌝ := by
  iintro ⟨Hpt, HR⟩
  ihave HR := (BigSepM2.bigSepM2_sepM (Φ1 := fun (_ : w64) (_ : Loc) => (emp : IProp GF))
    (Φ2 := fun (_ : w64) pv => progR2 (GF := GF) pv)
    (m1 := prs) (m2 := pvs) Hdom).2
    $$ [HR]
  · isplitr
    · iapply (BigSepM.bigSepM_emp (m := prs)).2
      iempintro
    · iexact HR
  ihave H := BigSepM2.bigSepM2_sep_eqv.2 $$ [$Hpt $HR]
  ihave H : ([∗map] k ↦ pr;pv ∈ prs;pvs,
      ((∃ pp, ownProgress pr pp ∗ ⌜P k pp.learner⌝) ∗ emp : IProp GF)) $$ [H]
  · iapply (BigSepM2.bigSepM2_mono (fun {k pr pv} _ hpv => ?_)) $$ H
    iintro ⟨Hp, -, HR⟩
    unfold progR2
    icases HR with ⟨%pp, Hinfl, %Habs⟩
    isplitl
    · iexists pp
      isplitl
      · iapply ownProgress_intro _ _ pp $$ Hp Hinfl
        ipureintro; exact Habs
      · ipureintro
        rw [← ((progressAbs_Some _ _ _).1 Habs).1]
        exact HP k pv hpv
    · iempintro
  icases (BigSepM2.bigSepM2_sepM (Φ1 := fun k pr =>
      iprop(∃ pp, ownProgress (GF := GF) pr pp ∗ ⌜P k pp.learner⌝))
    (Φ2 := fun (_ : w64) (_ : tracker.Progress) => (emp : IProp GF)) (m1 := prs) (m2 := pvs)
    Hdom).1 $$ H with ⟨H, -⟩
  iexact H

/-- The model states `chain` threads through `Restore`'s ops: before op `j ≤ n` (the `n`
`Simple` ops `sops`), the fold of the first `j`; before op `n + 1` (the `EnterJoint`, when
joint), the final state `s'`. -/
def RestoreAt (sops : List ConfChangeSingleM) (s' : CCState) (j : Nat) (s : CCState) :
    Prop :=
  (j ≤ sops.length ∧ simpleFold (sops.take j) (cfgState ∅ ∅) = some s) ∨
  (j = sops.length + 1 ∧ s = s')

/-- The invariant of `chain` over `Restore`'s ops: before op `j`, the pair is either the
empty configuration `Restore` started from (`j = 0`), or held as `ownCCSt` at the model state
`RestoreAt j` (`0 < j`). `MakeProgressTracker`'s own voter map `v0` is only read and comes
back. -/
def restoreInv (chg : confchange.Changer) (v0 : Loc) (sops : List ConfChangeSingleM)
    (s' : CCState) (j : Nat) (cfg : tracker.Config) (prs : Loc) : IProp GF :=
  iprop(v0 ↦$ (∅ : GMap w64 Unit) ∗
    (⌜j = 0 ∧ cfg = chg.Tracker'.Config' ∧ prs = chg.Tracker'.Progress'⌝ ∨
     (⌜0 < j⌝ ∗ ∃ s, ⌜RestoreAt sops s' j s⌝ ∗ ownCCSt cfg prs s)))

/-- One `Simple([c])` op of `Restore`, op `j` of the `Simple` ops `sops` (whose fold succeeds):
from `restoreInv j` to `restoreInv (j + 1)`. -/
theorem wp_restore_simple_op (H : confchange.Changer.Simple.spec (GF := GF) (hG := hG))
    (chg : confchange.Changer) (v0 : Loc) (sops : List ConfChangeSingleM) (s' sN : CCState)
    (Hfull : simpleFold sops (cfgState ∅ ∅) = some sN) (j : Nat) (c : ConfChangeSingleM)
    (Hc : sops[j]? = some c)
    (Hmi : 0 ≤ sint.Z chg.Tracker'.MaxInflight' ∧ sint.Z chg.Tracker'.MaxInflight' < 2 ^ 62)
    (Harr : chg.Tracker'.Config'.Voters'.arr = [v0, map.nil])
    (Hl : chg.Tracker'.Config'.Learners' = map.nil)
    (Hln : chg.Tracker'.Config'.LearnersNext' = map.nil)
    (Hal : chg.Tracker'.Config'.AutoLeave' = false)
    (p : Loc) (cfg : tracker.Config) (prs : Loc) (sl2 : GoSlice) (q : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗
        p ↦ ({ chg with Tracker' := { chg.Tracker' with Config' := cfg, Progress' := prs } } :
          confchange.Changer) ∗
        sl2 ↦* [q] ∗ ccsRO q c ∗ chg.Tracker'.Progress' ↦$□ (∅ : GMap w64 Loc) ∗
        restoreInv chg v0 sops s' j cfg prs }}
      (App (Val (p @!! go.GoType.PointerType confchange.Changer.ty @!! go!"Simple")) (Val #sl2))
    {{ (cfg' : tracker.Config) (trk : Loc), RET (PairV (PairV #cfg' #trk) #interface.nil);
        restoreInv chg v0 sops s' (j + 1) cfg' trk }} := by
  iintro %Φ ⟨#Hpkg, Hp, Hsl2, #Hq, #Hpm, HI⟩ HΦ
  ihave #Hcl : ([∗list] q';c' ∈ [q];[c], ccsRO (GF := GF) q' c') $$ []
  · iapply BigSepL2.bigSepL2_singleton.2; iexact Hq
  obtain ⟨sj, sj1, Hsj, Hstep, Hsj1⟩ := simpleFold_step sops _ sN j c Hc Hfull
  have hj : j < sops.length := (List.getElem?_eq_some_iff.1 Hc).1
  have HR1 : RestoreAt sops s' (j + 1) sj1 := .inl ⟨hj, Hsj1⟩
  unfold restoreInv
  icases HI with ⟨Hv0, (⟨%Hj0, %Hcfg, %Hprs⟩ | ⟨%Hpos, %s, %HR, Hst⟩)⟩
  · -- op 0: from the empty configuration `Restore` started from
    subst Hcfg Hprs Hj0
    have e : sj = cfgState ∅ ∅ := by
      simp only [List.take_zero, simpleFold, Option.some.injEq] at Hsj; exact Hsj.symm
    subst e
    wp_apply wp_Simple_empty H p chg sl2 [q] [c] v0 sj1 _ _ Hmi Harr Hl Hln Hal Hstep
      $$ [$Hpkg $Hp $Hsl2 $Hcl $Hv0 $Hpm] as %cfg' %trk ⟨-, -, Hv0, Hst⟩
    iapply HΦ
    iframe Hv0
    iright
    isplitr
    · ipureintro; omega
    iexists sj1
    iframe Hst
    ipureintro; exact HR1
  · -- op `j > 0`: from the pair the previous op built
    have e : s = sj := by
      rcases HR with ⟨-, h⟩ | ⟨h, -⟩
      · rw [Hsj] at h; exact (Option.some.inj h).symm
      · omega
    subst e
    wp_apply wp_Simple_st H p
      ({ chg with Tracker' := { chg.Tracker' with Config' := cfg, Progress' := prs } } :
        confchange.Changer) sl2 [q] [c] s sj1 _ _ Hmi Hstep
      $$ [$Hpkg $Hp $Hsl2 $Hcl $Hst] as %cfg' %trk ⟨-, -, Hst⟩
    iapply HΦ
    iframe Hv0
    iright
    isplitr
    · ipureintro; omega
    iexists sj1
    iframe Hst
    ipureintro; exact HR1

/-- The `EnterJoint(al, inc...)` op of a joint `Restore`, after the `n` `Simple` ops `sops`
(whose fold `sN` it answers with `s'`): from `restoreInv n` to `restoreInv (n + 1)`. -/
theorem wp_restore_ej_op (H : confchange.Changer.EnterJoint.spec (GF := GF) (hG := hG))
    (chg : confchange.Changer) (v0 : Loc) (sops : List ConfChangeSingleM) (s' sN : CCState)
    (Hfull : simpleFold sops (cfgState ∅ ∅) = some sN) (al : Bool)
    (inc : List ConfChangeSingleM) (Hej : enterJointM al inc sN = some s')
    (hpos : 0 < sops.length)
    (Hmi : 0 ≤ sint.Z chg.Tracker'.MaxInflight' ∧ sint.Z chg.Tracker'.MaxInflight' < 2 ^ 62)
    (p : Loc) (cfg : tracker.Config) (prs : Loc) (sl : GoSlice) (lsi : List Loc) (dqs : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗
        p ↦ ({ chg with Tracker' := { chg.Tracker' with Config' := cfg, Progress' := prs } } :
          confchange.Changer) ∗
        sl ↦*{dqs} lsi ∗ ([∗list] q;c ∈ lsi;inc, ccsRO q c) ∗
        restoreInv chg v0 sops s' sops.length cfg prs }}
      (App (App (Val (p @!! go.GoType.PointerType confchange.Changer.ty @!! go!"EnterJoint"))
        (Val #al)) (Val #sl))
    {{ (cfg' : tracker.Config) (trk : Loc), RET (PairV (PairV #cfg' #trk) #interface.nil);
        sl ↦*{dqs} lsi ∗ restoreInv chg v0 sops s' (sops.length + 1) cfg' trk }} := by
  iintro %Φ ⟨#Hpkg, Hp, Hsl, #Hcl, HI⟩ HΦ
  unfold restoreInv
  icases HI with ⟨Hv0, (⟨%Hj0, -, -⟩ | ⟨-, %s, %HR, Hst⟩)⟩
  · omega
  have e : s = sN := by
    rcases HR with ⟨-, h⟩ | ⟨h, -⟩
    · rw [List.take_length, Hfull] at h; exact (Option.some.inj h).symm
    · omega
  subst e
  wp_apply wp_EnterJoint_st H p
    ({ chg with Tracker' := { chg.Tracker' with Config' := cfg, Progress' := prs } } :
      confchange.Changer) al sl lsi inc s s' _ _ Hmi Hej
    $$ [$Hpkg $Hp $Hsl $Hcl $Hst] as %cfg' %trk ⟨-, Hsl, Hst⟩
  iapply HΦ
  iframe Hv0 Hsl
  iright
  isplitr
  · ipureintro; omega
  iexists s'
  iframe Hst
  ipureintro; exact .inr ⟨rfl, rfl⟩

/-- The pair at the end, in the model's final state: `spec`'s postcondition. -/
theorem ownCCSt_post (cfg : tracker.Config) (prsm : Loc) (s' : CCState) :
    ownCCSt (GF := GF) cfg prsm s' ⊢ ∃ prs : GMap w64 Loc,
      ownCfgCC cfg (DFrac.own 1) s'.cfg ∗ prsm ↦$ prs ∗ ⌜domSet prs = domSet s'.prs⌝ ∗
      ([∗map] k ↦ pr ∈ prs, ∃ p, ownProgress pr p ∗ ⌜s'.prs !! k = some p.learner⌝) := by
  unfold ownCCSt
  iintro ⟨%prs, %pvs, Hc, Hprsm, Hpt, HR, %Hfl⟩
  ihave %Hdom := BigSepM2.bigSepM2_lookup_iff $$ Hpt
  have Hdom' : ∀ k, (prs !! k).isSome ↔ (pvs !! k).isSome := Hdom
  ihave Hprogs := progs_of_values prs pvs (fun k b => s'.prs !! k = some b) Hdom' ?_
    $$ [$Hpt $HR]
  · intro k pv hpv
    have h' := flagsOf_lookup pvs k pv hpv
    rw [Hfl] at h'
    exact h'
  iexists prs
  iframe Hc Hprsm Hprogs
  ipureintro
  apply GMap.set_eq; intro k
  rw [GMap.elem_of_dom', GMap.elem_of_dom', GMap.mem_iff, Hdom' k, ← flagsOf_mem, Hfl]

/-- A conf state's pointer is not `nil`. -/
theorem ownCSM_nonnull (p : Loc) (dq : DFrac) (c : ConfStateM) :
    ownCSM (GF := GF) p dq c ⊢ ownCSM p dq c ∗ ⌜p ≠ null⌝ := by
  iintro H
  simp only [ownCSM]
  iunfold csPts at H
  iNamed H
  isplitl
  · iunfold csPts
    iexists sv, sl, so, sn, pa
    isplitr
    · ipureintro; exact Hnn
    iframe HV Hv HL Hl HO Ho HN Hn HA cA Hpb
    ipureintro; exact Hal
  · ipureintro; exact Hnn

/-- `cs.GetAutoLeave()` of an owned (non-`nil`) conf state. -/
theorem wp_GetAutoLeave_own
    (wp_ConfState_GetAutoLeave : raftpb.ConfState.GetAutoLeave.spec (GF := GF) (hG := hG))
    (p : Loc) (dq : DFrac) (c : ConfStateM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ ownCSM p dq c }}
      (App (Val (p @!! go.GoType.PointerType raftpb.ConfState.ty @!! go!"GetAutoLeave"))
        (Val #()))
    {{ RET #c.AutoLeave'; ownCSM p dq c }} := by
  iintro %Φ ⟨#Hpkg, Hcs⟩ HΦ
  icases ownCSM_nonnull p dq c $$ Hcs with ⟨Hcs, %Hnn⟩
  iapply wp_ConfState_GetAutoLeave p dq c $$ [$Hpkg Hcs]
  · unfold csOpt; iright; iexact Hcs
  inext
  iintro Hcs
  iapply HΦ
  unfold csOpt
  icases Hcs with (⟨%Hn, -⟩ | Hcs)
  · exact absurd Hn Hnn
  · iexact Hcs

theorem confchange.Restore.wp_proof
    (wp_confchange_toConfChangeSingle : confchange.toConfChangeSingle.spec (GF := GF) (hG := hG))
    (wp_Changer_Simple : confchange.Changer.Simple.spec (GF := GF) (hG := hG))
    (wp_Changer_EnterJoint : confchange.Changer.EnterJoint.spec (GF := GF) (hG := hG))
    (wp_confchange_chain : confchange.chain.spec (GF := GF) (hG := hG))
    (wp_ConfState_GetAutoLeave : raftpb.ConfState.GetAutoLeave.spec (GF := GF) (hG := hG)) :
    confchange.Restore.spec (GF := GF) (hG := hG) := by
  intro chg cs c dq v0 s' Hm Hmi Harr Hl Hln Hal
  wp_start as ⟨Hcs, Hv0, #Hpm⟩
  wp_auto
  wp_apply wp_confchange_toConfChangeSingle cs c dq $$ [$Hcs]
    as %outs %ins %lo %li ⟨Hcs, Houts, #Hlo, Hins, #Hli, Hinscap⟩
  ihave %Houtslen := ownSlice_len $$ Houts
  ihave %Hinslen := ownSlice_len $$ Hins
  ihave %Hlolen := BigSepL2.bigSepL2_length $$ Hlo
  ihave %Hlilen := BigSepL2.bigSepL2_length $$ Hli
  wp_if_destruct
  · -- not joint: one `Simple` per change of `in`
    have Hvo : c.VotersOutgoing' = [] := by
      have h := Houtslen.1
      rw [Hlolen, Hif, restoreOutCC, List.length_map] at h
      exact List.eq_nil_of_length_eq_zero (by rw [h]; rfl)
    have Hfull : simpleFold (restoreInCC c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext')
        (cfgState ∅ ∅) = some s' := by
      rw [Hvo] at Hm ⊢
      unfold restoreM restoreSimpleOps at Hm; simpa using Hm
    ihave HI0 : restoreInv chg v0 (restoreInCC c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext') s' 0 chg.Tracker'.Config' chg.Tracker'.Progress' $$ [Hv0]
    · unfold restoreInv
      iframe Hv0
      ileft
      ipureintro; exact ⟨rfl, rfl, rfl⟩
    ihave Hnil : (slice.nil ↦* ([] : List GoFunc)) $$ []
    · iapply ownSlice_nil
    ihave Hcap : ownSliceCap GoFunc slice.nil (DFrac.own 1) $$ []
    · iapply ownSliceCap_nil
    -- `for _, cc := range ins { cc := cc; ops = append(ops, func(chg) {chg.Simple(cc)}) }`:
    -- after `n` iterations, `ops` holds `n` closures, the `j`th taking the pair from
    -- `restoreInv j` to `restoreInv (j + 1)`
    ihave IH : iprop(∃ (n : w64) (ops' : GoSlice) (fs : List GoFunc) (x : Loc),
        "i" ∷ i_ptr ↦ n ∗
        "ops" ∷ ops_ptr ↦ ops' ∗
        "Hcc" ∷ cc_ptr ↦ x ∗
        "Hops" ∷ ops' ↦* fs ∗
        "Hopscap" ∷ ownSliceCap GoFunc ops' (DFrac.own 1) ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ ((restoreInCC c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext').length : Int) ∧ fs.length = sint.nat n⌝ ∗
        "#Hfs" ∷ □ (∀ (j : Nat) (f : GoFunc), ⌜fs[j]? = some f⌝ -∗
          opSpec f chg (restoreInv chg v0 (restoreInCC c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext') s' j) (restoreInv chg v0 (restoreInCC c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext') s' (j + 1))))
      $$ [i ops cc Hnil Hcap]
    · iexists W64 0, slice.nil, [], zero_val Loc
      simp only [named]
      iframe i ops cc Hnil Hcap
      isplitr
      · ipureintro; exact ⟨by decide, by word, rfl⟩
      imodintro
      iintro %j %f %Hjf
      simp at Hjf
    wp_for IH
    wp_if_destruct
    · have Hlt : sint.nat n < (restoreInCC c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext').length := by
        have := Hinslen.1; rw [← Hlilen]; word
      have Hltq : sint.nat n < li.length := by rw [Hlilen]; exact Hlt
      obtain ⟨cc0, Hc⟩ : ∃ cc0, (restoreInCC c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext')[sint.nat n]? = some cc0 :=
        ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨q, Hq⟩ : ∃ q, li[sint.nat n]? = some q := ⟨_, List.getElem?_eq_getElem Hltq⟩
      ihave #Hcq := BigSepL2.bigSepL2_lookup (Φ := fun _ q c => ccsRO (GF := GF) q c) Hq Hc $$ Hli
      have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ins.len := ⟨Hn.1, Hif⟩
      simp only [Hbnd', _root_.and_self]
      wp_apply wp_load_slice_index ins (sint.Z n) _ _ q Hn.1 $$ [Hins] with Hins
      · iframe Hins; ipureintro; exact Hq
      -- the closure captures its loop-local copy `cc`, read-only from here on
      ipersist cc
      -- `ops = append(ops, func(chg Changer) {...})`
      wp_func_lits
      wp_apply wp_slice_literal (V := GoFunc) [_]
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply wp_slice_append $$ [$Hops $Hopscap $Hsl] as %ops2 ⟨Hops, Hopscap, -⟩
      wp_for_post
      iframe
      iexists n + W64 1, ops2, _, q
      simp only [named]
      iframe i ops Hcc Hops Hopscap
      have Hfslen : fs.length = sint.nat n := Hn.2.2
      isplitr
      · ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [List.length_append, List.length_singleton, Hfslen]; word
      -- the closures' triples: the old ones, and the new one, op `fs.length = n`
      imodintro
      iintro %j %f %Hjf
      rcases Nat.lt_or_ge j fs.length with Hj | Hj
      · rw [List.getElem?_append_left Hj] at Hjf
        iapply Hfs $$ %j %f %Hjf
      have Hj' : j = fs.length := by
        have := (List.getElem?_eq_some_iff.1 Hjf).1
        rw [List.length_append, List.length_singleton] at this
        omega
      subst Hj'
      rw [List.getElem?_concat_length] at Hjf
      cases Hjf
      -- `func(chg Changer) { return chg.Simple(cc) }`: `Simple([cc])` on the pair in `chg`'s
      -- tracker, from `restoreInv fs.length` to `restoreInv (fs.length + 1)`
      unfold opSpec
      iintro %cfg %prs
      wp_start_folded as HI
      wp_auto
      wp_apply wp_slice_literal (V := Loc) [q]
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      rw [← Hfslen] at Hc
      wp_apply wp_restore_simple_op wp_Changer_Simple chg v0 (restoreInCC c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext') s' s' Hfull fs.length cc0 Hc Hmi
        Harr Hl Hln Hal _ cfg prs _ q $$ [$Hpkg $chg $Hsl2 $Hcq $Hpm $HI] as %cfg' %trk HI
      iapply HΦ
      iexact HI
    have Hn' : sint.nat n = (restoreInCC c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext').length := by
      have := Hinslen.1; rw [← Hlilen]; word
    -- `chain(chg, ops...)`
    wp_apply wp_confchange_chain chg ops' fs _ (restoreInv chg v0 (restoreInCC c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext') s')
        $$ [$Hops $HI0 $Hfs] as %cfg %prs ⟨Hops, HI⟩
    unfold restoreInv
    icases HI with ⟨Hv0, (⟨%Hj0, %Hc1, %Hc2⟩ | ⟨%Hpos, %s, %HR, Hst⟩)⟩
    · -- no op (no voter, no learner: a new cluster's conf state, 2026-10-16, stage R8b): the
      -- tracker's own maps come back
      have Hnil : restoreInCC c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext' = [] := by
        rw [Hn.2.2, Hn'] at Hj0; exact List.eq_nil_of_length_eq_zero Hj0
      iapply HΦ $$ %cfg %prs %(∅ : GMap w64 Loc)
      iframe Hcs Hv0 Hpm
      ileft
      ipureintro
      refine ⟨?_, Hc1, Hc2, rfl⟩
      rw [Hvo] at Hnil
      unfold restoreSimpleOps; rw [ite_eq_left Hvo]; exact Hnil
    have e : s = s' := by
      rcases HR with ⟨-, h⟩ | ⟨h, -⟩
      · rw [Hn.2.2, Hn', List.take_length, Hfull] at h; exact (Option.some.inj h).symm
      · rw [Hn.2.2, Hn'] at h; omega
    subst e
    have Hne : restoreInCC c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext' ≠ [] := by
      intro h; rw [Hn.2.2, Hn', h] at Hpos; simp at Hpos
    rw [Hvo] at Hne
    icases ownCCSt_post cfg prs s $$ Hst with ⟨%prsm, Hc, Hprsm, %Hdom, Hprogs⟩
    iapply HΦ
    iframe Hcs Hv0 Hpm
    iright
    iframe Hc Hprsm Hprogs
    ipureintro
    refine ⟨?_, Hdom⟩
    unfold restoreSimpleOps; rw [ite_eq_left Hvo]; exact Hne
  · -- joint: one `Simple(AddNode)` per outgoing voter, then `EnterJoint(cs.GetAutoLeave(), in...)`
    have Hvo : c.VotersOutgoing' ≠ [] := by
      intro h; apply Hif
      have h' := Houtslen.1
      rw [Hlolen] at h'
      simp only [restoreOutCC, h, List.map_nil, List.length_nil] at h'
      word
    have Hm' := Hm
    unfold restoreM restoreSimpleOps at Hm'
    simp only [Hvo, ↓reduceIte] at Hm'
    obtain ⟨sN, Hfull, Hej⟩ : ∃ sN, simpleFold (restoreOutCC c.VotersOutgoing') (cfgState ∅ ∅) = some sN ∧
        enterJointM c.AutoLeave' (restoreInCC c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext') sN =
          some s' := by
      cases h : simpleFold (restoreOutCC c.VotersOutgoing') (cfgState ∅ ∅) with
      | none => rw [h] at Hm'; cases Hm'
      | some sN => rw [h] at Hm'; exact ⟨sN, rfl, Hm'⟩
    have hpos : 0 < (restoreOutCC c.VotersOutgoing').length := by
      rw [restoreOutCC, List.length_map]
      exact Nat.pos_of_ne_zero (fun h => Hvo (List.eq_nil_of_length_eq_zero h))
    -- the `EnterJoint` closure reads `cs` and `incoming`, read-only from here on; the
    -- `ConfState` itself (`GetAutoLeave`) is threaded through `chain`'s invariant
    ipersist cs
    ipersist incoming
    ipersist Hins
    ihave HI0 : iprop(restoreInv chg v0 (restoreOutCC c.VotersOutgoing') s' 0 chg.Tracker'.Config' chg.Tracker'.Progress' ∗ ownCSM cs dq c) $$ [Hv0 Hcs]
    · iframe Hcs
      unfold restoreInv
      iframe Hv0
      ileft
      ipureintro; exact ⟨rfl, rfl, rfl⟩
    ihave Hnil : (slice.nil ↦* ([] : List GoFunc)) $$ []
    · iapply ownSlice_nil
    ihave Hcap : ownSliceCap GoFunc slice.nil (DFrac.own 1) $$ []
    · iapply ownSliceCap_nil
    -- `for _, cc := range outs { cc := cc; ops = append(ops, func(chg) {chg.Simple(cc)}) }`:
    -- after `n` iterations, `ops` holds `n` closures, the `j`th taking the pair from
    -- `restoreInv j` to `restoreInv (j + 1)` (each with the `ConfState`)
    ihave IH : iprop(∃ (n : w64) (ops' : GoSlice) (fs : List GoFunc) (x : Loc),
        "i" ∷ i_ptr ↦ n ∗
        "ops" ∷ ops_ptr ↦ ops' ∗
        "Hcc" ∷ cc_ptr ↦ x ∗
        "Hops" ∷ ops' ↦* fs ∗
        "Hopscap" ∷ ownSliceCap GoFunc ops' (DFrac.own 1) ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ ((restoreOutCC c.VotersOutgoing').length : Int) ∧ fs.length = sint.nat n⌝ ∗
        "#Hfs" ∷ □ (∀ (j : Nat) (f : GoFunc), ⌜fs[j]? = some f⌝ -∗
          opSpec f chg (fun cfg prs => iprop(restoreInv chg v0 (restoreOutCC c.VotersOutgoing') s' j cfg prs ∗ ownCSM cs dq c))
            (fun cfg prs => iprop(restoreInv chg v0 (restoreOutCC c.VotersOutgoing') s' (j + 1) cfg prs ∗ ownCSM cs dq c))))
      $$ [i ops cc Hnil Hcap]
    · iexists W64 0, slice.nil, [], zero_val Loc
      simp only [named]
      iframe i ops cc Hnil Hcap
      isplitr
      · ipureintro; exact ⟨by decide, by word, rfl⟩
      imodintro
      iintro %j %f %Hjf
      simp at Hjf
    wp_for IH
    wp_if_destruct
    · have Hlt : sint.nat n < (restoreOutCC c.VotersOutgoing').length := by
        have := Houtslen.1; rw [← Hlolen]; word
      have Hltq : sint.nat n < lo.length := by rw [Hlolen]; exact Hlt
      obtain ⟨cc0, Hc⟩ : ∃ cc0, (restoreOutCC c.VotersOutgoing')[sint.nat n]? = some cc0 :=
        ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨q, Hq⟩ : ∃ q, lo[sint.nat n]? = some q := ⟨_, List.getElem?_eq_getElem Hltq⟩
      ihave #Hcq := BigSepL2.bigSepL2_lookup (Φ := fun _ q c => ccsRO (GF := GF) q c) Hq Hc $$ Hlo
      have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z outs.len := ⟨Hn.1, Hif⟩
      simp only [Hbnd', _root_.and_self]
      wp_apply wp_load_slice_index outs (sint.Z n) _ _ q Hn.1 $$ [Houts] with Houts
      · iframe Houts; ipureintro; exact Hq
      -- the closure captures its loop-local copy `cc`, read-only from here on
      ipersist cc
      -- `ops = append(ops, func(chg Changer) {...})`
      wp_func_lits
      wp_apply wp_slice_literal (V := GoFunc) [_]
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply wp_slice_append $$ [$Hops $Hopscap $Hsl] as %ops2 ⟨Hops, Hopscap, -⟩
      wp_for_post
      iframe
      iexists n + W64 1, ops2, _, q
      simp only [named]
      iframe i ops Hcc Hops Hopscap
      have Hfslen : fs.length = sint.nat n := Hn.2.2
      isplitr
      · ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [List.length_append, List.length_singleton, Hfslen]; word
      -- the closures' triples: the old ones, and the new one, op `fs.length = n`
      imodintro
      iintro %j %f %Hjf
      rcases Nat.lt_or_ge j fs.length with Hj | Hj
      · rw [List.getElem?_append_left Hj] at Hjf
        iapply Hfs $$ %j %f %Hjf
      have Hj' : j = fs.length := by
        have := (List.getElem?_eq_some_iff.1 Hjf).1
        rw [List.length_append, List.length_singleton] at this
        omega
      subst Hj'
      rw [List.getElem?_concat_length] at Hjf
      cases Hjf
      -- `func(chg Changer) { return chg.Simple(cc) }`: `Simple([cc])` on the pair in `chg`'s
      -- tracker, from `restoreInv fs.length` to `restoreInv (fs.length + 1)`
      unfold opSpec
      iintro %cfg %prs
      wp_start_folded as HI
      icases HI with ⟨HI, Hcs⟩
      wp_auto
      wp_apply wp_slice_literal (V := Loc) [q]
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      rw [← Hfslen] at Hc
      wp_apply wp_restore_simple_op wp_Changer_Simple chg v0 (restoreOutCC c.VotersOutgoing') s' sN Hfull fs.length cc0 Hc Hmi
        Harr Hl Hln Hal _ cfg prs _ q $$ [$Hpkg $chg $Hsl2 $Hcq $Hpm $HI] as %cfg' %trk HI
      iapply HΦ
      dsimp only
      iframe HI Hcs
    have Hn' : sint.nat n = (restoreOutCC c.VotersOutgoing').length := by
      have := Houtslen.1; rw [← Hlolen]; word
    -- `ops = append(ops, func(chg Changer) { return chg.EnterJoint(cs.GetAutoLeave(), incoming...) })`
    wp_func_lits
    wp_apply wp_slice_literal (V := GoFunc) [_]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [$Hops $Hopscap $Hsl] as %ops2 ⟨Hops, Hopscap, -⟩
    have Hfslen : fs.length = (restoreOutCC c.VotersOutgoing').length := by rw [Hn.2.2, Hn']
    -- `chain(chg, ops...)`
    wp_apply wp_confchange_chain chg ops2 (fs ++ [_]) _
        (fun j cfg prs => iprop(restoreInv chg v0 (restoreOutCC c.VotersOutgoing') s' j cfg prs ∗ ownCSM cs dq c))
        $$ [$Hops $HI0] as %cfg %prs ⟨Hops, HI⟩
    · imodintro
      iintro %j %f %Hjf
      rcases Nat.lt_or_ge j fs.length with Hj | Hj
      · rw [List.getElem?_append_left Hj] at Hjf
        iapply Hfs $$ %j %f %Hjf
      have Hj' : j = fs.length := by
        have := (List.getElem?_eq_some_iff.1 Hjf).1
        rw [List.length_append, List.length_singleton] at this
        omega
      subst Hj'
      rw [List.getElem?_concat_length] at Hjf
      cases Hjf
      unfold opSpec
      iintro %cfg %prs
      wp_start_folded as HI
      icases HI with ⟨HI, Hcs⟩
      wp_auto
      wp_apply wp_GetAutoLeave_own wp_ConfState_GetAutoLeave cs dq c $$ [$Hcs] as Hcs
      rw [Hfslen]
      wp_apply wp_restore_ej_op wp_Changer_EnterJoint chg v0 (restoreOutCC c.VotersOutgoing') s' sN Hfull c.AutoLeave' _ Hej
        hpos Hmi _ cfg prs ins li _ $$ [$Hpkg $chg $Hins $Hli $HI] as %cfg' %trk ⟨-, HI⟩
      iapply HΦ
      dsimp only
      iframe HI Hcs
    icases HI with ⟨HI, Hcs⟩
    unfold restoreInv
    icases HI with ⟨Hv0, (⟨%Hj0, -, -⟩ | ⟨%Hpos, %s, %HR, Hst⟩)⟩
    · exfalso; simp at Hj0
    have e : s = s' := by
      rcases HR with ⟨h, -⟩ | ⟨-, h⟩
      · simp only [List.length_append, List.length_singleton, Hfslen] at h; omega
      · exact h
    subst e
    icases ownCCSt_post cfg prs s $$ Hst with ⟨%prsm, Hc, Hprsm, %Hdom, Hprogs⟩
    iapply HΦ
    iframe Hcs Hv0 Hpm
    iright
    iframe Hc Hprsm Hprogs
    ipureintro
    refine ⟨?_, Hdom⟩
    unfold restoreSimpleOps; rw [ite_eq_right Hvo]
    intro h; rw [h] at hpos; simp at hpos

end proof

end EtcdGrove
end Perennial
