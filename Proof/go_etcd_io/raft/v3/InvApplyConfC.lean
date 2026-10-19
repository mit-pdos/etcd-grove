/-
Applying a configuration change at any configuration (2026-10-13, reconfiguration stage A2),
Lean-first.

* `CCGood`: what every `confchange` state the node can reach satisfies -- the progress map
  tracks exactly the configuration's ids (`CfgM.ids`), each tracked `IsLearner` is whether
  the id is a learner, a learner is no voter, a staged learner is an outgoing voter and no
  incoming one. Every `Changer` operation keeps it (`ccApplyM_good`): so a `Changer` result is
  the configuration of an `ownTrackerC` (`LearnerFlagsC`, `domSet = ids`), which stage A1
  checked by hand.

Raft v3.7 retarget (stage R4): the heap section only; the model (`section model`) is in
`CCApplyC.lean` since stage R1, imported here.
-/
module

public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Proof.go_etcd_io.raft.v3.CCApplyC

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3


/-! ## The tracker as a `Changer` reads it, and a result as `switchToConfig` takes it -/

section heap
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `ownTracker_toCC` at any configuration: the node's tracker at `c` as the `Changer` reads it
(`ownTrackerCC` at `c`), the old `Progress` objects' rings set apart (`progRAt`), the tally;
the `Changer`'s state is `⟨c, trkFlags t.peers⟩`, which is reachable (`CCGood`) and passes
`checkInvariants`. -/
theorem ownTrackerC_toCC (c : CfgM) (tv : tracker.ProgressTracker) (t : Trk) :
    ownTrackerC (GF := GF) c tv t ⊢ ∃ (pvs : GMap w64 tracker.Progress),
      ownTrackerCC tv (DFrac.own 1) DFrac.discard (DFrac.own 1) c t.prs pvs ∗
      ([∗map] k ↦ pv ∈ pvs, progRAt t.peers k pv) ∗
      tv.Votes' ↦$ t.votes ∗
      ⌜flagsOf pvs = trkFlags t.peers⌝ ∗
      ⌜0 ≤ sint.Z tv.MaxInflight' ∧ sint.Z tv.MaxInflight' < 2 ^ 62⌝ ∗
      ⌜CCGood ⟨c, trkFlags t.peers⟩ ∧ CfgInv ⟨c, trkFlags t.peers⟩ ∧
        domSet t.prs = c.ids ∧ (GMap.size t.prs : Int) ≤ 2 ^ 62⌝ := by
  iintro Hown
  iunfold ownTrackerC at Hown
  iNamed Hown
  ihave H : ([∗map] k ↦ pr;p ∈ t.prs;t.peers, ∃ pv : tracker.Progress,
      (pr ↦ pv ∗ (⌜pv.IsLearner' = p.learner ∧ pv.IsWitness' = false⌝ ∗ (emp ∗ progRAt (GF := GF) t.peers k pv)) :
        IProp GF))
      $$ [Hprogs]
  · iapply (BigSepM2.bigSepM2_mono (fun {k pr p} _ hp => ?_)) $$ Hprogs
    iintro Hp
    unfold ownProgress
    iNamed Hp
    iexists pv
    iframe Hpv
    isplitr
    · ipureintro
      exact ⟨((progressAbs_Some _ _ _).1 Habs).1,
        ((progressAbs_Some _ _ _).1 Habs).2.2.2.2.2.2.2.2.trans (Hnw k p hp).1⟩
    isplitr
    · iempintro
    unfold progRAt
    iexists p
    iframe Hinfl
    ipureintro; exact ⟨hp, Habs⟩
  ihave %Hdom0 := BigSepM2.bigSepM2_lookup_iff $$ H
  have Hdom0' : ∀ k, (t.prs !! k).isSome ↔ (t.peers !! k).isSome := Hdom0
  -- the records' flags, read off with their keys
  ihave %Hlf0 := BigSepM2.bigSepM2_lookup_iff $$ H
  icases (BigSepM2.bigSepM2_sepM (Φ1 := fun k pr => iprop(∃ pv : tracker.Progress,
      (pr ↦ pv ∗ (⌜pv.IsLearner' = decide (k ∈ c.learners) ∧ pv.IsWitness' = false⌝ ∗
        (emp ∗ progRAt (GF := GF) t.peers k pv)) : IProp GF)))
    (Φ2 := fun (_ : w64) (_ : Progress) => (emp : IProp GF)) Hdom0).1 $$ [H] with ⟨H, -⟩
  · iapply (BigSepM2.bigSepM2_mono (fun {k pr p} _ hp => ?_)) $$ H
    iintro ⟨%pv, Hpv, %Hl, HR⟩
    isplitl
    · iexists pv
      iframe Hpv HR
      ipureintro; exact ⟨by rw [Hl.1]; exact Hflags k p hp, Hl.2⟩
    · iempintro
  icases bigSepM_exist_sepM2 t.prs _ $$ H with ⟨%pvs, H⟩
  ihave %HdomP := BigSepM2.bigSepM2_lookup_iff $$ H
  have Hdom' : ∀ k, (t.prs !! k).isSome ↔ (pvs !! k).isSome := HdomP
  icases BigSepM2.bigSepM2_sep_eqv.1 $$ H with ⟨Hpt, H⟩
  icases BigSepM2.bigSepM2_sep_eqv.1 $$ H with ⟨Hl, H⟩
  ihave %Hlf := BigSepM2.bigSepM2_pure_intro $$ Hl
  icases (BigSepM2.bigSepM2_sepM (Φ1 := fun (_ : w64) (_ : Loc) => (emp : IProp GF))
    (Φ2 := fun k pv => progRAt (GF := GF) t.peers k pv) HdomP).1 $$ H with ⟨-, HR⟩
  iexists pvs
  iframe HR Hvotes
  isplitl [Hcfg Hpt]
  · unfold ownTrackerCC
    iframe Hcfg Hpt Hprs
    ipureintro
    intro k pv hpv
    obtain ⟨pr, hpr⟩ := Option.isSome_iff_exists.1 ((Hdom' k).2 (by rw [hpv]; rfl))
    exact (Hlf k pr pv hpr hpv).2
  ipureintro
  have Hfl : flagsOf pvs = trkFlags t.peers := by
    apply GMap.map_eq; intro k
    rw [flagsOf_lookup', trkFlags_lookup]
    cases hpv : pvs !! k with
    | none =>
      have h1 : (t.prs !! k).isSome = false := by
        cases h : t.prs !! k with
        | none => rfl
        | some _ => have := (Hdom' k).1 (by rw [h]; rfl); rw [hpv] at this; cases this
      cases hp : t.peers !! k with
      | none => rfl
      | some _ => have := (Hdom0' k).2 (by rw [hp]; rfl); rw [h1] at this; cases this
    | some pv =>
      obtain ⟨pr, hpr⟩ := Option.isSome_iff_exists.1 ((Hdom' k).2 (by rw [hpv]; rfl))
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 ((Hdom0' k).1 (by rw [hpr]; rfl))
      rw [hp]
      simp only [Option.map_some]
      rw [(Hlf k pr pv hpr hpv).1, Hflags k p hp]
  refine ⟨Hfl, HmaxInfl, ⟨fun k => ?_, fun k b hb => ?_,
    fun k hk => ⟨(Hinv.2.2.1 k hk).2.1, (Hinv.2.2.1 k hk).1⟩,
    fun k hk => (Hinv.2.1 k hk).1⟩, Hinv, Hdom, Hsize⟩
  · show k ∈ trkFlags t.peers ↔ k ∈ c.ids
    rw [← Hdom, GMap.elem_of_dom', GMap.mem_iff, GMap.mem_iff, trkFlags_lookup, Hdom0' k]
    cases t.peers !! k <;> rfl
  · show b = decide (k ∈ c.learners)
    rw [trkFlags_lookup] at hb
    cases hp : t.peers !! k with
    | none => rw [hp] at hb; cases hb
    | some p =>
      rw [hp] at hb
      simp only [Option.map_some, Option.some.injEq] at hb
      rw [← hb]; exact Hflags k p hp

/-- What a result's new object is, once the old objects' rings are moved to it. -/
private def newPrQC (chg : confchange.Changer) (peers : GMap w64 Progress) (k : w64)
    (pv : tracker.Progress) : IProp GF :=
  iprop(∃ p, ownInflights pv.Inflights' p.infl ∗
    ⌜progressAbs pv p.infl = some p ∧ PrKeptAt peers chg.LastIndex' k p ∧ p.witness = false⌝)

/-- `ownResult_noop_transfer` at any configuration: a `Changer` result in a reachable state
`s'` (`CCGood`, `CfgInv`), with the old objects' rings moved to the new ones, is the new
configuration `switchToConfig` takes (`ownConfigC s'.cfg`), each new `Match` the old one or
`0` (`MatchKept`). -/
theorem ownResult_transfer (s' : CCState) (Hgood : CCGood s') (Hinv : CfgInv s')
    (chg : confchange.Changer)
    (base : GMap w64 tracker.Progress) (peers : GMap w64 Progress) (cfgv : tracker.Config)
    (trk : Loc) (Hsz : (GMap.size s'.cfg.ids : Int) ≤ 2 ^ 62) (Hnw : NoWitP peers)
    (H0 : W64 0 ∉ s'.cfg.ids) :
    ownCfgCC (GF := GF) cfgv (DFrac.own 1) s'.cfg ∗
      ownPrsW chg base trk s'.prs ∗
      ([∗map] k ↦ pv ∈ base, progRAt peers k pv) ⊢
      |==> ∃ (prs : GMap w64 Loc) (pvs : GMap w64 Progress),
        ownConfigC s'.cfg cfgv trk prs pvs ∗ ⌜MatchKept peers pvs⌝ ∗
        ⌜PrKept peers pvs chg.LastIndex'⌝ ∗ ⌜domSet prs = s'.cfg.ids⌝ := by
  iintro ⟨Hc, Hw, HR⟩
  unfold ownPrsW
  icases Hw with ⟨%prs, %pvs, Htrk, Hprs, %Hflags, Hnew⟩
  ihave HQ := ownNewPr_transfer chg base (fun k pv => progRAt (GF := GF) peers k pv)
      (fun k pv => newPrQC (GF := GF) chg peers k pv) ?_ ?_ pvs $$ [$HR $Hnew]
  · intro k pv0 pv _ h1
    unfold progRAt newPrQC
    iintro ⟨%p, %Hp, Hinfl, %Habs⟩
    iexists { p with learner := pv.IsLearner' }
    have Hinf : pv.Inflights' = pv0.Inflights' := by rw [h1]
    rw [Hinf]
    iframe Hinfl
    ipureintro
    obtain ⟨_, h2, h3, h4, h5, h6, h7, h8, h9⟩ := (progressAbs_Some _ _ _).1 Habs
    refine ⟨(progressAbs_Some _ _ _).2 ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, h8, ?_⟩, .inl ⟨p, Hp, rfl, rfl, rfl, rfl⟩,
      (Hnw k p Hp).1⟩ <;>
      (rw [h1]; assumption)
  · intro k pv Hf
    unfold newPrQC
    iintro Hinfl
    iexists progressOf pv .probe (inflightsNew chg.Tracker'.MaxInflight'
      chg.Tracker'.MaxInflightBytes')
    isplitl [Hinfl]
    · simp only [progressOf]; iexact Hinfl
    ipureintro
    obtain ⟨Hm, Hn, -, Hst, Hps, -, -, Hw⟩ := Hf
    exact ⟨(progressAbs_Some _ _ _).2 ⟨rfl, Hst, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, .inr ⟨Hm, Hn, Hps, rfl⟩,
      by simp only [progressOf]; exact Hw⟩
  ihave %Hdom0 := BigSepM2.bigSepM2_lookup_iff $$ Hprs
  have Hdom : ∀ k, (prs !! k).isSome ↔ (pvs !! k).isSome := Hdom0
  obtain ⟨Hgd, Hgf, -, -⟩ := Hgood
  have Hlf : ∀ k pv, pvs !! k = some pv → pv.IsLearner' = decide (k ∈ s'.cfg.learners) := by
    intro k pv h
    have h' := flagsOf_lookup pvs k pv h
    rw [Hflags] at h'
    exact Hgf k _ h'
  have Hpdom : domSet prs = s'.cfg.ids := by
    apply GMap.set_eq; intro k
    rw [GMap.elem_of_dom', GMap.mem_iff, Hdom k, ← flagsOf_mem, Hflags]
    exact Hgd k
  ihave HQ2 := (BigSepM2.bigSepM2_sepM (Φ1 := fun (_ : w64) (_ : Loc) => (emp : IProp GF))
    (Φ2 := fun k pv => newPrQC (GF := GF) chg peers k pv) (m1 := prs) (m2 := pvs) Hdom0).2 $$ [HQ]
  · isplitr
    · iapply (BigSepM.bigSepM_emp (m := prs)).2
      iempintro
    · iexact HQ
  ihave H := BigSepM2.bigSepM2_sep_eqv.2 $$ [$Hprs $HQ2]
  ihave H : ([∗map] k ↦ pr;pv ∈ prs;pvs, ((∃ p, ownProgress pr p ∗
      ⌜PrKeptAt peers chg.LastIndex' k p ∧
        p.learner = decide (k ∈ s'.cfg.learners) ∧ p.witness = false⌝) ∗ emp :
        IProp GF)) $$ [H]
  · iapply (BigSepM2.bigSepM2_mono (fun {k pr pv} _ hpv => ?_)) $$ H
    iintro ⟨Hp, -, HQ⟩
    unfold newPrQC
    icases HQ with ⟨%p, Hinfl, %Hp⟩
    obtain ⟨Habs, Hm, Hpw⟩ := Hp
    isplitl
    · iexists p
      isplitl
      · iapply ownProgress_intro _ _ p $$ Hp Hinfl
        ipureintro; exact Habs
      · ipureintro
        exact ⟨Hm, ((progressAbs_Some _ _ _).1 Habs).1.symm.trans (Hlf k pv hpv), Hpw⟩
    · iempintro
  icases (BigSepM2.bigSepM2_sepM (Φ1 := fun k pr => iprop(∃ p, ownProgress (GF := GF) pr p ∗
      ⌜PrKeptAt peers chg.LastIndex' k p ∧
        p.learner = decide (k ∈ s'.cfg.learners) ∧ p.witness = false⌝))
    (Φ2 := fun (_ : w64) (_ : tracker.Progress) => (emp : IProp GF)) (m1 := prs) (m2 := pvs)
    Hdom0).1 $$ H with ⟨H, -⟩
  icases bigSepM_exist_sepM2 prs _ $$ H with ⟨%ps, H⟩
  ihave %Hdom2 := BigSepM2.bigSepM2_lookup_iff $$ H
  icases BigSepM2.bigSepM2_sep_eqv.1 $$ H with ⟨Hprogs, Hmk⟩
  ihave %Hmk := BigSepM2.bigSepM2_pure_intro $$ Hmk
  have Hdom2' : ∀ k, (prs !! k).isSome ↔ (ps !! k).isSome := Hdom2
  have Hflc : LearnerFlagsC s'.cfg ps := by
    intro k p hp
    obtain ⟨pr, hpr⟩ := Option.isSome_iff_exists.1 ((Hdom2' k).2 (by rw [hp]; rfl))
    exact (Hmk k pr p hpr hp).2.1
  have Htf : trkFlags ps = s'.prs := by
    apply GMap.map_eq; intro k
    rw [trkFlags_lookup]
    cases hp : ps !! k with
    | none =>
      have h1 : (prs !! k).isSome = false := by
        cases h : prs !! k with
        | none => rfl
        | some _ => have := (Hdom2' k).1 (by rw [h]; rfl); rw [hp] at this; cases this
      have h2 : k ∉ s'.prs := by
        rw [← Hflags, flagsOf_mem, ← Hdom k, h1]; simp
      rw [GMap.mem_iff] at h2
      cases h3 : s'.prs !! k with
      | none => rfl
      | some _ => rw [h3] at h2; exact absurd rfl h2
    | some p =>
      simp only [Option.map_some]
      obtain ⟨pr, hpr⟩ := Option.isSome_iff_exists.1 ((Hdom2' k).2 (by rw [hp]; rfl))
      obtain ⟨pv, hpv⟩ := Option.isSome_iff_exists.1 ((Hdom k).1 (by rw [hpr]; rfl))
      have h' := flagsOf_lookup pvs k pv hpv
      rw [Hflags] at h'
      rw [h', Hflc k p hp, ← Hlf k pv hpv]
  imod ownMap_persist $$ Htrk with #Htrk
  imodintro
  iexists prs, ps
  isplitl
  · unfold ownConfigC
    simp only [named]
    iframe Hc Htrk Hprogs
    ipureintro
    refine ⟨?_, Hpdom, Hflc, ?_, fun k p hp => ?_⟩
    · rw [Htf]; exact Hinv
    · rw [← GMap.size_dom, Hpdom]; exact Hsz
    · obtain ⟨pr, hpr⟩ := Option.isSome_iff_exists.1 ((Hdom2' k).2 (by rw [hp]; rfl))
      exact ⟨(Hmk k pr p hpr hp).2.2, ne0_of_dom (by rw [Hpdom]; exact H0) hpr⟩
  · ipureintro
    refine ⟨fun k p' hp' => ?_, fun k p' hp' => ?_, Hpdom⟩
    · obtain ⟨pr, hpr⟩ := Option.isSome_iff_exists.1 ((Hdom2' k).2 (by rw [hp']; rfl))
      exact (Hmk k pr p' hpr hp').1.matchKept
    · obtain ⟨pr, hpr⟩ := Option.isSome_iff_exists.1 ((Hdom2' k).2 (by rw [hp']; rfl))
      exact (Hmk k pr p' hpr hp').1

end heap

end EtcdGrove
end Perennial
