/-
Proof of `Spec/confchange_Restore.lean`.

Until 2026-10-08 this file was `axiom confchange.Restore.wp_proof` (the Rocq
`proof_confchange_Restore.v`'s `Axiom`): the package was not translated. It is now
proved from its callees (`toConfChangeSingle`, the `chg.Simple(cc)` closures, `chain`),
in the voters-only case the spec states. The statement is unchanged.
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.Restore
public import Spec.go_etcd_io.raft.v3.confchange.toConfChangeSingle
public import Spec.go_etcd_io.raft.v3.confchange.Changer__Simple
public import Spec.go_etcd_io.raft.v3.confchange.chain

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `Simple([AddNode id])` on a voters-only tracker whose progress map tracks exactly the
voters, none of them a learner: `id` joins the voters, tracked as a non-learner. -/
theorem simpleM_addNode (vm : GMap w64 Unit) (fl : GMap w64 Bool) (al : Bool) (id : w64)
    (hid : id ≠ W64 0) (hdom : ∀ k, k ∈ fl ↔ k ∈ vm) :
    simpleM [addNodeCC id] ⟨⟨vm, ∅, ∅, ∅, al⟩, fl⟩ =
      some ⟨⟨<[id := ()]> vm, ∅, ∅, ∅, false⟩, <[id := false]> fl⟩ := by
  have Hinv0 : CfgInv (clearAutoLeave ⟨⟨vm, ∅, ∅, ∅, al⟩, fl⟩) := by
    refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun _ => ⟨rfl, rfl⟩⟩
    · simp only [clearAutoLeave.proj_cfg, clearAutoLeave.proj_prs] at hk ⊢
      rcases hk with hk | hk | hk | hk
      · exact (hdom k).2 hk
      all_goals simp [GMap.mem_iff] at hk
    · simp [clearAutoLeave, GMap.mem_iff] at hk
    · simp [clearAutoLeave, GMap.mem_iff] at hk
  have Hs1 : makeVoterM id (clearAutoLeave ⟨⟨vm, ∅, ∅, ∅, al⟩, fl⟩) =
      ⟨⟨<[id := ()]> vm, ∅, ∅, ∅, false⟩, <[id := false]> fl⟩ := by
    unfold makeVoterM
    split
    · simp [clearAutoLeave, GMap.delete_empty]
    · simp [clearAutoLeave, initProgressM]
  have Hne : (<[id := ()]> vm) ≠ ∅ := by
    intro h; have := congrArg (fun m => m !! id) h; simp at this
  have Happ : applyM [addNodeCC id] (clearAutoLeave ⟨⟨vm, ∅, ∅, ∅, al⟩, fl⟩) =
      some ⟨⟨<[id := ()]> vm, ∅, ∅, ∅, false⟩, <[id := false]> fl⟩ := by
    have hid' : (addNodeCC id).NodeId' ≠ W64 0 := hid
    simp only [applyM, applyAll, applyOne, if_neg hid',
      ↓reduceIte, Hs1, Option.bind_some,
      if_neg Hne]
  have Hsd : ¬ SymdiffTooBig vm (<[id := ()]> vm) := by
    unfold SymdiffTooBig symdiffN
    have h1 : vm \ (<[id := ()]> vm) = ∅ := by
      apply GMap.map_eq; intro k
      by_cases hk : id = k
      · subst hk; simp
      · rw [GMap.lookup_sdiff, GMap.lookup_insert_ne _ _ hk]
        rcases h : vm !! k with _ | v <;> simp
    have h2 : GMap.size ((<[id := ()]> vm) \ vm) ≤ 1 := by
      have hsub : (<[id := ()]> vm) \ vm ⊆ ({[id := ()]} : GMap w64 Unit) := by
        intro k v hkv
        by_cases hk : id = k
        · subst hk; cases v; simp
        · rw [GMap.lookup_sdiff, GMap.lookup_insert_ne _ _ hk] at hkv
          rcases h : vm !! k with _ | v' <;> simp_all
      have := GMap.map_subseteq_size hsub
      rw [GMap.map_size_singleton] at this
      exact this
    rw [h1, GMap.map_size_empty]
    generalize GMap.size ((<[id := ()]> vm) \ vm) = n at h2
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h2 with h0 | h0 <;> subst h0 <;> decide
  have Hinv1 : CfgInv ⟨⟨<[id := ()]> vm, ∅, ∅, ∅, false⟩, <[id := false]> fl⟩ := by
    refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun _ => ⟨rfl, rfl⟩⟩
    · dsimp only at hk ⊢
      rcases hk with hk | hk | hk | hk
      · rw [GMap.mem_iff] at hk ⊢
        by_cases h : id = k
        · subst h; simp
        · rw [GMap.lookup_insert_ne _ _ h] at hk ⊢
          exact (hdom k).2 hk
      all_goals simp [GMap.mem_iff] at hk
    · simp [GMap.mem_iff] at hk
    · simp [GMap.mem_iff] at hk
  unfold simpleM
  rw [if_neg (fun h => h Hinv0), Happ]
  simp only [clearAutoLeave.proj_cfg]
  rw [if_neg (by simp), if_neg Hsd]
  simp [checkedM, Hinv1]

/-- What `ownProgress` holds besides the points-to: the inflight ring, and that the value
is a non-learner `Progress` of the record. -/
def progR (pv : tracker.Progress) : IProp GF :=
  iprop(∃ pp : Progress, ownInflights pv.Inflights' pp.infl ∗ ⌜progressAbs pv pp.infl = some pp⌝)

/-- Name the values of a map of `ownProgress` objects. -/
theorem ownProgress_values (prs : GMap w64 Loc) :
    ([∗map] _k ↦ pr ∈ prs, ∃ pp, ownProgress pr pp) ⊢ ∃ pvs : GMap w64 tracker.Progress,
      ([∗map] _k ↦ pr;pv ∈ prs;pvs, (pr ↦ pv : IProp GF)) ∗ ([∗map] _k ↦ pv ∈ pvs, progR pv) ∗
      ⌜∀ k pv, pvs !! k = some pv → pv.IsLearner' = false⌝ ∗
      ⌜∀ k, (prs !! k).isSome ↔ (pvs !! k).isSome⌝ := by
  iintro H
  ihave H : ([∗map] k ↦ pr ∈ prs, ∃ pv : tracker.Progress,
      (pr ↦ pv ∗ (⌜pv.IsLearner' = false⌝ ∗ (emp ∗ progR pv)) : IProp GF)) $$ [H]
  · iapply (BigSepM.bigSepM_mono (fun {k pr} _ => ?_)) $$ H
    iintro ⟨%pp, Hp⟩
    unfold ownProgress
    iNamed Hp
    iexists pv
    iframe Hpv
    isplitr
    · ipureintro; exact ((progressAbs_Some _ _ _).1 Habs).1
    isplitr
    · iempintro
    unfold progR
    iexists pp
    iframe Hinfl
    ipureintro; exact Habs
  icases bigSepM_exist_sepM2 prs _ $$ H with ⟨%pvs, H⟩
  ihave %Hdom := BigSepM2.bigSepM2_lookup_iff $$ H
  have Hdom' : ∀ k, (prs !! k).isSome ↔ (pvs !! k).isSome := Hdom
  icases BigSepM2.bigSepM2_sep_eqv.1 $$ H with ⟨Hpt, H⟩
  icases BigSepM2.bigSepM2_sep_eqv.1 $$ H with ⟨Hl, H⟩
  ihave %Hlf := BigSepM2.bigSepM2_pure_intro $$ Hl
  icases (BigSepM2.bigSepM2_sepM (Φ1 := fun (_ : w64) (_ : Loc) => (emp : IProp GF))
    (Φ2 := fun (_ : w64) pv => progR (GF := GF) pv) Hdom).1 $$ H with ⟨-, HR⟩
  iexists pvs
  iframe Hpt HR
  ipureintro
  refine ⟨fun k pv h => ?_, Hdom'⟩
  obtain ⟨pr, hpr⟩ := Option.isSome_iff_exists.1 ((Hdom' k).2 (by rw [h]; rfl))
  exact Hlf k pr pv hpr h

/-- The other way: values with their rings and non-learner facts make `ownProgress`es. -/
theorem ownProgress_of_values (prs : GMap w64 Loc) (pvs : GMap w64 tracker.Progress)
    (Hdom : ∀ k, (prs !! k).isSome ↔ (pvs !! k).isSome)
    (Hl : ∀ k pv, pvs !! k = some pv → pv.IsLearner' = false) :
    ([∗map] _k ↦ pr;pv ∈ prs;pvs, (pr ↦ pv : IProp GF)) ∗
      ([∗map] _k ↦ pv ∈ pvs, (⌜pv.IsLearner' = false⌝ -∗ progR (GF := GF) pv)) ⊢
      [∗map] _k ↦ pr ∈ prs, ∃ pp, ownProgress pr pp := by
  iintro ⟨Hpt, HR⟩
  ihave HR := (BigSepM2.bigSepM2_sepM (Φ1 := fun (_ : w64) (_ : Loc) => (emp : IProp GF))
    (Φ2 := fun (_ : w64) pv => iprop(⌜pv.IsLearner' = false⌝ -∗ progR (GF := GF) pv))
    (m1 := prs) (m2 := pvs) Hdom).2
    $$ [HR]
  · isplitr
    · iapply (BigSepM.bigSepM_emp (m := prs)).2
      iempintro
    · iexact HR
  ihave H := BigSepM2.bigSepM2_sep_eqv.2 $$ [$Hpt $HR]
  ihave H : ([∗map] _k ↦ pr;pv ∈ prs;pvs, ((∃ pp, ownProgress pr pp) ∗ emp : IProp GF)) $$ [H]
  · iapply (BigSepM2.bigSepM2_mono (fun {k pr pv} _ hpv => ?_)) $$ H
    iintro ⟨Hp, -, HR⟩
    unfold progR
    icases HR $$ %(Hl k pv hpv) with ⟨%pp, Hinfl, %Habs⟩
    isplitl
    · iexists pp
      iapply ownProgress_intro _ _ pp $$ Hp Hinfl
      ipureintro; exact Habs
    · iempintro
  icases (BigSepM2.bigSepM2_sepM (Φ1 := fun (_ : w64) pr => iprop(∃ pp, ownProgress (GF := GF) pr pp))
    (Φ2 := fun (_ : w64) (_ : tracker.Progress) => (emp : IProp GF)) (m1 := prs) (m2 := pvs)
    Hdom).1 $$ H with ⟨H, -⟩
  iexact H

/-- The statement `Changer.Simple.spec` had until 2026-10-12, for `Restore`'s path:
`Simple([AddNode id])` with `id ≠ 0` on a voters-only tracker of non-learner `Progress`
objects; the tracker's objects are given up (the copies take their inflight rings). -/
abbrev Simple_votersOnly_spec : Prop :=
  ∀ (p : Loc) (chg : confchange.Changer) (ccs : GoSlice) (id : w64) (v : Loc)
    (vm : GMap w64 Unit) (prs : GMap w64 Loc) (dq dqc dqv dqp : DFrac),
  id ≠ W64 0 →
  GMap.size vm < 2 ^ 63 →
  ConfigVotersOnly chg.Tracker'.Config' v →
  domSet prs = domSet vm →
  (0 ≤ sint.Z chg.Tracker'.MaxInflight' ∧ sint.Z chg.Tracker'.MaxInflight' < 2 ^ 62) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dq} chg ∗
      ccs ↦*{dqc} [addNodeCC id] ∗
      v ↦${dqv} vm ∗ chg.Tracker'.Progress' ↦${dqp} prs ∗
      ([∗map] _k ↦ pr ∈ prs, ∃ pp, ownProgress pr pp) }}
    (App (Val (p @!! go.GoType.PointerType confchange.Changer.ty @!! go!"Simple")) (Val #ccs))
  {{ (cfg' : tracker.Config) (trk v' : Loc) (prs' : GMap w64 Loc),
      RET (PairV (PairV #cfg' #trk) #interface.nil);
      p ↦{dq} chg ∗ ccs ↦*{dqc} [addNodeCC id] ∗
      v ↦${dqv} vm ∗ chg.Tracker'.Progress' ↦${dqp} prs ∗
      ⌜ConfigSimple cfg' v'⌝ ∗ v' ↦$ (<[id := ()]> vm) ∗ trk ↦$ prs' ∗
      ⌜domSet prs' = domSet (<[id := ()]> vm)⌝ ∗
      ([∗map] _k ↦ pr ∈ prs', ∃ pp, ownProgress pr pp) }}

theorem Simple_votersOnly (H : confchange.Changer.Simple.spec (GF := GF) (hG := hG)) :
    Simple_votersOnly_spec (GF := GF) (hG := hG) := by
  intro p chg ccs id v vm prs dq dqc dqv dqp Hid Hsz Hcfg Hdom Hmi
  obtain ⟨Harr, Hl, Hln⟩ := Hcfg
  iintro %Φ ⟨#Hpkg, Hp, Hccs, Hv, Hpm, Hprogs⟩ HΦ
  icases ownProgress_values prs $$ Hprogs with ⟨%pvs, Hpt, HR, %Hlf, %Hdom2⟩
  have Hfl : ∀ k, k ∈ flagsOf pvs ↔ k ∈ vm := by
    intro k
    rw [flagsOf_mem, ← Hdom2]
    show k ∈ prs ↔ k ∈ vm
    rw [← GMap.elem_of_dom', Hdom, GMap.elem_of_dom']
  have Hs := simpleM_addNode vm (flagsOf pvs) chg.Tracker'.Config'.AutoLeave' id Hid Hfl
  ihave Htc : ownTrackerCC chg.Tracker' dqv dqp (DFrac.own 1)
      ⟨vm, ∅, ∅, ∅, chg.Tracker'.Config'.AutoLeave'⟩ prs pvs $$ [Hv Hpm Hpt]
  · unfold ownTrackerCC
    iframe Hpm Hpt
    iapply ownCfgCC_intro chg.Tracker'.Config' dqv
      (⟨vm, ∅, ∅, ∅, chg.Tracker'.Config'.AutoLeave'⟩ : CfgM) v map.nil Harr rfl $$ Hv [] [] []
    · unfold ownIdsetC; ileft; ipureintro; exact ⟨rfl, rfl⟩
    · rw [Hl]; unfold ownIdsetC; ileft; ipureintro; exact ⟨rfl, rfl⟩
    · rw [Hln]; unfold ownIdsetC; ileft; ipureintro; exact ⟨rfl, rfl⟩
  iapply H p chg _ prs pvs ccs [addNodeCC id] dq dqc dqv dqp (DFrac.own 1) Hmi
    $$ [$Hpkg $Hp $Hccs $Htc]
  inext
  iintro %cfg %trk %err ⟨Hp, Hccs, Htc, Hres⟩
  rw [Hs]
  simp only [ownResult]
  icases Hres with ⟨%Herr, Hc, Hw⟩
  subst Herr
  unfold ownTrackerCC
  icases Htc with ⟨Htcc, Hpm, -⟩
  icases ownCfgCC_elim _ _ _ $$ Htcc with ⟨%vin0, %vout0, %Harr0, Hv, -, -, -, -⟩
  have Hv0 : vin0 = v := by rw [Harr] at Harr0; injection Harr0 with h; exact h.symm
  subst Hv0
  icases ownCfgCC_elim _ _ _ $$ Hc with ⟨%vin, %vout, %Harr1, Hin, Hout, Hl1, Hln1, %Hal1⟩
  ihave %Hvout : ⌜vout = map.nil⌝ $$ [Hout]
  · unfold ownIdsetC
    icases Hout with (%H | ⟨-, %H⟩)
    · ipureintro; exact H.1
    · exact absurd rfl H
  ihave %Hl1' : ⌜cfg.Learners' = map.nil⌝ $$ [Hl1]
  · unfold ownIdsetC
    icases Hl1 with (%H | ⟨-, %H⟩)
    · ipureintro; exact H.1
    · exact absurd rfl H
  ihave %Hln1' : ⌜cfg.LearnersNext' = map.nil⌝ $$ [Hln1]
  · unfold ownIdsetC
    icases Hln1 with (%H | ⟨-, %H⟩)
    · ipureintro; exact H.1
    · exact absurd rfl H
  unfold ownPrsW
  icases Hw with ⟨%prs0, %pvs0, Htrk, Hprs, %Hflags, Hnew⟩
  ihave %Hdom3' := BigSepM2.bigSepM2_lookup_iff $$ Hprs
  have Hdom3 : ∀ k, (prs0 !! k).isSome ↔ (pvs0 !! k).isSome := Hdom3'
  have Hlf2 : ∀ k pv, pvs0 !! k = some pv → pv.IsLearner' = false := by
    intro k pv h
    have h' := flagsOf_lookup pvs0 k pv h
    rw [Hflags] at h'
    by_cases hk : id = k
    · subst hk; simp at h'; exact h'
    · rw [GMap.lookup_insert_ne _ _ hk, flagsOf_lookup'] at h'
      cases h'' : pvs !! k with
      | none => rw [h''] at h'; cases h'
      | some pv' => rw [h''] at h'; simp at h'; rw [← h']; exact Hlf k pv' h''
  have Hcopy : ∀ (k : w64) (pv0 pv : tracker.Progress), pvs !! k = some pv0 →
      pv = { pv0 with IsLearner' := pv.IsLearner' } →
      progR (GF := GF) pv0 ⊢ iprop(⌜pv.IsLearner' = false⌝ -∗ progR (GF := GF) pv) := by
    intro k pv0 pv h0 h1
    unfold progR
    iintro ⟨%pp, Hinfl, %Habs⟩ %Hl2
    have hl0 : pv0.IsLearner' = false := ((progressAbs_Some _ _ _).1 Habs).1
    have hpv : pv = pv0 := by rw [h1, Hl2, ← hl0]
    subst hpv
    iexists pp
    iframe Hinfl
    ipureintro; exact Habs
  have Hfresh : ∀ (k : w64) (pv : tracker.Progress), FreshPr chg pv →
      ownInflights (GF := GF) pv.Inflights' (inflightsNew chg.Tracker'.MaxInflight'
        chg.Tracker'.MaxInflightBytes') ⊢
      iprop(⌜pv.IsLearner' = false⌝ -∗ progR (GF := GF) pv) := by
    intro k pv Hf
    unfold progR
    iintro Hinfl %Hl2
    iexists progressOf pv .probe (inflightsNew chg.Tracker'.MaxInflight'
      chg.Tracker'.MaxInflightBytes')
    simp only [progressOf]
    iframe Hinfl
    ipureintro
    exact (progressAbs_Some _ _ _).2 ⟨Hl2, Hf.2.2.2.1, rfl, rfl, rfl, rfl, rfl, rfl⟩
  ihave HQ := ownNewPr_transfer chg pvs (fun _ pv => progR (GF := GF) pv)
    (fun _ pv => iprop(⌜pv.IsLearner' = false⌝ -∗ progR (GF := GF) pv)) Hcopy Hfresh pvs0
    $$ [$HR $Hnew]
  iapply HΦ
  iframe Hp Hccs Hv Hpm Hin Htrk
  isplitr
  · ipureintro
    exact ⟨⟨by rw [Harr1, Hvout], Hl1', Hln1'⟩, Hal1⟩
  isplitr
  · ipureintro
    apply GMap.set_eq; intro k
    rw [GMap.elem_of_dom', GMap.elem_of_dom', GMap.mem_iff, Hdom3, ← flagsOf_mem, Hflags]
    by_cases hk : id = k
    · subst hk; simp [GMap.mem_iff]
    · rw [GMap.mem_iff, GMap.mem_iff, GMap.lookup_insert_ne _ _ hk, GMap.lookup_insert_ne _ _ hk]
      exact Hfl k
  iapply ownProgress_of_values prs0 pvs0 Hdom3 Hlf2 $$ [$Hprs $HQ]

/-- The invariant `chain` threads through `Restore`'s ops: before op `j`, the pair is
either the empty configuration `Restore` started from (`j = 0`), or a fresh voters-only
config holding the first `j` voters, with a progress for each (`0 < j`).
`MakeProgressTracker`'s own voter map `v0` is only read and comes back. -/
def restoreInv (chg : confchange.Changer) (v0 : Loc) (voters : List w64)
    (j : Nat) (cfg : tracker.Config) (prs : Loc) : IProp GF :=
  iprop(v0 ↦$ (∅ : GMap w64 Unit) ∗
    (⌜j = 0 ∧ cfg = chg.Tracker'.Config' ∧ prs = chg.Tracker'.Progress'⌝ ∨
     (∃ (v : Loc) (vm : GMap w64 Unit) (prs' : GMap w64 Loc),
       ⌜0 < j⌝ ∗ ⌜ConfigSimple cfg v⌝ ∗ v ↦$ vm ∗ prs ↦$ prs' ∗
       ⌜domSet prs' = domSet vm ∧ domSet vm = GMap.listToSet (voters.take j) ∧
         GMap.size vm ≤ j⌝ ∗
       ([∗map] _k ↦ pr ∈ prs', ∃ pp, ownProgress pr pp))))

theorem confchange.Restore.wp_proof
    (wp_confchange_toConfChangeSingle : confchange.toConfChangeSingle.spec (GF := GF) (hG := hG))
    (wp_Changer_Simple : confchange.Changer.Simple.spec (GF := GF) (hG := hG))
    (wp_confchange_chain : confchange.chain.spec (GF := GF) (hG := hG)) :
    confchange.Restore.spec (GF := GF) (hG := hG) := by
  have wp_Changer_Simple := Simple_votersOnly wp_Changer_Simple
  intro chg cs voters dq v0 Hvne Hv0n Hcvo Hcl Hcln Hmi Harr Hl Hln
  wp_start as ⟨Hvs, Hv0, #Hpm⟩
  wp_auto
  wp_apply wp_confchange_toConfChangeSingle _ voters _ Hcvo Hcl Hcln $$ [$Hvs]
    as %ins ⟨Hvs, Hins, Hinscap⟩
  ihave %Hvlen := ownSlice_len $$ Hvs
  ihave %Hinslen := ownSlice_len $$ Hins
  ihave Hnil : (slice.nil ↦* ([] : List GoFunc)) $$ []
  · iapply ownSlice_nil
  ihave Hcap : ownSliceCap GoFunc slice.nil (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  -- `for _, cc := range incoming { cc := cc; ops = append(ops, func(chg) {chg.Simple(cc)}) }`:
  -- after `n` iterations, `ops` holds `n` closures, the `j`th taking the pair from
  -- `restoreInv j` to `restoreInv (j + 1)` (op `j` adds voter `j`)
  ihave IH : iprop(∃ (n : w64) (ops' : GoSlice) (fs : List GoFunc) (x : raftpb.ConfChangeSingle),
      "i" ∷ i_ptr ↦ n ∗
      "ops" ∷ ops_ptr ↦ ops' ∗
      "Hcc" ∷ cc_ptr ↦ x ∗
      "Hops" ∷ ops' ↦* fs ∗
      "Hopscap" ∷ ownSliceCap GoFunc ops' (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (voters.length : Int) ∧ fs.length = sint.nat n⌝ ∗
      "#Hfs" ∷ □ (∀ (j : Nat) (f : GoFunc), ⌜fs[j]? = some f⌝ -∗
        opSpec f chg (restoreInv chg v0 voters j) (restoreInv chg v0 voters (j + 1))))
    $$ [i ops cc Hnil Hcap]
  · iexists W64 0, slice.nil, [], zero_val raftpb.ConfChangeSingle
    simp only [named]
    iframe i ops cc Hnil Hcap
    isplitr
    · ipureintro; exact ⟨by decide, by word, rfl⟩
    imodintro
    iintro %j %f %Hjf
    simp at Hjf
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < voters.length := by
      have := Hinslen.1; rw [List.length_map] at this; word
    obtain ⟨idn, Hidn⟩ : ∃ x, voters[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ins.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd', _root_.and_self]
    wp_apply wp_load_slice_index ins (sint.Z n) _ _ (addNodeCC idn) Hn.1 $$ [Hins] with Hins
    · iframe Hins; ipureintro; rw [List.getElem?_map, Hidn]; rfl
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
    iframe HΦ Hv0 chg Hvs Hins Hinscap
    iexists n + W64 1, ops2, _, addNodeCC idn
    simp only [named]
    iframe i ops Hcc Hops Hopscap
    have Hidn0 : idn ≠ W64 0 := fun h => Hv0n (h ▸ List.mem_of_getElem? Hidn)
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
    -- `func(chg Changer) { return chg.Simple(cc) }`: `Simple([AddNode idn])` on the
    -- pair in `chg`'s tracker, from `restoreInv fs.length` to `restoreInv (fs.length + 1)`
    unfold opSpec
    iintro %cfg %prs
    wp_start_folded as HI
    wp_auto
    wp_apply wp_slice_literal (V := raftpb.ConfChangeSingle) [addNodeCC idn]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    have Htake : voters.take (fs.length + 1) = voters.take fs.length ++ [idn] := by
      rw [List.take_add_one, Hfslen, Hidn]; rfl
    unfold restoreInv
    icases HI with ⟨Hv0, (⟨%Hj0, %Hcfg, %Hprs⟩ | ⟨%v, %vm, %prs', %Hpos, %Hcs, Hv, Hprs, %Hd, Hprogs⟩)⟩
    · -- op 0: from the empty configuration `Restore` started from
      subst Hcfg Hprs
      have Hcv : ConfigVotersOnly chg.Tracker'.Config' v0 := ⟨Harr, Hl, Hln⟩
      wp_apply wp_Changer_Simple _ _ _ idn v0 ∅ ∅ _ _ _ _ Hidn0
        (by rw [GMap.map_size_empty]; decide) Hcv rfl Hmi $$ [$chg $Hsl2 $Hv0 $Hpm]
        as %cfg' %trk %v' %prs'' ⟨chg, Hsl2, Hv0, -, %Hcs', Hv', Htrk, %Hd', Hprogs'⟩
      · iapply BigSepM.bigSepM_empty.2; iempintro
      iapply HΦ
      iframe Hv0
      iright
      iexists v', <[idn := ()]> ∅, prs''
      iframe Hv' Htrk Hprogs'
      ipureintro
      refine ⟨by omega, Hcs', Hd', ?_, ?_⟩
      · have Hv0' : voters[0]? = some idn := (Hfslen.symm.trans Hj0) ▸ Hidn
        rw [Hj0]
        show (<[idn := ()]> ∅).domSet = listToSet (List.take (0 + 1) voters)
        simp only [List.take_succ, List.take_zero, Hv0', Option.toList_some, List.nil_append,
          GMap.listToSet_cons, GMap.listToSet_nil, GMap.dom_insert, GMap.dom_empty]
      · rw [GMap.map_size_insert_None _ _ _ (by rfl), GMap.map_size_empty]; omega
    · -- op `fs.length > 0`: from the configuration the previous op built
      have Hsz : GMap.size vm < 2 ^ 63 := by
        have := Hd.2.2
        have h2 := Hvlen.1
        word
      wp_apply wp_Changer_Simple _
        ({ chg with Tracker' := { chg.Tracker' with Config' := cfg, Progress' := prs } } :
          confchange.Changer)
        _ idn v vm prs' _ _ _ _ Hidn0 Hsz Hcs.1 Hd.1 Hmi
        $$ [$chg $Hsl2 $Hv $Hprs $Hprogs]
        as %cfg' %trk %v' %prs'' ⟨chg, Hsl2, -, -, %Hcs', Hv', Htrk, %Hd', Hprogs'⟩
      iapply HΦ
      iframe Hv0
      iright
      iexists v', <[idn := ()]> vm, prs''
      iframe Hv' Htrk Hprogs'
      ipureintro
      refine ⟨by omega, Hcs', Hd', ?_, ?_⟩
      · rw [Htake, GMap.listToSet_app, GMap.listToSet_cons, GMap.listToSet_nil, ← Hd.2.1,
          GMap.dom_insert]
        apply GMap.set_eq; intro k
        simp only [GMap.elem_of_union, GMap.elem_of_singleton, GMap.elem_of_empty, or_false]
        exact Or.comm
      · rcases h : vm !! idn with _ | ⟨⟩
        · rw [GMap.map_size_insert_None _ _ _ h]; omega
        · rw [GMap.insert_id _ _ _ h]; omega
  · -- the loop is over: `chain(chg, ops...)`
    have Hn' : sint.nat n = voters.length := by
      have := Hinslen.1; rw [List.length_map] at this; word
    ihave HI0 : restoreInv chg v0 voters 0 chg.Tracker'.Config' chg.Tracker'.Progress' $$ [Hv0]
    · unfold restoreInv
      iframe Hv0
      ileft
      ipureintro; exact ⟨rfl, rfl, rfl⟩
    wp_apply wp_confchange_chain chg ops' fs _ (restoreInv chg v0 voters) $$ [$Hops $HI0 $Hfs]
      as %cfg %prs ⟨Hops, HI⟩
    unfold restoreInv
    icases HI with ⟨Hv0, (⟨%Hj0, -, -⟩ | ⟨%v, %vm, %prs', %Hpos, %Hcs, Hv, Hprs, %Hd, Hprogs⟩)⟩
    · exfalso
      rw [Hn.2.2, Hn'] at Hj0
      exact Hvne (List.eq_nil_of_length_eq_zero Hj0)
    iapply HΦ
    iframe Hvs Hv0 Hpm Hv Hprs Hprogs
    ipureintro
    rw [Hn.2.2, Hn', List.take_length] at Hd
    exact ⟨⟨Hcs.1.1, Hcs.1.2.1, Hcs.1.2.2, Hcs.2⟩, Hd.2.1, Hd.1.trans Hd.2.1⟩

end proof

end EtcdGrove
end Perennial
