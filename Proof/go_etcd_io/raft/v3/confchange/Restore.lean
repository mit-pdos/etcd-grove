/-
Proof of `Spec/confchange_Restore.lean`.

Until 2026-10-08 this file was `axiom confchange.Restore.wp_proof` (the Rocq
`proof_confchange_Restore.v`'s `Axiom`): the package was not translated. It is now
proved from its callees (`toConfChangeSingle`, the `chg.Simple(cc)` closures, `chain`).
Since 2026-10-13 (reconfiguration stage L) for a non-joint `ConfState` with learners: each
op is a `Simple` step on `cfgState V L` (`simpleM_cfgState_addNode`/`_addLearner`,
`InvApplyConf.lean`), the configuration held as `ownCfgSt`.
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.Restore
public import Spec.go_etcd_io.raft.v3.confchange.toConfChangeSingle
public import Spec.go_etcd_io.raft.v3.confchange.Changer__Simple
public import Spec.go_etcd_io.raft.v3.confchange.chain
public import Proof.go_etcd_io.raft.v3.InvApplyConf

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

/-- What `ownProgress` holds besides the points-to: the inflight ring, and that the value
is a `Progress` of the record (a learner's or not, as the value says). -/
def progR2 (pv : tracker.Progress) : IProp GF :=
  iprop(∃ pp : Progress, ownInflights pv.Inflights' pp.infl ∗ ⌜progressAbs pv pp.infl = some pp⌝)

/-- A configuration `Restore` has built so far, as a `Changer` step leaves it: the voters
`V` and the learners `L` (`cfgM V L`), the progress map at `prsm` with its `Progress`
objects, each id's `IsLearner` as `cfgFlags V L` says. -/
def ownCfgSt (cfg : tracker.Config) (prsm : Loc) (V L : GSet w64) : IProp GF :=
  iprop(∃ (prs : GMap w64 Loc) (pvs : GMap w64 tracker.Progress),
    ownCfgCC cfg (DFrac.own 1) (cfgM V L) ∗ prsm ↦$ prs ∗
    ([∗map] _k ↦ pr;pv ∈ prs;pvs, pr ↦ pv) ∗ ([∗map] _k ↦ pv ∈ pvs, progR2 pv) ∗
    ⌜flagsOf pvs = cfgFlags V L⌝)

/-- A `Changer` step's result, its new `Progress` objects given the rings of the old ones
(copies) or their own (fresh). -/
theorem ownCfgSt_of_result (chg : confchange.Changer) (base : GMap w64 tracker.Progress)
    (cfg : tracker.Config) (trk : Loc) (V L : GSet w64) :
    ownCfgCC (GF := GF) cfg (DFrac.own 1) (cfgM V L) ∗ ownPrsW chg base trk (cfgFlags V L) ∗
      ([∗map] _k ↦ pv ∈ base, progR2 pv) ⊢ ownCfgSt cfg trk V L := by
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
    obtain ⟨_, h2, h3, h4, h5, h6, h7, h8⟩ := (progressAbs_Some _ _ _).1 Habs
    refine (progressAbs_Some _ _ _).2 ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, h8⟩ <;>
      (rw [h1]; assumption)
  · intro k pv Hf
    unfold progR2
    iintro Hinfl
    iexists progressOf pv .probe (inflightsNew chg.Tracker'.MaxInflight'
      chg.Tracker'.MaxInflightBytes')
    isplitl [Hinfl]
    · simp only [progressOf]; iexact Hinfl
    ipureintro
    exact (progressAbs_Some _ _ _).2 ⟨rfl, Hf.2.2.2.1, rfl, rfl, rfl, rfl, rfl, rfl⟩
  unfold ownCfgSt
  iexists prs, pvs
  iframe Hc Htrk Hprs HQ
  ipureintro; exact Hflags

/-- `chg.Simple(ccs)` on a tracker holding `ownCfgSt V L`, for a change the model answers
with `cfgState V' L'`: the result holds `ownCfgSt V' L'`; the old configuration and progress
map come back (garbage once `chain` moves on). -/
theorem wp_Simple_cfgSt (H : confchange.Changer.Simple.spec (GF := GF) (hG := hG))
    (p : Loc) (chg : confchange.Changer) (ccs : GoSlice) (l : List raftpb.ConfChangeSingle)
    (V L V' L' : GSet w64) (dq dqs : DFrac)
    (Hmi : 0 ≤ sint.Z chg.Tracker'.MaxInflight' ∧ sint.Z chg.Tracker'.MaxInflight' < 2 ^ 62)
    (Hm : simpleM l (cfgState V L) = some (cfgState V' L')) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dq} chg ∗
        ccs ↦*{dqs} l ∗ ownCfgSt chg.Tracker'.Config' chg.Tracker'.Progress' V L }}
      (App (Val (p @!! go.GoType.PointerType confchange.Changer.ty @!! go!"Simple")) (Val #ccs))
    {{ (cfg : tracker.Config) (trk : Loc), RET (PairV (PairV #cfg #trk) #interface.nil);
        p ↦{dq} chg ∗ ccs ↦*{dqs} l ∗ ownCfgSt cfg trk V' L' }} := by
  iintro %Φ ⟨#Hpkg, Hp, Hccs, Hst⟩ HΦ
  unfold ownCfgSt
  icases Hst with ⟨%prs, %pvs, Hc, Hpm, Hpt, HR, %Hfl⟩
  ihave Htc : ownTrackerCC chg.Tracker' (DFrac.own 1) (DFrac.own 1) (DFrac.own 1)
      (cfgM V L) prs pvs $$ [Hc Hpm Hpt]
  · unfold ownTrackerCC
    iframe
  iapply H p chg (cfgM V L) prs pvs ccs l dq dqs (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) Hmi
    $$ [$Hpkg $Hp $Hccs $Htc]
  inext
  iintro %cfg %trk %err ⟨Hp, Hccs, -, Hres⟩
  rw [show ({ cfg := cfgM V L, prs := flagsOf pvs } : CCState) = cfgState V L by
    rw [Hfl]; rfl, Hm]
  simp only [ownResult]
  icases Hres with ⟨%Herr, Hc, Hw⟩
  subst Herr
  ihave Hc := (show ownCfgCC (GF := GF) cfg (DFrac.own 1) (cfgState V' L').cfg ⊢
    ownCfgCC cfg (DFrac.own 1) (cfgM V' L') from .rfl) $$ Hc
  ihave Hw := (show ownPrsW (GF := GF) chg pvs trk (cfgState V' L').prs ⊢
    ownPrsW chg pvs trk (cfgFlags V' L') from .rfl) $$ Hw
  ihave Hst := ownCfgSt_of_result chg pvs cfg trk V' L' $$ [$Hc $Hw $HR]
  iapply HΦ
  iframe Hp Hccs
  iunfold ownCfgSt at Hst
  iexact Hst

/-- The same from the empty tracker `MakeProgressTracker` built: its voter map `v0` and its
(read-only) progress map come back. -/
theorem wp_Simple_empty (H : confchange.Changer.Simple.spec (GF := GF) (hG := hG))
    (p : Loc) (chg : confchange.Changer) (ccs : GoSlice) (l : List raftpb.ConfChangeSingle)
    (v0 : Loc) (V' L' : GSet w64) (dq dqs : DFrac)
    (Hmi : 0 ≤ sint.Z chg.Tracker'.MaxInflight' ∧ sint.Z chg.Tracker'.MaxInflight' < 2 ^ 62)
    (Harr : chg.Tracker'.Config'.Voters'.arr = [v0, map.nil])
    (Hl : chg.Tracker'.Config'.Learners' = map.nil)
    (Hln : chg.Tracker'.Config'.LearnersNext' = map.nil)
    (Hal : chg.Tracker'.Config'.AutoLeave' = false)
    (Hm : simpleM l (cfgState ∅ ∅) = some (cfgState V' L')) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dq} chg ∗
        ccs ↦*{dqs} l ∗ v0 ↦$ (∅ : GMap w64 Unit) ∗
        chg.Tracker'.Progress' ↦$□ (∅ : GMap w64 Loc) }}
      (App (Val (p @!! go.GoType.PointerType confchange.Changer.ty @!! go!"Simple")) (Val #ccs))
    {{ (cfg : tracker.Config) (trk : Loc), RET (PairV (PairV #cfg #trk) #interface.nil);
        p ↦{dq} chg ∗ ccs ↦*{dqs} l ∗ v0 ↦$ (∅ : GMap w64 Unit) ∗
        ownCfgSt cfg trk V' L' }} := by
  iintro %Φ ⟨#Hpkg, Hp, Hccs, Hv0, #Hpm⟩ HΦ
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
  iapply H p chg (cfgM ∅ ∅) ∅ ∅ ccs l dq dqs (DFrac.own 1) DFrac.discard (DFrac.own 1) Hmi
    $$ [$Hpkg $Hp $Hccs $Htc]
  inext
  iintro %cfg %trk %err ⟨Hp, Hccs, Htc, Hres⟩
  have Hf0 : flagsOf (∅ : GMap w64 tracker.Progress) = cfgFlags ∅ ∅ := by
    apply GMap.map_eq; intro k
    rw [cfgFlags_lookup, if_neg (GMap.not_elem_of_empty _), if_neg (GMap.not_elem_of_empty _)]
    rfl
  rw [show ({ cfg := cfgM ∅ ∅, prs := flagsOf (∅ : GMap w64 tracker.Progress) } : CCState) =
      cfgState ∅ ∅ by rw [Hf0]; rfl, Hm]
  simp only [ownResult]
  icases Hres with ⟨%Herr, Hc, Hw⟩
  subst Herr
  ihave Hc := (show ownCfgCC (GF := GF) cfg (DFrac.own 1) (cfgState V' L').cfg ⊢
    ownCfgCC cfg (DFrac.own 1) (cfgM V' L') from .rfl) $$ Hc
  ihave Hw := (show ownPrsW (GF := GF) chg ∅ trk (cfgState V' L').prs ⊢
    ownPrsW chg ∅ trk (cfgFlags V' L') from .rfl) $$ Hw
  unfold ownTrackerCC
  icases Htc with ⟨Htcc, -, -⟩
  icases ownCfgCC_elim _ _ _ $$ Htcc with ⟨%vin0, %vout0, %Harr0, Hv0, -, -, -, -⟩
  have Hv0' : vin0 = v0 := by rw [Harr] at Harr0; injection Harr0 with h; exact h.symm
  subst Hv0'
  ihave HR0 : ([∗map] _k ↦ pv ∈ (∅ : GMap w64 tracker.Progress), progR2 (GF := GF) pv) $$ []
  · iapply BigSepM.bigSepM_empty.2; iempintro
  ihave Hst := ownCfgSt_of_result chg ∅ cfg trk V' L' $$ [$Hc $Hw $HR0]
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

/-- The invariant `chain` threads through `Restore`'s ops: before op `j`, the pair is
either the empty configuration `Restore` started from (`j = 0`), or the configuration of
the first `j` ops: the voters among them and the learners after them (`0 < j`).
`MakeProgressTracker`'s own voter map `v0` is only read and comes back. -/
def restoreInv (chg : confchange.Changer) (v0 : Loc) (voters learners : List w64)
    (j : Nat) (cfg : tracker.Config) (prs : Loc) : IProp GF :=
  iprop(v0 ↦$ (∅ : GMap w64 Unit) ∗
    (⌜j = 0 ∧ cfg = chg.Tracker'.Config' ∧ prs = chg.Tracker'.Progress'⌝ ∨
     (⌜0 < j⌝ ∗ ownCfgSt cfg prs (GMap.listToSet (voters.take j))
        (GMap.listToSet (learners.take (j - voters.length))))))

theorem listToSet_snoc (l : List w64) (x : w64) :
    GMap.listToSet (l ++ [x]) = (<[x := ()]> (GMap.listToSet l) : GSet w64) := by
  apply GMap.set_eq; intro k
  rw [GMap.elem_of_list_to_set, gset_mem_insert, GMap.elem_of_list_to_set]
  simp only [List.mem_append, List.mem_singleton]
  exact Or.comm

theorem confchange.Restore.wp_proof
    (wp_confchange_toConfChangeSingle : confchange.toConfChangeSingle.spec (GF := GF) (hG := hG))
    (wp_Changer_Simple : confchange.Changer.Simple.spec (GF := GF) (hG := hG))
    (wp_confchange_chain : confchange.chain.spec (GF := GF) (hG := hG)) :
    confchange.Restore.spec (GF := GF) (hG := hG) := by
  intro chg cs voters learners dq dql v0 Hvne Hv0n Hl0n Hdis Hcvo Hcln Hmi Harr Hl Hln Hal
  wp_start as ⟨Hvs, Hls, Hv0, #Hpm⟩
  wp_auto
  wp_apply wp_confchange_toConfChangeSingle _ voters learners _ _ Hcvo Hcln $$ [$Hvs $Hls]
    as %ins ⟨Hvs, Hls, Hins, Hinscap⟩
  ihave %Hinslen := ownSlice_len $$ Hins
  ihave Hnil : (slice.nil ↦* ([] : List GoFunc)) $$ []
  · iapply ownSlice_nil
  ihave Hcap : ownSliceCap GoFunc slice.nil (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  have Hlen : (voters.map addNodeCC ++ learners.map addLearnerCC).length =
      voters.length + learners.length := by simp
  -- `for _, cc := range incoming { cc := cc; ops = append(ops, func(chg) {chg.Simple(cc)}) }`:
  -- after `n` iterations, `ops` holds `n` closures, the `j`th taking the pair from
  -- `restoreInv j` to `restoreInv (j + 1)` (op `j` adds voter `j`, or learner
  -- `j - |voters|`)
  ihave IH : iprop(∃ (n : w64) (ops' : GoSlice) (fs : List GoFunc) (x : raftpb.ConfChangeSingle),
      "i" ∷ i_ptr ↦ n ∗
      "ops" ∷ ops_ptr ↦ ops' ∗
      "Hcc" ∷ cc_ptr ↦ x ∗
      "Hops" ∷ ops' ↦* fs ∗
      "Hopscap" ∷ ownSliceCap GoFunc ops' (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ ((voters.length + learners.length : Nat) : Int) ∧
        fs.length = sint.nat n⌝ ∗
      "#Hfs" ∷ □ (∀ (j : Nat) (f : GoFunc), ⌜fs[j]? = some f⌝ -∗
        opSpec f chg (restoreInv chg v0 voters learners j)
          (restoreInv chg v0 voters learners (j + 1))))
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
  · have Hlt : sint.nat n < voters.length + learners.length := by
      have := Hinslen.1; rw [Hlen] at this; word
    obtain ⟨c, Hc⟩ : ∃ c, (voters.map addNodeCC ++ learners.map addLearnerCC)[sint.nat n]? =
        some c := ⟨_, List.getElem?_eq_getElem (by rw [Hlen]; exact Hlt)⟩
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ins.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd', _root_.and_self]
    wp_apply wp_load_slice_index ins (sint.Z n) _ _ c Hn.1 $$ [Hins] with Hins
    · iframe Hins; ipureintro; exact Hc
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
    iframe HΦ Hv0 chg Hvs Hls Hins Hinscap
    iexists n + W64 1, ops2, _, c
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
    -- `func(chg Changer) { return chg.Simple(cc) }`: `Simple([c])` on the pair in `chg`'s
    -- tracker, from `restoreInv fs.length` to `restoreInv (fs.length + 1)`
    unfold opSpec
    iintro %cfg %prs
    wp_start_folded as HI
    wp_auto
    wp_apply wp_slice_literal (V := raftpb.ConfChangeSingle) [c]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    -- the model step: a voter, or a learner
    rw [← Hfslen] at Hc
    have Hstep : ∀ (V L : GSet w64), V = GMap.listToSet (voters.take fs.length) →
        L = GMap.listToSet (learners.take (fs.length - voters.length)) →
        simpleM [c] (cfgState V L) = some (cfgState
          (GMap.listToSet (voters.take (fs.length + 1)))
          (GMap.listToSet (learners.take (fs.length + 1 - voters.length)))) := by
      intro V L HV HL
      rcases Nat.lt_or_ge fs.length voters.length with Hv | Hv
      · -- a voter
        rw [List.getElem?_append_left (by simpa using Hv), List.getElem?_map] at Hc
        obtain ⟨x, Hx, rfl⟩ := Option.map_eq_some_iff.1 Hc
        have hx0 : x ≠ W64 0 := fun h => Hv0n (h ▸ List.mem_of_getElem? Hx)
        have hL : L = ∅ := by
          rw [HL, show fs.length - voters.length = 0 by omega, List.take_zero]; rfl
        have hL' : fs.length + 1 - voters.length = 0 := by omega
        rw [hL', List.take_zero, List.take_add_one, Hx, Option.toList_some, listToSet_snoc,
          ← HV, show GMap.listToSet ([] : List w64) = ∅ from rfl, ← hL]
        apply simpleM_cfgState_addNode V L x hx0
        · rw [hL]; exact GMap.not_elem_of_empty _
        · intro k hk; rw [hL] at hk; exact absurd hk (GMap.not_elem_of_empty _)
      · -- a learner
        have Hk : fs.length - voters.length < learners.length := by omega
        rw [List.getElem?_append_right (by simpa using Hv), List.getElem?_map,
          List.length_map] at Hc
        obtain ⟨x, Hx, rfl⟩ := Option.map_eq_some_iff.1 Hc
        have hx0 : x ≠ W64 0 := fun h => Hl0n (h ▸ List.mem_of_getElem? Hx)
        have hxv : x ∉ voters := Hdis x (List.mem_of_getElem? Hx)
        have HV' : V = GMap.listToSet voters := by
          rw [HV, List.take_of_length_le Hv]
        have e1 : GMap.listToSet (voters.take (fs.length + 1)) = V := by
          rw [HV', List.take_of_length_le (by omega)]
        have e2 : GMap.listToSet (learners.take (fs.length + 1 - voters.length)) =
            (<[x := ()]> L : GSet w64) := by
          rw [show fs.length + 1 - voters.length = fs.length - voters.length + 1 by omega,
            List.take_add_one, Hx, Option.toList_some, listToSet_snoc, ← HL]
        rw [e1, e2]
        apply simpleM_cfgState_addLearner V L x hx0
        · rw [HV', GMap.elem_of_list_to_set]; exact hxv
        · rw [HV']; intro h
          apply Hvne
          cases voters with
          | nil => rfl
          | cons y ys =>
            have : y ∈ GMap.listToSet (y :: ys) := (GMap.elem_of_list_to_set _ _).2 (by simp)
            rw [h] at this; exact absurd this (GMap.not_elem_of_empty _)
        · intro k hk
          rw [HL, GMap.elem_of_list_to_set] at hk
          rw [HV', GMap.elem_of_list_to_set]
          exact Hdis k (List.mem_of_mem_take hk)
    unfold restoreInv
    icases HI with ⟨Hv0, (⟨%Hj0, %Hcfg, %Hprs⟩ | ⟨%Hpos, Hst⟩)⟩
    · -- op 0: from the empty configuration `Restore` started from
      subst Hcfg Hprs
      have Hm := Hstep ∅ ∅ (by rw [Hj0, List.take_zero]; rfl)
        (by rw [Hj0, Nat.zero_sub, List.take_zero]; rfl)
      wp_apply wp_Simple_empty wp_Changer_Simple _ _ _ _ v0 _ _ _ _ Hmi Harr Hl Hln Hal Hm
        $$ [$chg $Hsl2 $Hv0 $Hpm] as %cfg' %trk ⟨chg, Hsl2, Hv0, Hst⟩
      iapply HΦ
      iframe Hv0
      iright
      iframe Hst
      ipureintro; omega
    · -- op `fs.length > 0`: from the configuration the previous op built
      have Hm := Hstep _ _ rfl rfl
      wp_apply wp_Simple_cfgSt wp_Changer_Simple _
        ({ chg with Tracker' := { chg.Tracker' with Config' := cfg, Progress' := prs } } :
          confchange.Changer) _ _ _ _ _ _ _ _ Hmi Hm
        $$ [$chg $Hsl2 $Hst] as %cfg' %trk ⟨chg, Hsl2, Hst⟩
      iapply HΦ
      iframe Hv0
      iright
      iframe Hst
      ipureintro; omega
  · -- the loop is over: `chain(chg, ops...)`
    have Hn' : sint.nat n = voters.length + learners.length := by
      have := Hinslen.1; rw [Hlen] at this; word
    ihave HI0 : restoreInv chg v0 voters learners 0 chg.Tracker'.Config' chg.Tracker'.Progress'
        $$ [Hv0]
    · unfold restoreInv
      iframe Hv0
      ileft
      ipureintro; exact ⟨rfl, rfl, rfl⟩
    wp_apply wp_confchange_chain chg ops' fs _ (restoreInv chg v0 voters learners)
        $$ [$Hops $HI0 $Hfs] as %cfg %prs ⟨Hops, HI⟩
    unfold restoreInv
    icases HI with ⟨Hv0, (⟨%Hj0, -, -⟩ | ⟨%Hpos, Hst⟩)⟩
    · exfalso
      rw [Hn.2.2, Hn'] at Hj0
      apply Hvne
      exact List.eq_nil_of_length_eq_zero (by omega)
    rw [Hn.2.2, Hn', List.take_of_length_le (by omega),
      show voters.length + learners.length - voters.length = learners.length by omega,
      List.take_length]
    unfold ownCfgSt
    icases Hst with ⟨%prs', %pvs, Hc, Hprsm, Hpt, HR, %Hfl⟩
    icases ownCfgCC_elim _ _ _ $$ Hc with ⟨%vin, %vout, %Harr1, Hin, Hout, Hl1, Hln1, %Hal1⟩
    icases ownIdsetC_nil_of _ _ (cfgM _ _).outgoing rfl $$ Hout with %Hvout
    icases ownIdsetC_nil_of _ _ (cfgM _ _).learnersNext rfl $$ Hln1 with %Hln1'
    ihave %Hdom := BigSepM2.bigSepM2_lookup_iff $$ Hpt
    have Hdom' : ∀ k, (prs' !! k).isSome ↔ (pvs !! k).isSome := Hdom
    ihave Hprogs := progs_of_values prs' pvs
      (fun k b => b = decide (k ∉ GMap.listToSet voters)) Hdom' ?_ $$ [$Hpt $HR]
    · intro k pv hpv
      have h' := flagsOf_lookup pvs k pv hpv
      rw [Hfl, cfgFlags_lookup] at h'
      by_cases hv : k ∈ GMap.listToSet voters
      · rw [if_pos hv] at h'; rw [← Option.some.inj h']; simp [hv]
      · rw [if_neg hv] at h'
        by_cases hl : k ∈ GMap.listToSet learners
        · rw [if_pos hl] at h'; rw [← Option.some.inj h']; simp [hv]
        · rw [if_neg hl] at h'; cases h'
    iapply HΦ
    iframe Hvs Hls Hv0 Hpm Hprsm Hprogs
    isplitr
    · ipureintro
      refine ⟨by rw [Harr1, Hvout], Hln1', Hal1⟩
    ihave Hl1 := (show ownIdsetC (GF := GF) cfg.Learners' (DFrac.own 1)
      (cfgM (GMap.listToSet voters) (GMap.listToSet learners)).learners ⊢
      ownIdsetC cfg.Learners' (DFrac.own 1) (GMap.listToSet learners) from .rfl) $$ Hl1
    iframe Hl1
    iframe Hin
    ipureintro
    refine ⟨domSet_gset _, ?_⟩
    apply GMap.set_eq; intro k
    rw [GMap.elem_of_dom', GMap.mem_iff, Hdom' k, ← flagsOf_mem, Hfl, cfgFlags_mem,
      GMap.elem_of_union]

end proof

end EtcdGrove
end Perennial
