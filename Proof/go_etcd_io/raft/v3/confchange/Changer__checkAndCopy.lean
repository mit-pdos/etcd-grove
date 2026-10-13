/-
Proof of `Spec/go_etcd_io/raft/v3/confchange/Changer__checkAndCopy.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.Changer__checkAndCopy
public import Spec.go_etcd_io.raft.v3.tracker.Config__Clone
public import Spec.go_etcd_io.raft.v3.confchange.checkAndReturn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem confchange.Changer.checkAndCopy.wp_proof
    (wp_Config_Clone : tracker.Config.Clone.spec (GF := GF) (hG := hG))
    (wp_confchange_checkAndReturn : confchange.checkAndReturn.spec (GF := GF) (hG := hG)) :
    confchange.Changer.checkAndCopy.spec (GF := GF) (hG := hG) := by
  intro p chg c prs pvs dq dqc dqm dqp
  wp_start as ⟨Hp, Htc⟩
  unfold ownTrackerCC
  icases Htc with ⟨Hc, Hpm, Hprs⟩
  ihave %Hdom0 := BigSepM2.bigSepM2_lookup_iff $$ Hprs
  have Hdom : ∀ k, (prs !! k).isSome ↔ (pvs !! k).isSome := Hdom0
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  -- `cfg := c.Tracker.Config.Clone()`: the field of the local copy, and back
  icases (Access.access
    (A := iprop((c_ptr.[confchange.Changer, go!"Tracker"]).[tracker.ProgressTracker, go!"Config"] ↦
      chg.Tracker'.Config'))
    (A' := iprop((c_ptr.[confchange.Changer, go!"Tracker"]).[tracker.ProgressTracker, go!"Config"] ↦
      chg.Tracker'.Config'))
    (P := iprop(c_ptr ↦ chg))) $$ c with ⟨Hf, Hback⟩
  wp_apply wp_Config_Clone _ _ c _ dqc $$ [$Hf $Hc] as %cfg' ⟨Hf, Hc, Hc'⟩
  ihave c := Hback $$ Hf
  -- `trk := tracker.ProgressMap{}`: a `make`
  wp_apply wp_map_make1 (K := w64) (V := Loc) as %trkm Htrk
  -- `for id, pr := range c.Tracker.Progress { ppr := *pr; trk[id] = &ppr }`: after `i`
  -- keys, the copy map holds a fresh copy of each of them
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (x : w64) (y : Loc)
      (prs' : GMap w64 Loc) (pvs' : GMap w64 tracker.Progress),
      "id" ∷ id_ptr ↦ x ∗
      "pr" ∷ pr_ptr ↦ y ∗
      "trk" ∷ trk_ptr ↦ trkm ∗
      "Htrk" ∷ trkm ↦$ prs' ∗
      "Hprs" ∷ ([∗map] _k ↦ pr;pv ∈ prs;pvs, pr ↦{dqp} pv) ∗
      "Hcopies" ∷ ([∗map] _k ↦ pr;pv ∈ prs';pvs', pr ↦ pv) ∗
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "%Hpart" ∷ ⌜∀ k, pvs' !! k = if k ∈ keys.take i.toNat then pvs !! k else none⌝))
    $$ Hpm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [id pr trk Htrk Hprs]
  · iexists zero_val w64, zero_val Loc, ∅, ∅
    iframe id pr trk Htrk Hprs
    isplitl []
    · iapply (BigSepM2.bigSepM2_empty _).2; iempintro
    ipureintro
    refine ⟨Int.le_refl _, fun k => ?_⟩
    simp
  isplitr
  · imodintro
    iintro %i %key %pr ⟨%Hkey, %Hpr⟩ HP
    iNamed HP
    obtain ⟨pv, Hpv⟩ : ∃ pv, pvs !! key = some pv :=
      Option.isSome_iff_exists.1 ((Hdom key).1 (by rw [Hpr]; rfl))
    have Hnew : key ∉ keys.take i.toNat := not_mem_take_of_nodup Hknodup Hkey
    icases (BigSepM2.bigSepM2_lookup_acc Hpr Hpv) $$ Hprs with ⟨Hp1, Hprback⟩
    wp_auto
    ihave Hprs := Hprback $$ Hp1
    wp_apply wp_mapInsert $$ Htrk as Htrk
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    ihave %Hcdom0 := BigSepM2.bigSepM2_lookup_iff $$ Hcopies
    have Hpv'none : pvs' !! key = none := by rw [Hpart, if_neg Hnew]
    have Hprs'none : prs' !! key = none := by
      have h := (Hcdom0 key)
      change (prs' !! key).isSome = true ↔ (pvs' !! key).isSome = true at h
      rw [Hpv'none] at h
      cases h' : prs' !! key with
      | none => rfl
      | some _ => rw [h'] at h; simp at h
    iexists key, pr, _, <[key := pv]> pvs'
    iframe id pr trk Htrk Hprs
    isplitl [Hcopies ppr]
    · iapply (BigSepM2.bigSepM2_insert Hprs'none Hpv'none).2
      iframe
    ipureintro
    refine ⟨by omega, fun k => ?_⟩
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
    rw [Htake]
    by_cases hk : k = key
    · subst hk
      rw [GMap.lookup_insert_eq, if_pos (List.mem_append_right _ (List.mem_singleton.2 rfl)), Hpv]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), Hpart]
      simp only [List.mem_append, List.mem_singleton, hk, or_false]
  iintro HP Hpm
  iNamed HP
  have Hpvs' : pvs' = pvs := by
    apply GMap.map_eq; intro k
    rw [Hpart, Int.toNat_natCast, ← Hklen, List.take_length]
    by_cases hk : k ∈ keys
    · rw [if_pos hk]
    · rw [if_neg hk]
      have h1 : (prs !! k).isSome = false := by
        cases h : (prs !! k).isSome
        · rfl
        · exact absurd ((Hkset k).2 h) hk
      have h2 : (pvs !! k).isSome = false := by
        cases h : (pvs !! k).isSome
        · rfl
        · rw [← Hdom] at h; rw [h] at h1; cases h1
      cases h3 : pvs !! k with
      | none => rfl
      | some _ => rw [h3] at h2; cases h2
  subst Hpvs'
  -- `checkAndReturn(cfg, trk)`
  wp_auto
  wp_apply wp_confchange_checkAndReturn cfg' trkm _ prs' pvs' _ _ _ $$ [$Hc' $Htrk $Hcopies]
    as %cfg'' %trk'' %err ⟨Hc', Htrk, Hcopies, %Hres⟩
  iapply HΦ
  iframe Hp Hc Hpm Hprs
  rcases Hres with ⟨Hinv, Herr, rfl, rfl⟩ | ⟨Hinv, Herr⟩
  · iright
    iframe Hc'
    isplitr
    · ipureintro; exact ⟨Hinv, Herr⟩
    iexists prs'
    iframe
  · ileft
    ipureintro; exact ⟨Hinv, Herr⟩

end proof

end EtcdGrove
end Perennial
