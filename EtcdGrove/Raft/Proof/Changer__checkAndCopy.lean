/-
Proof of `Spec/Changer__checkAndCopy.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Raft.Spec.Changer__checkAndCopy
import EtcdGrove.Raft.Spec.Config__Clone
import EtcdGrove.Raft.Spec.confchange_checkAndReturn

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
  intro p chg v vm prs dq dqv dqp Hcfg Hdom
  wp_start as ⟨Hp, Hv, Hpm, Hprogs⟩
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
  wp_apply wp_Config_Clone _ _ v vm _ _ Hcfg $$ [$Hf $Hv] as %cfg' %v' ⟨Hf, Hv, %Hcfg', Hv'⟩
  ihave c := Hback $$ Hf
  -- `trk := tracker.ProgressMap{}`: a `make`
  wp_apply wp_map_make1 (K := w64) (V := Loc) as %trkm Htrk
  -- `for id, pr := range c.Tracker.Progress { ppr := *pr; trk[id] = &ppr }`. Each copy
  -- takes the original's inflight ring, so the invariant marks the originals copied so
  -- far (`keys.take i`) as no longer owned.
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (x : w64) (y : Loc)
      (prs' : GMap w64 Loc),
      "id" ∷ id_ptr ↦ x ∗
      "pr" ∷ pr_ptr ↦ y ∗
      "trk" ∷ trk_ptr ↦ trkm ∗
      "Htrk" ∷ trkm ↦$ prs' ∗
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "%Hdom'" ∷ ⌜∀ k, k ∈ domSet prs' ↔ k ∈ keys.take i.toNat⌝ ∗
      "Hcopies" ∷ ([∗map] _k ↦ pr ∈ prs', ∃ pp, ownProgress pr pp) ∗
      "Horig" ∷ ([∗map] k ↦ pr ∈ prs, ⌜k ∈ keys.take i.toNat⌝ ∨ ∃ pp, ownProgress pr pp)))
    $$ Hpm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [id pr trk Htrk Hprogs]
  · iexists zero_val w64, zero_val Loc, ∅
    simp only [named, Int.toNat_zero, List.take_zero]
    iframe id pr trk Htrk
    isplitr
    · ipureintro; exact Int.le_refl _
    isplitr
    · ipureintro
      intro k
      simp only [List.not_mem_nil, iff_false]
      rw [GMap.elem_of_dom]
      rintro ⟨v, hv⟩
      simp at hv
    isplitl []
    · iapply BigSepM.bigSepM_empty.2; iempintro
    have Hmono : ∀ (k : w64) (pr : Loc),
        (iprop(∃ pp, ownProgress pr pp) : IProp GF) ⊢
          iprop(⌜k ∈ ([] : List w64)⌝ ∨ ∃ pp, ownProgress pr pp) := by
      intro k pr; iintro H; iright; iexact H
    iapply (BigSepM.bigSepM_mono (fun {k pr} _ => Hmono k pr)) $$ Hprogs
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    -- the original at `key`, still owned
    icases (BigSepM.bigSepM_delete (m := prs) Hvv).1 $$ Horig with ⟨Hk, Horig⟩
    icases Hk with (%Hin | ⟨%pp, Hpr⟩)
    · exact absurd Hin (not_mem_take_of_nodup Hknodup Hkey)
    iNamed Hpr
    wp_auto
    wp_apply wp_mapInsert $$ Htrk as Htrk
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega]
      rw [List.take_add_one, Hkey]; rfl
    have Hnew : prs' !! key = none := by
      rw [← GMap.not_elem_of_dom, Hdom']
      exact not_mem_take_of_nodup Hknodup Hkey
    iexists key, vv, _
    simp only [named]
    iframe id pr trk Htrk
    isplitr
    · ipureintro; omega
    isplitr
    · ipureintro
      intro k
      rw [GMap.dom_insert, GMap.elem_of_union, GMap.elem_of_singleton, Hdom', Htake,
        List.mem_append, List.mem_singleton]
      constructor
      · rintro (h | h); exact .inr h; exact .inl h
      · rintro (h | h); exact .inr h; exact .inl h
    isplitl [Hcopies ppr Hinfl]
    · iapply (BigSepM.bigSepM_insert (Φ := fun _ pr => iprop(∃ pp, ownProgress pr pp)) (m := prs')
        Hnew).2
      iframe Hcopies
      iexists pp
      iapply ownProgress_intro _ _ pp $$ ppr Hinfl
      ipureintro; exact Habs
    iapply (BigSepM.bigSepM_delete (m := prs) Hvv).2
    isplitl []
    · ileft; ipureintro; rw [Htake]; exact List.mem_append_right _ (List.mem_singleton.2 rfl)
    have Hmono : ∀ (k : w64) (pr : Loc),
        (iprop(⌜k ∈ keys.take i.toNat⌝ ∨ ∃ pp, ownProgress pr pp) : IProp GF) ⊢
          iprop(⌜k ∈ keys.take (i + 1).toNat⌝ ∨ ∃ pp, ownProgress pr pp) := by
      intro k pr
      iintro (%Hin | H)
      · ileft; ipureintro; rw [Htake]; exact List.mem_append_left _ Hin
      · iright; iexact H
    iapply (BigSepM.bigSepM_mono (fun {k pr} _ => Hmono k pr)) $$ Horig
  iintro HP Hpm
  iNamed HP
  rw [Int.toNat_natCast, ← Hklen, List.take_length] at Hdom'
  have Hdom'' : domSet prs' = domSet vm := by
    rw [← Hdom]
    apply GMap.set_eq; intro k
    rw [Hdom', Hkset]
    exact (GMap.elem_of_dom' _ _).symm
  -- `checkAndReturn(cfg, trk)`
  wp_auto
  wp_apply wp_confchange_checkAndReturn _ _ v' vm prs' _ _ Hcfg' Hdom'' $$ [$Hv' $Htrk]
    as ⟨Hv', Htrk⟩
  iapply HΦ
  iframe
  ipureintro
  exact ⟨Hcfg', Hdom''⟩

end proof

end EtcdGrove
end Perennial
