/- Port of election_proof/proof_ProgressTracker__ConfState.v. -/
import EtcdGrove.Raft.Spec.ProgressTracker__ConfState
import EtcdGrove.Raft.Spec.MajorityConfig__Slice

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- A permutation of the elements of an empty set is empty. -/
private theorem perm_elements_empty (xs : List w64)
    (H : xs ≡ₚ elements (domSet (∅ : GMap w64 Unit))) : xs = [] := by
  have := H.length_eq
  rw [GMap.length_elements, GMap.dom_empty_L, GMap.size_empty] at this
  exact List.eq_nil_of_length_eq_zero this

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem tracker.ProgressTracker.ConfState.wp_proof
    (wp_MajorityConfig_Slice : quorum.MajorityConfig.Slice.spec (GF := GF) (hG := hG)) :
    tracker.ProgressTracker.ConfState.spec (GF := GF) (hG := hG) := by
  intro cfg trk tv t
  obtain ⟨votes, prs, pvs⟩ := t
  wp_start as ⟨Htrk, Hown⟩
  iNamed Hown
  wp_auto
  -- `Voters[0].Slice()`: the receiver is a pointer into the tracker's `JointConfig`
  -- array. Split the array field out of `trk ↦ tv` and element 0 out of the array.
  icases (Access.access
      (A := trk.[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Voters"] ↦
        tv.Config'.Voters')
      (A' := trk.[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Voters"] ↦
        tv.Config'.Voters')
      (P := trk ↦ tv)) $$ Htrk with ⟨Hvf, Htrkback⟩
  icases array_acc _ (sint.Z (W64 0)) _ _ _ voters_ref (by decide) (by rw [Hvoters_arr]; rfl)
    $$ Hvf with ⟨Hc0, Hcback⟩
  wp_method_call
  wp_call
  wp_auto
  -- `Slice`'s postcondition gives back an `ownIdsetOpt`, whose `map.nil` disjunct we
  -- refute with the voter map's own points-to
  ihave %Hvoters_nn := ownMap_not_nil $$ Hvoters
  wp_apply wp_MajorityConfig_Slice _ voters $$ [Hvoters] as %sl0 %xs0 ⟨Hvoters, Hsl0, -, %Hxs0⟩
  · isplitl
    · unfold ownIdsetOpt; iright; iexact Hvoters
    · ipureintro; rw [← GMap.size_dom, Hvoters_dom]; exact Hcfg_size
  ihave Hvf := Hcback $$ Hc0
  -- element 1, the nil outgoing config
  icases array_acc _ (sint.Z (W64 1)) _ _ _ map.nil (by decide) (by rw [Hvoters_arr]; rfl)
    $$ Hvf with ⟨Hc1, Hcback⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_MajorityConfig_Slice map.nil ∅ $$ [] as %sl1 %xs1 ⟨-, Hsl1, -, %Hxs1⟩
  · isplitl
    · unfold ownIdsetOpt; ileft; ipureintro; exact ⟨rfl, rfl⟩
    · ipureintro; simp [GMap.size_empty]
  ihave Hvf := Hcback $$ Hc1
  have Harr : array.mk 2 ((tv.Config'.Voters'.arr.set (sint.Z (W64 0)).toNat voters_ref).set
      (sint.Z (W64 1)).toNat map.nil) = tv.Config'.Voters' := by
    generalize tv.Config'.Voters' = a at Hvoters_arr ⊢
    cases a
    simp only at Hvoters_arr
    subst Hvoters_arr
    rfl
  rw [Harr]
  ihave Htrk := Htrkback $$ Hvf
  wp_auto
  obtain ⟨rfl, rfl⟩ := Hno_learners
  wp_apply wp_MajorityConfig_Slice $$ [$Hlearners] as %sl2 %xs2 ⟨Hlearners, Hsl2, -, %Hxs2⟩
  · ipureintro; simp [GMap.size_empty]
  wp_apply wp_MajorityConfig_Slice $$ [$HlearnersNext]
    as %sl3 %xs3 ⟨HlearnersNext, Hsl3, -, %Hxs3⟩
  · ipureintro; simp [GMap.size_empty]
  obtain rfl := perm_elements_empty xs1 Hxs1
  obtain rfl := perm_elements_empty xs2 Hxs2
  obtain rfl := perm_elements_empty xs3 Hxs3
  ihave %Hl1 := ownSlice_len $$ Hsl1
  ihave %Hl2 := ownSlice_len $$ Hsl2
  ihave %Hl3 := ownSlice_len $$ Hsl3
  ihave Hvoters : iprop(⌜voters_ref = map.nil ∧ voters = ∅⌝ ∨ voters_ref ↦$ voters) $$ [Hvoters]
  · unfold ownIdsetOpt; iexact Hvoters
  icases Hvoters with (⟨%Hvn, %Hve⟩ | Hvoters)
  · exact absurd Hvn Hvoters_nn
  iapply HΦ
  iframe Htrk Hsl0
  isplitl [Hvotes Hprogs Hvoters Hlearners HlearnersNext]
  · iapply ownTracker_intro (Hprs_dom := Hprs_dom) (Hvoters_arr := Hvoters_arr)
      (Hautoleave := Hautoleave) (Hvoters_dom := Hvoters_dom) (Hno_learners := ⟨rfl, rfl⟩)
      (Hcfg_size := Hcfg_size) (HmaxInfl := HmaxInfl) $$ Hvotes Hprs Hprogs Hvoters Hlearners
      HlearnersNext
  ipureintro
  refine ⟨Hvoters_dom ▸ Hxs0, ?_, ?_, ?_, Hautoleave⟩
  · simp at Hl1; word
  · simp at Hl2; word
  · simp at Hl3; word

end proof

end EtcdGrove
end Perennial
