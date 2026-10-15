/-
`tracker.ProgressTracker.LearnerNodes`, Lean-first.
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__LearnerNodes
public import Spec.slices.Sort

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

/-- As `VoterNodes`: `make([]uint64, 0, len(m))`, a `for range` appending each key
(`wp_idset_for_range`, the loop invariant that `nodes` holds the first `i` keys), and
`slices.Sort`; before it, the empty set returns `nil`. -/
theorem tracker.ProgressTracker.LearnerNodes.wp_proof
    (wp_slices_Sort : slices.«Sort».spec (GF := GF) (hG := hG)) :
    tracker.ProgressTracker.LearnerNodes.spec (GF := GF) (hG := hG) := by
  intro trk dq tv dql ls Hsize
  wp_start as ⟨Htrk, Hl⟩
  icases (Access.access
      (A := trk.[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Learners"] ↦{dq}
        tv.Config'.Learners')
      (A' := trk.[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Learners"] ↦{dq}
        tv.Config'.Learners')
      (P := trk ↦{dq} tv)) $$ Htrk with ⟨Hlf, Htrkback⟩
  wp_auto
  wp_apply wp_idset_len $$ Hl as ⟨Hl, %Hlt⟩
  ihave Hcapnil : ownSliceCap w64 slice.nil (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  ihave Hnil : (slice.nil ↦* ([] : List w64)) $$ []
  · iapply ownSlice_nil
  wp_if_destruct
  · -- no learners: `nil`
    have Hls : ls = ∅ := GMap.map_size_empty_inv _ (by word)
    subst Hls
    ihave Htrk := Htrkback $$ Hlf
    iapply HΦ
    iframe
    ipureintro
    have He : GMap.elements (∅ : GMap w64 Unit) = [] :=
      List.eq_nil_of_length_eq_zero (by rw [GMap.length_elements, GMap.size_empty])
    rw [He]
    exact ⟨List.Perm.refl _, by simp, fun _ => rfl⟩
  · iclear Hcapnil Hnil
    wp_apply wp_idset_len $$ Hl as ⟨Hl, -⟩
    wp_apply wp_slice_make3 (V := w64) (t := go.uint64) (W64 0) (W64 (GMap.size ls))
      (by word) as %sl ⟨Hsl, Hsl_cap, %Hslcap⟩
    simp only [List.replicate_zero]
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_idset_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (sl' : GoSlice) (x : w64),
        "%Hi" ∷ ⌜0 ≤ i⌝ ∗
        "nodes" ∷ nodes_ptr ↦ sl' ∗
        "Hsl" ∷ sl' ↦* keys.take i.toNat ∗
        "Hsl_cap" ∷ ownSliceCap w64 sl' (DFrac.own 1) ∗
        "id" ∷ id_ptr ↦ x)) $$ Hl
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [nodes Hsl Hsl_cap id]
    · iexists sl, zero_val w64
      simp only [Int.toNat_zero, List.take_zero]
      iframe
      ipureintro
      omega
    isplitr
    · imodintro
      iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
      iNamed HP
      wp_auto
      wp_apply wp_slice_literal (V := w64) [key]
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      wp_apply wp_slice_append $$ [$Hsl $Hsl_cap $Hsl2] as %sl3 ⟨Hsl, Hsl_cap, -⟩
      unfold forMapPostcondition
      iright
      ileft
      isplitr
      · ipureintro; rfl
      have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
        rw [show (i + 1).toNat = i.toNat + 1 by omega]
        rw [List.take_add_one, Hkey]; rfl
      iexists sl3, key
      rw [Htake]
      iframe
      ipureintro
      omega
    iintro HP Hl
    iNamed HP
    rw [← Hklen, Int.toNat_natCast, List.take_length]
    wp_auto
    wp_apply wp_slices_Sort $$ [$Hsl] as %xs ⟨Hsl, %Hxs, %Hsorted⟩
    · ipureintro; omega
    ihave Htrk := Htrkback $$ Hlf
    iapply HΦ
    iframe
    ipureintro
    refine ⟨Hxs.symm.trans ((List.perm_ext_iff_of_nodup Hknodup (GMap.NoDup_elements ls)).2 ?_),
      Hsorted, ?_⟩
    · intro k
      rw [Hkset, GMap.elem_of_elements, GMap.mem_iff]
    · intro Hls
      subst Hls
      exact absurd (by rw [GMap.map_size_empty]; rfl) Hif

end proof

end EtcdGrove
end Perennial
