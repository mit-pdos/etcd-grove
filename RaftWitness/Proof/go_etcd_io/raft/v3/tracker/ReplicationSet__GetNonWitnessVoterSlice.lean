/-
Proof of `Spec/go_etcd_io/raft/v3/tracker/ReplicationSet__GetNonWitnessVoterSlice.lean`.
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.ReplicationSet__GetNonWitnessVoterSlice

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

/-- The map's keys appended one by one (`wp_map_for_range`, as `MajorityConfig.Slice`); a nil
map is a pure step, leaving the empty literal. -/
theorem tracker.ReplicationSet.GetNonWitnessVoterSlice.wp_proof :
    tracker.ReplicationSet.GetNonWitnessVoterSlice.spec (GF := GF) (hG := hG) := by
  intro l rv m
  wp_start as ⟨#Hl, #Hm⟩
  icases ownRS_fields l rv m $$ [Hl Hm] with ⟨-, -, #Hn⟩
  · iframe Hl Hm
  iunfold ownRS at Hm
  icases Hm with ⟨-, Hm⟩
  iunfold ownScope at Hm
  icases Hm with (%Hnil | ⟨%ids, %Hids, #Hmap⟩)
  · obtain ⟨Hn0, Hs0⟩ := Hnil
    wp_auto
    wp_apply wp_slice_literal (V := w64) []
    isplitr
    · ipureintro; rfl
    iintro %sl0 ⟨Hsl0, Hcap0⟩
    wp_auto
    rw [Hn0]
    wp_func_lits
    wp_auto
    iapply HΦ
    iframe Hsl0 Hcap0
    ipureintro
    rw [Hs0]
    have : (∅ : GSet w64).elements = [] :=
      List.eq_nil_of_length_eq_zero (by rw [GMap.length_elements, GMap.size_empty])
    rw [this]
  · wp_auto
    wp_apply wp_slice_literal (V := w64) []
    isplitr
    · ipureintro; rfl
    iintro %sl0 ⟨Hsl0, Hcap0⟩
    wp_auto
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (sl' : GoSlice) (x : w64),
        "%Hi" ∷ ⌜0 ≤ i⌝ ∗
        "results" ∷ results_ptr ↦ sl' ∗
        "Hsl" ∷ sl' ↦* keys.take i.toNat ∗
        "Hsl_cap" ∷ ownSliceCap w64 sl' (DFrac.own 1) ∗
        "v" ∷ v_ptr ↦ x)) $$ Hmap
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [results v Hsl0 Hcap0]
    · iexists _, zero_val w64
      simp only [Int.toNat_zero, List.take_zero, named]
      iframe results v Hsl0 Hcap0
      ipureintro; omega
    isplitr
    · imodintro
      iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
      iNamed HP
      wp_auto
      wp_apply wp_slice_literal (V := w64) [key]
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      wp_auto
      wp_apply wp_slice_append (V := w64) _ _ _ _ _ $$ [$Hsl $Hsl_cap $Hsl2]
        as %sl3 ⟨Hsl, Hsl_cap, -⟩
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
        rw [show (i + 1).toNat = i.toNat + 1 by omega]
        rw [List.take_add_one, Hkey]; rfl
      iexists sl3, key
      rw [Htake]
      simp only [named]
      iframe results Hsl Hsl_cap v
      ipureintro; omega
    iintro HP -
    iNamed HP
    rw [show (GMap.size ids : Int).toNat = keys.length by omega, List.take_length]
    wp_auto
    iapply HΦ
    iframe Hsl Hsl_cap
    ipureintro
    rw [← Hids]
    refine (List.perm_ext_iff_of_nodup Hknodup (GMap.NoDup_elements _)).2 ?_
    intro k
    rw [GMap.elem_of_elements, GMap.elem_of_dom, Hkset, Option.isSome_iff_exists]

end proof

end EtcdGrove
end Perennial
