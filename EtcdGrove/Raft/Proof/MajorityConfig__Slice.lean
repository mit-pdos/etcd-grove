/- Port of election_proof/proof_MajorityConfig__Slice.v.

Lean notes: Perennial's `wp_map_for_range` hands the map's points-to back after the
loop, as Rocq's (`iIntros "HP Hm"`); the postcondition needs it (`ownIdsetOpt m ids`). -/
import EtcdGrove.Raft.Spec.MajorityConfig__Slice
import EtcdGrove.Raft.Spec.slices_Sort

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

theorem quorum.MajorityConfig.Slice.wp_proof
    (wp_slices_Sort : slices.«Sort».spec (GF := GF) (hG := hG)) :
    quorum.MajorityConfig.Slice.spec (GF := GF) (hG := hG) := by
  intro m ids
  wp_start as Hm
  wp_auto
  unfold ownIdsetOpt
  icases Hm with (%Hnil | Hm)
  · -- the nil set: the range is a pure step, and `sl` stays nil
    obtain ⟨rfl, rfl⟩ := Hnil
    wp_func_lits
    wp_auto
    ihave Hsl0 : (slice.nil ↦* ([] : List w64)) $$ []
    · iapply ownSlice_nil
    wp_apply wp_slices_Sort $$ [$Hsl0] as %xs ⟨Hsl, %Hxs, -⟩
    iapply HΦ
    iframe Hsl
    isplitl []
    · ileft; ipureintro; exact ⟨rfl, rfl⟩
    isplitl []
    · iapply ownSliceCap_nil
    ipureintro
    rw [GMap.dom_empty]
    have : (∅ : GSet w64).elements = [] :=
      List.eq_nil_of_length_eq_zero (by rw [GMap.length_elements, GMap.size_empty])
    rw [this]
    exact Hxs.symm
  · wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (sl' : GoSlice) (x : w64),
        "%Hi" ∷ ⌜0 ≤ i⌝ ∗
        "sl" ∷ sl_ptr ↦ sl' ∗
        "Hsl" ∷ sl' ↦* keys.take i.toNat ∗
        "Hsl_cap" ∷ ownSliceCap w64 sl' (DFrac.own 1) ∗
        "id" ∷ id_ptr ↦ x)) $$ Hm
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [sl id]
    · iexists slice.nil, zero_val w64
      simp only [Int.toNat_zero, List.take_zero, named]
      iframe sl id
      isplitl []
      · ipureintro; omega
      isplitl []
      · iapply ownSlice_nil
      · iapply ownSliceCap_nil
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
      iframe sl Hsl Hsl_cap id
      ipureintro; omega
    iintro HP Hm
    iNamed HP
    rw [show (GMap.size ids : Int).toNat = keys.length by omega, List.take_length]
    wp_auto
    wp_apply wp_slices_Sort $$ [$Hsl] as %xs ⟨Hsl, %Hxs, -⟩
    iapply HΦ
    iframe Hsl Hsl_cap
    isplitl [Hm]
    · iright; iexact Hm
    ipureintro
    refine Hxs.symm.trans ((List.perm_ext_iff_of_nodup Hknodup (GMap.NoDup_elements _)).2 ?_)
    intro k
    rw [GMap.elem_of_elements, GMap.elem_of_dom, Hkset, Option.isSome_iff_exists]

end proof

end EtcdGrove
end Perennial
