module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.encodeItems
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.encodeObj
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.rvBytes

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state labelSel fieldSel)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem encodeItems.wp_proof
    (wp_encodeObj : encodeObj.spec (GF := GF) (hG := hG))
    (wp_rvBytes : rvBytes.spec (GF := GF) (hG := hG)) :
    encodeItems.spec (GF := GF) (hG := hG) := by
  intro sl os
  wp_start as #Hs
  ihave %Hl := ownSlice_len $$ Hs
  wp_auto
  rename_i iu_ptr
  irename : (iu_ptr ↦ zero_val w64 : IProp GF) => Hiu
  ihave HI : (∃ (j k : w64) (out : GoSlice),
      "i" ∷ i_ptr ↦ j ∗ "Hiu" ∷ iu_ptr ↦ k ∗ "out" ∷ out_ptr ↦ out ∗
      "Ho" ∷ out ↦* encItemsL (os.take (sint.nat j)) ∗ "Hc" ∷ ownSliceCap w8 out (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len⌝ : IProp GF) $$ [i Hiu out]
  · iexists W64 0, _, slice.nil
    iframe
    isplitl
    · rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero,
        show encItemsL [] = [] from rfl]
      iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    · ipureintro; refine ⟨by word, by word⟩
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len :=
      ⟨Hj.1, Hif⟩
    list_elem os (sint.nat j) as o
    icases ownSlice_elem_acc (sint.Z j) o sl DFrac.discard _ Hj.1 Ho_lookup $$ Hs with ⟨#Hel, -⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z j) os DFrac.discard o Hj.1 $$ [Hs] as -
    · isplit
      · iexact Hs
      · ipureintro; exact Ho_lookup
    (try wp_auto)
    simp only [Hb', _root_.and_self, ↓reduceIte]
    wp_apply wp_encodeObj $$ [$Hel] as %e ⟨He, -⟩
    (try wp_auto)
    simp only [Hb', _root_.and_self, ↓reduceIte]
    iStructNamed Hel
    (try wp_auto)
    wp_apply wp_rvBytes
    (try wp_auto)
    wp_apply wp_string_to_bytes (rvBytes o.ResourceVersion') as %s1 ⟨Hs1, -⟩
    wp_apply wp_slice_append $$ [$Ho $Hc $Hs1] as %s2 ⟨Hs2, Hc2, -⟩
    (try wp_auto)
    ihave %Hel' := ownSlice_len $$ He
    (try wp_auto)
    wp_apply wp_rvBytes
    (try wp_auto)
    wp_apply wp_string_to_bytes as %s3 ⟨Hs3, -⟩
    wp_apply wp_slice_append $$ [$Hs2 $Hc2 $Hs3] as %s4 ⟨Hs4, Hc4, -⟩
    (try wp_auto)
    wp_apply wp_slice_append $$ [$Hs4 $Hc4 $He] as %s5 ⟨Hs5, Hc5, -⟩
    (try wp_auto)
    wp_for_post
    iframe
    iexists j + W64 1, j, s5
    iframe
    have hlen : e.len = W64 ((encodeWith tagV1 o).length : Int) := by have := Hel'; word
    have hcat : ∀ l, encItemsL (l ++ [o]) = encItemsL l ++ encItemL o := by
      intro l; simp [encItemsL, List.foldl_append]
    rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Ho_lookup,
      Option.toList_some, hcat]
    simp only [encItemL, hlen, List.append_assoc]
    iframe
    ipureintro; refine ⟨by word, by word⟩
  · (try wp_auto)
    wp_apply wp_bytes_to_string $$ [$Ho] as -
    (try wp_auto)
    have : os.take (sint.nat j) = os := List.take_of_length_le (by word)
    rw [this]
    iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
