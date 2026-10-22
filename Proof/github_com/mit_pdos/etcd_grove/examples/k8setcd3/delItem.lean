module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.delItem

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

theorem delItem.wp_proof : delItem.spec (GF := GF) (hG := hG) := by
  intro sl its dq k
  wp_start as Hs
  ihave %Hl := ownSlice_len $$ Hs
  wp_auto
  wp_apply wp_slice_make3 (V := item) (W64 0) sl.len ⟨by word, by word⟩
    as %o0 ⟨Ho, Hocap, -⟩
  rw [List.replicate_zero]
  ihave HI : (∃ (j : w64) (e0 : item) (o : GoSlice),
      "i" ∷ i_ptr ↦ j ∗ "e" ∷ e_ptr ↦ e0 ∗ "out" ∷ out_ptr ↦ o ∗
      "Ho" ∷ o ↦* delItemL (its.take (sint.nat j)) k ∗
      "Hocap" ∷ ownSliceCap item o (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len⌝ : IProp GF) $$ [i e out Ho Hocap]
  · iexists W64 0, _, o0
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    iframe
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, Hif⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem its (sint.nat j) as x
    wp_apply wp_load_slice_index sl (sint.Z j) its dq x Hj.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hx_lookup
    have Htake : delItemL (its.take (sint.nat (j + W64 1))) k =
        delItemL (its.take (sint.nat j)) k ++ delItemL [x] k := by
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Hx_lookup]
      simp [delItemL, List.filter_append]
    wp_if_destruct
    · wp_for_post
      iframe
      iexists j + W64 1, _, o
      have : delItemL [x] x.key' = [] := by simp [delItemL]
      rw [Htake, this, List.append_nil]
      iframe
      ipureintro; word
    · wp_apply wp_slice_literal (l := [x])
      isplitr
      · ipureintro; rfl
      iintro %lsl ⟨Hl1, _⟩
      wp_apply wp_slice_append $$ [$Ho $Hocap $Hl1] as %o' ⟨Ho, Hocap, -⟩
      wp_for_post
      iframe
      iexists j + W64 1, _, o'
      have : delItemL [x] k = [x] := by simp [delItemL, Hif]
      rw [Htake, this]
      iframe
      ipureintro; word
  · have hall : its.take (sint.nat j) = its := List.take_of_length_le (by word)
    rw [hall]
    iapply HΦ
    iframe

end proof

end k8setcd3
end EtcdGrove
end Perennial
