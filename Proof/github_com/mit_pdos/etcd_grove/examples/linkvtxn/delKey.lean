/-
Lean-first (no Rocq counterpart).

The proof of `delKey`: the loop's invariant is that `out` holds the entries before the index
without `k`'s.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.delKey

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkvtxn

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

theorem delKey.wp_proof : delKey.spec (GF := GF) (hG := hG) := by
  intro sl es dq k
  wp_start as Hs
  ihave %Hl := ownSlice_len $$ Hs
  wp_auto
  wp_apply wp_slice_make3 (V := entry) (W64 0) sl.len ⟨by word, by word⟩
    as %o0 ⟨Ho, Hocap, -⟩
  rw [List.replicate_zero]
  ihave HI : (∃ (j : w64) (e0 : entry) (o : GoSlice),
      "i" ∷ i_ptr ↦ j ∗ "e" ∷ e_ptr ↦ e0 ∗ "out" ∷ out_ptr ↦ o ∗
      "Ho" ∷ o ↦* delKeyL (es.take (sint.nat j)) k ∗
      "Hocap" ∷ ownSliceCap entry o (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len⌝ : IProp GF) $$ [i e out Ho Hocap]
  · iexists W64 0, _, o0
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    iframe
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, Hif⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem es (sint.nat j) as x
    wp_apply wp_load_slice_index sl (sint.Z j) es dq x Hj.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hx_lookup
    have Htake : delKeyL (es.take (sint.nat (j + W64 1))) k =
        delKeyL (es.take (sint.nat j)) k ++ delKeyL [x] k := by
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Hx_lookup]
      simp [delKeyL, List.filter_append]
    wp_if_destruct
    · wp_for_post
      iframe
      iexists j + W64 1, _, o
      have : delKeyL [x] x.key' = [] := by simp [delKeyL]
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
      have : delKeyL [x] k = [x] := by simp [delKeyL, Hif]
      rw [Htake, this]
      iframe
      ipureintro; word
  · have hall : es.take (sint.nat j) = es := List.take_of_length_le (by word)
    rw [hall]
    iapply HΦ
    iframe

end proof

end linkvtxn
end EtcdGrove
end Perennial
