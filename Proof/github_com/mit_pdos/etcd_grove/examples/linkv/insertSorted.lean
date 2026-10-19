/-
Lean-first (no Rocq counterpart).

The proof of `insertSorted`: the loop's invariant is `insStep`'s fold over the entries before
the index (`out` and `done`); after it, `insFin`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.insertSorted
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.entryLess

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkv

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv.Assumptions]

theorem insertSorted.wp_proof (wp_entryLess : entryLess.spec (GF := GF) (hG := hG)) :
    insertSorted.spec (GF := GF) (hG := hG) := by
  intro sl es dq e
  wp_start as ⟨Hs, %Hb⟩
  ihave %Hl := ownSlice_len $$ Hs
  wp_auto
  wp_apply wp_slice_make3 (V := kvEntry) (W64 0) (sl.len + W64 1) ⟨by word, by word⟩
    as %o0 ⟨Ho, Hocap, -⟩
  rw [List.replicate_zero]
  ihave HI : (∃ (j : w64) (e0 : kvEntry) (o : GoSlice),
      "i" ∷ i_ptr ↦ j ∗ "x" ∷ x_ptr ↦ e0 ∗ "out" ∷ out_ptr ↦ o ∗
      "done" ∷ done_ptr ↦ ((es.take (sint.nat j)).foldl (insStep e) ([], false)).2 ∗
      "Ho" ∷ o ↦* ((es.take (sint.nat j)).foldl (insStep e) ([], false)).1 ∗
      "Hocap" ∷ ownSliceCap kvEntry o (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len⌝ : IProp GF) $$ [i x out done Ho Hocap]
  · iexists W64 0, _, o0
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.foldl_nil]
    iframe
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, Hif⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem es (sint.nat j) as x
    wp_apply wp_load_slice_index sl (sint.Z j) es dq x Hj.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hx_lookup
    have Htake : (es.take (sint.nat (j + W64 1))).foldl (insStep e) ([], false) =
        insStep e ((es.take (sint.nat j)).foldl (insStep e) ([], false)) x := by
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Hx_lookup]
      simp
    generalize (es.take (sint.nat j)).foldl (insStep e) ([], false) = st at Htake ⊢
    obtain ⟨o1, d⟩ := st
    simp only at Htake ⊢
    cases d
    · wp_auto
      wp_apply wp_entryLess x e
      cases hl : entryLessB x e
      · -- `!entryLess(x, e)`: insert `e` before `x`
        wp_auto
        wp_apply wp_slice_literal (l := [e])
        isplitr
        · ipureintro; rfl
        iintro %lsl ⟨Hl1, _⟩
        wp_apply wp_slice_append $$ [$Ho $Hocap $Hl1] as %o' ⟨Ho, Hocap, -⟩
        wp_apply wp_slice_literal (l := [x])
        isplitr
        · ipureintro; rfl
        iintro %lsl2 ⟨Hl2, _⟩
        wp_apply wp_slice_append $$ [$Ho $Hocap $Hl2] as %o'' ⟨Ho, Hocap, -⟩
        wp_for_post
        iframe
        iexists j + W64 1, _, o''
        rw [Htake, insStep, if_pos ⟨rfl, hl⟩]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
        iframe
        ipureintro; word
      · wp_auto
        wp_apply wp_slice_literal (l := [x])
        isplitr
        · ipureintro; rfl
        iintro %lsl ⟨Hl1, _⟩
        wp_apply wp_slice_append $$ [$Ho $Hocap $Hl1] as %o' ⟨Ho, Hocap, -⟩
        wp_for_post
        iframe
        iexists j + W64 1, _, o'
        rw [Htake, insStep, if_neg (fun h => Bool.noConfusion (hl.symm.trans h.2))]
        iframe
        ipureintro; word
    · wp_auto
      wp_apply wp_slice_literal (l := [x])
      isplitr
      · ipureintro; rfl
      iintro %lsl ⟨Hl1, _⟩
      wp_apply wp_slice_append $$ [$Ho $Hocap $Hl1] as %o' ⟨Ho, Hocap, -⟩
      wp_for_post
      iframe
      iexists j + W64 1, _, o'
      rw [Htake, insStep, if_neg (fun h => Bool.noConfusion h.1)]
      iframe
      ipureintro; word
  · -- the end: `insFin`
    have hall : es.take (sint.nat j) = es := List.take_of_length_le (by word)
    rw [hall]
    have hins : insertSortedL es e = insFin e (es.foldl (insStep e) ([], false)) := rfl
    rw [hins]
    generalize es.foldl (insStep e) ([], false) = st
    obtain ⟨o1, d⟩ := st
    cases d
    · wp_auto
      wp_apply wp_slice_literal (l := [e])
      isplitr
      · ipureintro; rfl
      iintro %lsl ⟨Hl1, _⟩
      wp_apply wp_slice_append $$ [$Ho $Hocap $Hl1] as %o' ⟨Ho, Hocap, -⟩
      iapply HΦ
      simp only [insFin, Bool.false_eq_true, if_false]
      iframe
    · wp_auto
      iapply HΦ
      simp only [insFin, if_true]
      iframe

end proof

end linkv
end EtcdGrove
end Perennial
