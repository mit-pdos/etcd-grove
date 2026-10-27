module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.setItem

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

theorem setItem.wp_proof : setItem.spec (GF := GF) (hG := hG) := by
  intro sl its dq it
  wp_start as ⟨Hs, %Hb⟩
  ihave %Hl := ownSlice_len $$ Hs
  wp_auto
  wp_apply wp_slice_make3 (V := item) (W64 0) (sl.len + W64 1) ⟨by word, by word⟩
    as %o0 ⟨Ho, Hocap, -⟩
  rw [List.replicate_zero]
  ihave HI : (∃ (j : w64) (e0 : item) (o : GoSlice),
      "i" ∷ i_ptr ↦ j ∗ "e" ∷ e_ptr ↦ e0 ∗ "out" ∷ out_ptr ↦ o ∗
      "done" ∷ done_ptr ↦ ((its.take (sint.nat j)).foldl (setStepI it) ([], false)).2 ∗
      "Ho" ∷ o ↦* ((its.take (sint.nat j)).foldl (setStepI it) ([], false)).1 ∗
      "Hocap" ∷ ownSliceCap item o (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len⌝ : IProp GF) $$ [i e out done Ho Hocap]
  · iexists W64 0, _, o0
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.foldl_nil]
    iframe
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, Hif⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem its (sint.nat j) as x
    wp_apply wp_load_slice_index sl (sint.Z j) its dq x Hj.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hx_lookup
    have Htake : (its.take (sint.nat (j + W64 1))).foldl (setStepI it) ([], false) =
        setStepI it ((its.take (sint.nat j)).foldl (setStepI it) ([], false)) x := by
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Hx_lookup]
      simp
    generalize (its.take (sint.nat j)).foldl (setStepI it) ([], false) = st at Htake ⊢
    obtain ⟨o1, d⟩ := st
    simp only at Htake ⊢
    cases d
    · (try wp_auto)
      wp_if_destruct
      · have Hlt := Hif
        wp_apply wp_slice_literal (l := [it])
        isplitr
        · ipureintro; rfl
        iintro %lsl1 ⟨Hl1, _⟩
        wp_apply wp_slice_append $$ [$Ho $Hocap $Hl1] as %oa ⟨Ho, Hocap, -⟩
        (try wp_auto)
        wp_if_destruct
        · (try wp_auto)
          wp_for_post
          iframe
          iexists j + W64 1, _, oa
          have hst : setStepI it (o1, false) x = (o1 ++ [it], true) := by simp [setStepI, Hlt, Hif, go.goStringLt_irrefl]
          rw [Htake, hst]
          simp only [List.append_assoc, List.cons_append, List.nil_append]
          iframe
          ipureintro; word
        · (try wp_auto)
          wp_apply wp_slice_literal (l := [x])
          isplitr
          · ipureintro; rfl
          iintro %lsl2 ⟨Hl2, _⟩
          wp_apply wp_slice_append $$ [$Ho $Hocap $Hl2] as %ob ⟨Ho, Hocap, -⟩
          (try wp_auto)
          wp_for_post
          iframe
          iexists j + W64 1, _, ob
          have hst : setStepI it (o1, false) x = (o1 ++ [it] ++ [x], true) := by simp [setStepI, Hlt, Hif, go.goStringLt_irrefl]
          rw [Htake, hst]
          simp only [List.append_assoc, List.cons_append, List.nil_append]
          iframe
          ipureintro; word
      · have Hlt := Hif
        wp_if_destruct
        · (try wp_auto)
          wp_apply wp_slice_literal (l := [it])
          isplitr
          · ipureintro; rfl
          iintro %lsl1 ⟨Hl1, _⟩
          wp_apply wp_slice_append $$ [$Ho $Hocap $Hl1] as %oa ⟨Ho, Hocap, -⟩
          (try wp_auto)
          wp_for_post
          iframe
          iexists j + W64 1, _, oa
          have hst : setStepI it (o1, false) x = (o1 ++ [it], true) := by simp [setStepI, Hlt, Hif, go.goStringLt_irrefl]
          rw [Htake, hst]
          simp only [List.append_assoc, List.cons_append, List.nil_append]
          iframe
          ipureintro; word
        · (try wp_auto)
          wp_apply wp_slice_literal (l := [x])
          isplitr
          · ipureintro; rfl
          iintro %lsl2 ⟨Hl2, _⟩
          wp_apply wp_slice_append $$ [$Ho $Hocap $Hl2] as %ob ⟨Ho, Hocap, -⟩
          (try wp_auto)
          wp_for_post
          iframe
          iexists j + W64 1, _, ob
          have hst : setStepI it (o1, false) x = (o1 ++ [x], false) := by simp [setStepI, Hlt, Hif, go.goStringLt_irrefl]
          rw [Htake, hst]
          simp only [List.append_assoc, List.cons_append, List.nil_append]
          iframe
          ipureintro; word
    · (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, _, o
        have hst : setStepI it (o1, true) x = (o1, true) := by simp [setStepI, Hif]
        rw [Htake, hst]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
        iframe
        ipureintro; word
      · (try wp_auto)
        wp_apply wp_slice_literal (l := [x])
        isplitr
        · ipureintro; rfl
        iintro %lsl2 ⟨Hl2, _⟩
        wp_apply wp_slice_append $$ [$Ho $Hocap $Hl2] as %ob ⟨Ho, Hocap, -⟩
        (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, _, ob
        have hst : setStepI it (o1, true) x = (o1 ++ [x], true) := by simp [setStepI, Hif]
        rw [Htake, hst]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
        iframe
        ipureintro; word
  · -- the end
    have hall : its.take (sint.nat j) = its := List.take_of_length_le (by word)
    rw [hall]
    have hset : setItemL its it =
        (let st := its.foldl (setStepI it) ([], false); if st.2 then st.1 else st.1 ++ [it]) := rfl
    rw [hset]
    generalize its.foldl (setStepI it) ([], false) = st
    obtain ⟨o1, d⟩ := st
    cases d
    · wp_auto
      wp_apply wp_slice_literal (l := [it])
      isplitr
      · ipureintro; rfl
      iintro %lsl ⟨Hl1, _⟩
      wp_apply wp_slice_append $$ [$Ho $Hocap $Hl1] as %o' ⟨Ho, Hocap, -⟩
      iapply HΦ
      simp only [Bool.false_eq_true, if_false]
      iframe
    · wp_auto
      iapply HΦ
      simp only [if_true]
      iframe

end proof

end k8setcd3
end EtcdGrove
end Perennial
