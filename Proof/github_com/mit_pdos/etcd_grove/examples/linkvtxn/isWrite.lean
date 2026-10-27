/-
Lean-first (no Rocq counterpart).

The proof of `isWrite`: by the kind; a transaction's then- and else-operations, each loop's
invariant that no operation before the index writes.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.isWrite
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.thenOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.elseOf

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkvtxn

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

theorem isWriteL_txn (x : Input) (h2 : ¬ x.Kind' = W64 2) (h3 : ¬ x.Kind' = W64 3)
    (h4 : x.Kind' = W64 4) :
    isWriteL x = ((thenOfL x).any (fun op => decide (op.Kind' ≠ W64 0)) ||
      (elseOfL x).any (fun op => decide (op.Kind' ≠ W64 0))) := by
  unfold isWriteL
  rw [if_neg (by rintro (h | h) <;> contradiction), if_neg (fun h => h h4)]

theorem isWrite.wp_proof (wp_thenOf : thenOf.spec (GF := GF) (hG := hG))
    (wp_elseOf : elseOf.spec (GF := GF) (hG := hG)) :
    isWrite.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  wp_auto
  wp_if_destruct
  · rw [show isWriteL x = true by unfold isWriteL; rw [if_pos (Or.inl Hif)]]
    iapply HΦ; itrivial
  · have H2 := Hif; clear Hif
    wp_if_destruct
    · rw [show isWriteL x = true by unfold isWriteL; rw [if_pos (Or.inr Hif)]]
      iapply HΦ; itrivial
    · have H3 := Hif; clear Hif
      wp_if_destruct
      · have H4 := Hif; clear Hif
        rw [isWriteL_txn x H2 H3 H4]
        irename : (in_ptr ↦ x : IProp GF) => Hin
        wp_apply wp_thenOf x as %s1 ⟨Hs1, Hs1cap⟩
        ihave %Hls1 := ownSlice_len $$ Hs1
        ihave HI : (∃ (j : w64) (o0 : TOp),
            "i" ∷ i_ptr ↦ j ∗ "op" ∷ op_ptr ↦ o0 ∗
            "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s1.len ∧
              ∀ o ∈ (thenOfL x).take (sint.nat j), o.Kind' = W64 0⌝ : IProp GF) $$ [i op]
        · iexists W64 0, _
          iframe
          ipureintro; refine ⟨by word, by word, ?_⟩
          rw [show sint.nat (W64 0) = 0 from rfl]; simp
        wp_for HI
        wp_if_destruct
        · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s1.len := ⟨Hj.1, Hif⟩
          simp only [Hb', _root_.and_self, ↓reduceIte]
          list_elem (thenOfL x) (sint.nat j) as o
          wp_apply wp_load_slice_index s1 (sint.Z j) (thenOfL x) _ o Hj.1 $$ [Hs1] as Hs1
          · iframe; ipureintro; exact Ho_lookup
          wp_if_destruct
          · wp_for_post
            iframe
            iexists j + W64 1, _
            iframe
            ipureintro
            refine ⟨by word, by word, ?_⟩
            rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Ho_lookup]
            intro y hy
            simp only [List.mem_append, Option.toList_some, List.mem_singleton] at hy
            rcases hy with hy | rfl
            · exact Hj.2.2 y hy
            · exact Hif
          · wp_for_post
            have hw : (thenOfL x).any (fun op => decide (op.Kind' ≠ W64 0)) = true :=
              List.any_eq_true.2 ⟨o, List.mem_of_getElem? Ho_lookup, by simpa using Hif⟩
            rw [hw]
            try simp only [Bool.true_or]
            iapply HΦ; itrivial
        · have hall : ∀ o ∈ thenOfL x, o.Kind' = W64 0 := by
            have : (thenOfL x).take (sint.nat j) = thenOfL x := List.take_of_length_le (by word)
            rw [← this]; exact Hj.2.2
          have hn : (thenOfL x).any (fun op => decide (op.Kind' ≠ W64 0)) = false :=
            List.any_eq_false.2 (fun o ho => by simp [hall o ho])
          rw [hn]
          try simp only [Bool.false_or]
          wp_apply wp_elseOf x as %s2 ⟨Hs2, Hs2cap⟩
          ihave %Hls2 := ownSlice_len $$ Hs2
          ihave HI : (∃ (j : w64) (o0 : TOp),
              "i" ∷ i_ptr ↦ j ∗ "op" ∷ op_ptr ↦ o0 ∗
              "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s2.len ∧
                ∀ o ∈ (elseOfL x).take (sint.nat j), o.Kind' = W64 0⌝ : IProp GF) $$ [i op]
          · iexists W64 0, _
            iframe
            ipureintro; refine ⟨by word, by word, ?_⟩
            rw [show sint.nat (W64 0) = 0 from rfl]; simp
          wp_for HI
          wp_if_destruct
          · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s2.len := ⟨Hj.1, Hif⟩
            simp only [Hb', _root_.and_self, ↓reduceIte]
            list_elem (elseOfL x) (sint.nat j) as o
            wp_apply wp_load_slice_index s2 (sint.Z j) (elseOfL x) _ o Hj.1 $$ [Hs2] as Hs2
            · iframe; ipureintro; exact Ho_lookup
            wp_if_destruct
            · wp_for_post
              iframe
              iexists j + W64 1, _
              iframe
              ipureintro
              refine ⟨by word, by word, ?_⟩
              rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Ho_lookup]
              intro y hy
              simp only [List.mem_append, Option.toList_some, List.mem_singleton] at hy
              rcases hy with hy | rfl
              · exact Hj.2.2 y hy
              · exact Hif
            · wp_for_post
              have hw : (elseOfL x).any (fun op => decide (op.Kind' ≠ W64 0)) = true :=
                List.any_eq_true.2 ⟨o, List.mem_of_getElem? Ho_lookup, by simpa using Hif⟩
              rw [hw]
              try simp only [Bool.true_or]
              iapply HΦ; itrivial
          · have hall : ∀ o ∈ elseOfL x, o.Kind' = W64 0 := by
              have : (elseOfL x).take (sint.nat j) = elseOfL x := List.take_of_length_le (by word)
              rw [← this]; exact Hj.2.2
            have hn : (elseOfL x).any (fun op => decide (op.Kind' ≠ W64 0)) = false :=
              List.any_eq_false.2 (fun o ho => by simp [hall o ho])
            rw [hn]
            try simp only [Bool.false_or]
            iapply HΦ; itrivial
      · rw [show isWriteL x = false by
          unfold isWriteL; rw [if_neg (by rintro (h | h) <;> contradiction), if_pos Hif]]
        iapply HΦ; itrivial

end proof

end linkvtxn
end EtcdGrove
end Perennial
