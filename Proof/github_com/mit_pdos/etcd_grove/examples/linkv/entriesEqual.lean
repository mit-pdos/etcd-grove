/-
Lean-first (no Rocq counterpart).

The proof of `entriesEqual`: the lengths, then the loop, whose invariant is that the entries
before the index are equal.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.entriesEqual

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

theorem entriesEqual.wp_proof : entriesEqual.spec (GF := GF) (hG := hG) := by
  intro sa sb xs ys dqa dqb
  wp_start as ⟨Ha, Hb⟩
  ihave %Hla := ownSlice_len $$ Ha
  ihave %Hlb := ownSlice_len $$ Hb
  wp_auto
  wp_if_destruct
  · rename_i iu_ptr
    have Heq := Hif; clear Hif
    irename : (iu_ptr ↦ zero_val w64 : IProp GF) => Hiu
    ihave HI : (∃ (i j : w64),
        "i" ∷ i_ptr ↦ i ∗ "Hiu" ∷ iu_ptr ↦ j ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sa.len ∧
          xs.take (sint.nat i) = ys.take (sint.nat i)⌝ : IProp GF) $$ [i Hiu]
    · iexists W64 0, _
      iframe
      ipureintro; refine ⟨by word, by word, rfl⟩
    wp_for HI
    wp_if_destruct
    · have Hb' : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sa.len := ⟨Hi.1, Hif⟩
      have Hb2' : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sb.len := by rw [← Heq]; exact Hb'
      simp only [Hb', _root_.and_self, ↓reduceIte]
      list_elem xs (sint.nat i) as w
      list_elem ys (sint.nat i) as w2
      wp_apply wp_load_slice_index sa (sint.Z i) xs dqa w Hi.1 $$ [Ha] as Ha
      · iframe; ipureintro; exact Hw_lookup
      simp only [Hb', _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index sa (sint.Z i) xs dqa w Hi.1 $$ [Ha] as Ha
      · iframe; ipureintro; exact Hw_lookup
      simp only [Hb2', _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index sb (sint.Z i) ys dqb w2 Hi.1 $$ [Hb] as Hb
      · iframe; ipureintro; exact Hw2_lookup
      wp_if_destruct
      · have Hk := Hif
        wp_if_destruct
        · -- equal: the next index
          have hw : w = w2 := by cases w; cases w2; simp_all
          wp_for_post
          iframe
          iexists i + W64 1, _
          iframe
          ipureintro
          refine ⟨by word, by word, ?_⟩
          rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, List.take_add_one,
            List.take_add_one, Hi.2.2, Hw_lookup, Hw2_lookup, hw]
        · have hne : xs ≠ ys := fun h => Hif (by
            subst h; rw [Hw_lookup] at Hw2_lookup; cases Hw2_lookup; rfl)
          wp_for_post
          rw [show decide (xs = ys) = false from decide_eq_false hne]
          iapply HΦ
          iframe
      · have hne : xs ≠ ys := fun h => Hif (by
          subst h; rw [Hw_lookup] at Hw2_lookup; cases Hw2_lookup; rfl)
        wp_for_post
        rw [show decide (xs = ys) = false from decide_eq_false hne]
        iapply HΦ
        iframe
    · have h1 : xs.length = sint.nat i := by word
      have h2 : ys.length = sint.nat i := by rw [Hlb.1, ← Heq]; word
      have heq : xs = ys := by
        have := Hi.2.2
        rwa [← h1, List.take_length, h1, ← h2, List.take_length] at this
      rw [show decide (xs = ys) = true from decide_eq_true heq]
      iapply HΦ
      iframe
  · rw [decide_eq_false (fun h => Hif (by subst h; word))]
    iapply HΦ; iframe

end proof

end linkv
end EtcdGrove
end Perennial
