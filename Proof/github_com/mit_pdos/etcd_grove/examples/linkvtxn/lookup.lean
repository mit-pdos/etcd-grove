/-
Lean-first (no Rocq counterpart).

The proof of `lookup`: the loop's invariant is that no entry before the index has the key.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.lookup

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

/-- `lookup` returns at the first entry of the key. -/
theorem lookupL_at (es : List entry) (k : GoString) (j : Nat) (e : entry)
    (hj : es[j]? = some e) (hpre : ∀ x ∈ es.take j, x.key' ≠ k) (he : e.key' = k) :
    lookupL es k = (e.r', true) := by
  have hl : j < es.length := by
    rcases Nat.lt_or_ge j es.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hj; cases hj
  have hsplit : es = es.take j ++ e :: es.drop (j + 1) := by
    rw [List.getElem?_eq_getElem hl] at hj
    have := List.drop_eq_getElem_cons hl
    rw [Option.some.inj hj] at this
    rw [← this, List.take_append_drop]
  have hn : (es.take j).find? (fun e => decide (e.key' = k)) = none := by
    rw [List.find?_eq_none]; intro x hx; simpa using hpre x hx
  unfold lookupL
  rw [hsplit, List.find?_append, hn, Option.none_or, List.find?_cons_of_pos (by simpa using he)]

/-- `lookup` returns no value when no entry has the key. -/
theorem lookupL_absent (es : List entry) (k : GoString) (h : ∀ x ∈ es, x.key' ≠ k) :
    lookupL es k = (zVR, false) := by
  have hn : es.find? (fun e => decide (e.key' = k)) = none := by
    rw [List.find?_eq_none]; intro x hx; simpa using h x hx
  unfold lookupL; rw [hn]

theorem lookup.wp_proof : lookup.spec (GF := GF) (hG := hG) := by
  intro sl es dq k
  wp_start as Hs
  ihave %Hl := ownSlice_len $$ Hs
  wp_auto
  ihave HI : (∃ (j : w64) (e0 : entry),
      "i" ∷ i_ptr ↦ j ∗ "e" ∷ e_ptr ↦ e0 ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len ∧
        ∀ x ∈ es.take (sint.nat j), x.key' ≠ k⌝ : IProp GF) $$ [i e]
  · iexists W64 0, _
    iframe
    ipureintro; refine ⟨by word, by word, ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl]; simp
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, Hif⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem es (sint.nat j) as x
    wp_apply wp_load_slice_index sl (sint.Z j) es dq x Hj.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hx_lookup
    wp_if_destruct
    · wp_for_post
      iapply HΦ
      iframe
      ipureintro
      exact (lookupL_at es _ (sint.nat j) x Hx_lookup Hj.2.2 rfl).symm
    · wp_for_post
      iframe
      iexists j + W64 1, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Hx_lookup]
      intro y hy
      simp only [List.mem_append, Option.toList_some, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · exact Hj.2.2 y hy
      · exact Hif
  · iapply HΦ
    iframe
    ipureintro
    refine (lookupL_absent es k ?_).symm
    have : es.take (sint.nat j) = es := List.take_of_length_le (by word)
    rw [← this]; exact Hj.2.2

end proof

end linkvtxn
end EtcdGrove
end Perennial
