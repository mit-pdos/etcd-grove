module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.lookup

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

theorem lookupL_at (its : List item) (k : GoString) (j : Nat) (e : item)
    (hj : its[j]? = some e) (hpre : ∀ x ∈ its.take j, x.key' ≠ k) (he : e.key' = k) :
    lookupL its k = (e, true) := by
  have hl : j < its.length := by
    rcases Nat.lt_or_ge j its.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hj; cases hj
  have hsplit : its = its.take j ++ e :: its.drop (j + 1) := by
    rw [List.getElem?_eq_getElem hl] at hj
    have := List.drop_eq_getElem_cons hl
    rw [Option.some.inj hj] at this
    rw [← this, List.take_append_drop]
  have hn : (its.take j).find? (fun e => decide (e.key' = k)) = none := by
    rw [List.find?_eq_none]; intro x hx; simpa using hpre x hx
  unfold lookupL
  rw [hsplit, List.find?_append, hn, Option.none_or, List.find?_cons_of_pos (by simpa using he)]

/-- `lookup` returns no item when none has the key. -/
theorem lookupL_absent (its : List item) (k : GoString) (h : ∀ x ∈ its, x.key' ≠ k) :
    lookupL its k = (zItem, false) := by
  have hn : its.find? (fun e => decide (e.key' = k)) = none := by
    rw [List.find?_eq_none]; intro x hx; simpa using h x hx
  unfold lookupL; rw [hn]

theorem lookup.wp_proof : lookup.spec (GF := GF) (hG := hG) := by
  intro sl its dq k
  wp_start as Hs
  ihave %Hl := ownSlice_len $$ Hs
  wp_auto
  ihave HI : (∃ (j : w64) (e0 : item),
      "i" ∷ i_ptr ↦ j ∗ "it" ∷ it_ptr ↦ e0 ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len ∧
        ∀ x ∈ its.take (sint.nat j), x.key' ≠ k⌝ : IProp GF) $$ [i it]
  · iexists W64 0, _
    iframe
    ipureintro; refine ⟨by word, by word, ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl]; simp
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, Hif⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem its (sint.nat j) as x
    wp_apply wp_load_slice_index sl (sint.Z j) its dq x Hj.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hx_lookup
    wp_if_destruct
    · wp_for_post
      iapply HΦ
      iframe
      ipureintro
      exact (lookupL_at its _ (sint.nat j) x Hx_lookup Hj.2.2 rfl).symm
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
    refine (lookupL_absent its k ?_).symm
    have : its.take (sint.nat j) = its := List.take_of_length_le (by word)
    rw [← this]; exact Hj.2.2

end proof

end k8setcd3
end EtcdGrove
end Perennial
