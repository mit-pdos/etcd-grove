/-
Lean-first (no Rocq counterpart).

The proof of `orderByLinearization`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.orderByLinearization
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.RunLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine

/-- Standalone (an inline `omega` here is rejected by the kernel once abstracted:
`notes/decisions.md`, "A kernel rejection of auto-abstracted inline `omega`/`word` proofs"). -/
theorem lt_of_lt_succ_ne {k a b : Nat} (hab : a = b + 1) (hk : k < a) (hne : ¬ b = k) : k < b := by
  omega

theorem lt_len_of_ge {k n m : Nat} (hjx : n = m) (hk : k < m) : k < n := by omega

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.lintest.Assumptions]

theorem orderByLinearization.wp_proof :
    orderByLinearization.spec (GF := GF) (hG := hG) := by
  intro osl lsl os xs dq1 dq2 Hxs
  wp_start as ⟨Hos, Hls⟩
  ihave %Hlsl := ownSlice_len _ _ _ $$ Hls
  ihave %Hosl := ownSlice_len _ _ _ $$ Hos
  wp_auto
  wp_apply (wp_slice_make2 (V := Operation) lsl.len) as %rsl ⟨Hr, -⟩
  · ipureintro; word
  rename_i ui_ptr
  irename : (ui_ptr ↦ zero_val w64 : IProp GF) => ui
  ihave HI : (∃ (j uv dv : w64) (rs : List Operation),
      "i" ∷ i_ptr ↦ j ∗ "ui" ∷ ui_ptr ↦ uv ∗ "idx" ∷ idx_ptr ↦ dv ∗ "Hr" ∷ rsl ↦* rs ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z lsl.len ∧ rs.length = xs.length ∧
        ∀ k, k < sint.nat j → rs[k]? = (xs[k]?).bind (fun x => os[(sint.Z x).toNat]?)⌝ : IProp GF)
    $$ [i ui idx Hr]
  · iexists W64 0, _, _, _
    iframe
    ipureintro
    refine ⟨by decide, by word, by simp [Hlsl.1], fun k hk => absurd hk (by word)⟩
  wp_for HI
  obtain ⟨Hj1, Hj2, Hj3, Hj4⟩ := Hj
  wp_if_destruct
  · have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z lsl.len := ⟨Hj1, Hif⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    list_elem xs (sint.nat j) as x
    wp_apply wp_load_slice_index lsl (sint.Z j) xs dq2 x hb.1 $$ [Hls] as Hls
    · iframe; ipureintro; exact Hx_lookup
    have hxv := Hxs x (List.mem_of_getElem? Hx_lookup)
    have hxb : 0 ≤ sint.Z x ∧ sint.Z x < sint.Z osl.len := ⟨hxv.1, by have := hxv.2; word⟩
    simp only [hxb, _root_.and_self, ↓reduceIte]
    list_elem os ((sint.Z x).toNat) as o
    wp_apply wp_load_slice_index osl (sint.Z x) os dq1 o hxv.1 $$ [Hos] as Hos
    · iframe; ipureintro; exact Ho_lookup
    ihave %Hrl := ownSlice_len _ _ _ $$ Hr
    have hrs : sint.nat rsl.len = sint.nat lsl.len := by rw [← Hrl.1, Hj3, Hlsl.1]
    have hjr : sint.Z j < sint.Z rsl.len := by
      have h1 := Hif; have h2 := Hrl.2; have h3 := Hlsl.2
      have h4 : sint.Z rsl.len = sint.Z lsl.len := by
        rw [← Int.toNat_of_nonneg h2, ← Int.toNat_of_nonneg h3]
        exact congrArg _ hrs
      omega
    have hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z rsl.len := ⟨Hj1, hjr⟩
    have hjrs : sint.nat j < rs.length := by
      rw [Hrl.1]; have := Hj1; have := hjr; word
    simp only [hb', _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index $$ [Hr] as Hr
    · iframe; ipureintro
      have h : (sint.Z j).toNat < rs.length := hjrs
      exact ⟨Hj1, by omega⟩
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
      have := Hj1; have := hjr; word
    have hj1z : 0 ≤ sint.Z (j + W64 1) ∧ sint.Z (j + W64 1) ≤ sint.Z lsl.len := by
      have := Hj1; have := Hif; word
    wp_for_post
    iframe
    iexists j + W64 1, j, x, _
    iframe
    ipureintro
    refine ⟨hj1z.1, hj1z.2, by simp [Hj3], fun k hk => ?_⟩
    rw [List.getElem?_set]
    by_cases hjk : sint.nat j = k
    · subst hjk
      simp only [show (sint.Z j).toNat = sint.nat j from rfl, ↓reduceIte,
        hjrs, Hx_lookup, Option.bind_some,
        Ho_lookup]
    · simp only [show ¬ ((sint.Z j).toNat = k) from fun h => hjk h, ↓reduceIte]
      exact Hj4 k (lt_of_lt_succ_ne hj1 hk hjk)
  · have hjx : sint.nat j = xs.length := by
      have : ¬ (sint.Z j < sint.Z lsl.len) := Hif
      rw [Hlsl.1]; word
    have hall : ∀ x ∈ xs, (os[(sint.Z x).toNat]?).isSome := fun x hx => by
      simp [List.getElem?_eq_getElem (Hxs x hx).2]
    have Hrs : rs = xs.filterMap (fun x => os[(sint.Z x).toNat]?) := by
      apply List.ext_getElem?
      intro k
      rw [getElem?_filterMap_all _ xs hall k]
      by_cases hk : k < xs.length
      · exact Hj4 k (lt_len_of_ge hjx hk)
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]; rfl
    iapply HΦ
    rw [← Hrs]
    iframe

end proof

end lintest
end EtcdGrove
end Perennial
