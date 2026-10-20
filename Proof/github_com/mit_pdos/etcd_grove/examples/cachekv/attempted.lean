/- Lean-first (no Rocq counterpart). The proof of `attempted`: the loop over `tried`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.cachekv.attempted

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cachekv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.cachekv

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.cachekv.Assumptions]

theorem attempted.wp_proof : attempted.spec (GF := GF) (hG := hG) := by
  intro sl tried dq key val
  wp_start as Hs
  ihave %Hl := ownSlice_len $$ Hs
  wp_auto
  ihave HI : (∃ (j : w64) (p0 : ckv),
      "i" ∷ i_ptr ↦ j ∗ "p" ∷ p_ptr ↦ p0 ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len ∧
        (key, val) ∉ (tried.take (sint.nat j)).map pairOf⌝ : IProp GF) $$ [i p]
  · iexists W64 0, _
    iframe
    ipureintro; refine ⟨by word, by word, ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl]; simp
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, Hif⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem tried (sint.nat j) as x
    wp_apply wp_load_slice_index sl (sint.Z j) tried dq x Hj.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hx_lookup
    (try wp_auto)
    by_cases hk : x.key' = key
    · subst hk
      by_cases hv : x.val' = val
      · subst hv
        simp only [decide_true]
        wp_auto
        wp_for_post
        iapply HΦ
        iframe
        ipureintro; intro; rfl
      · simp only [decide_true]
        wp_auto
        rw [decide_eq_false hv]
        wp_auto
        wp_for_post
        iframe
        iexists j + W64 1, _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Hx_lookup]
        simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil,
          List.mem_append, List.mem_singleton, not_or]
        refine ⟨Hj.2.2, ?_⟩
        unfold pairOf; intro h; simp at h; exact hv h.symm
    · rw [decide_eq_false hk]
      wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Hx_lookup]
      simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil,
        List.mem_append, List.mem_singleton, not_or]
      refine ⟨Hj.2.2, ?_⟩
      unfold pairOf; intro h; simp at h; exact hk h.1.symm
  · iapply HΦ
    iframe
    ipureintro
    intro hm
    exfalso
    have : tried.take (sint.nat j) = tried := List.take_of_length_le (by word)
    rw [this] at Hj
    exact Hj.2.2 hm

end proof

end cachekv
end EtcdGrove
end Perennial
