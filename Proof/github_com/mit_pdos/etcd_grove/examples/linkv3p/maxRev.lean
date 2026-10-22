/- Lean-first (no Rocq counterpart). The proof of `maxRev`: the loop keeping the maximum. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.maxRev

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.linkv3p

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

theorem maxRev.wp_proof : maxRev.spec (GF := GF) (hG := hG) := by
  intro sl oks dq
  wp_start as Hs
  ihave %Hl := ownSlice_len $$ Hs
  (try wp_auto)
  ihave HI : (∃ (j : w64) (p0 : wrec) (m : w64),
      "i" ∷ i_ptr ↦ j ∗ "p" ∷ p_ptr ↦ p0 ∗ "m" ∷ m_ptr ↦ m ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len ∧ 0 ≤ sint.Z m ∧
        ∀ p ∈ oks.take (sint.nat j), sint.Z p.rev' ≤ sint.Z m⌝ : IProp GF) $$ [i p m]
  · iexists W64 0, _, W64 0
    iframe
    ipureintro; refine ⟨by word, by word, by word, ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl]; simp
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, Hif⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem oks (sint.nat j) as x
    wp_apply wp_load_slice_index sl (sint.Z j) oks dq x Hj.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hx_lookup
    have htake : oks.take (sint.nat (j + W64 1)) = oks.take (sint.nat j) ++ [x] := by
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Hx_lookup]; rfl
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, x, x.rev'
      iframe
      ipureintro
      refine ⟨by word, by word, by word, ?_⟩
      rw [htake]
      intro p hp
      simp only [List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · have := Hj.2.2.2 p hp; word
      · exact Int.le_refl _
    · (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, x, m
      iframe
      ipureintro
      refine ⟨by word, by word, Hj.2.2.1, ?_⟩
      rw [htake]
      intro p hp
      simp only [List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact Hj.2.2.2 p hp
      · word
  · (try wp_auto)
    iapply HΦ
    iframe
    ipureintro
    refine ⟨Hj.2.2.1, ?_⟩
    have : oks.take (sint.nat j) = oks := List.take_of_length_le (by word)
    rw [this] at Hj
    exact Hj.2.2.2

end proof

end linkv3p
end EtcdGrove
end Perennial
