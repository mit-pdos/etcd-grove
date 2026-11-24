/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `votesHas`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.votesHas
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

omit [GooseSemantics] [GooseInterp] go_gctx in
/-- `voteRel` makes Go's `==` on `VoteRec`s Lean's equality of the records. -/
theorem votesHas_rel_iff {g g' : G.VoteRec} {x x' : VoteRec} (h : voteRel g x) (h' : voteRel g' x') :
    g = g' ↔ x = x' := by
  obtain ⟨g1, g2, g3⟩ := g
  obtain ⟨h1, h2, h3⟩ := g'
  obtain ⟨x1, x2, x3⟩ := x
  obtain ⟨y1, y2, y3⟩ := x'
  simp only [voteRel] at h h'
  obtain ⟨e1, e2, e3⟩ := h
  obtain ⟨f1, f2, f3⟩ := h'
  simp only [G.VoteRec, github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.VoteRec.mk.injEq,
    VoteRec.mk.injEq]
  subst e1 e2 e3 f1 f2 f3
  simp only [BitVec.toInt_inj]

theorem votesHas.wp_proof : votesHas.spec (GF := GF) (hG := hG) := by
  intro sl xs g x
  wp_start as ⟨#Hs, %Hgx⟩
  iunfold votesRO at Hs
  icases Hs with ⟨%gs, #Hgs, %Hrel⟩
  ihave %Hlen := ownSlice_len $$ Hgs
  have Hl := Hrel.length_eq
  wp_auto
  ihave IH : iprop(∃ (n : w64) (y : G.VoteRec),
      "i" ∷ i_ptr ↦ n ∗ "w" ∷ w_ptr ↦ y ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧ x ∉ xs.take (sint.nat n)⌝) $$ [i w]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < gs.length := by rw [Hlen.1]; word
    have Hlt' : sint.nat n < xs.length := Hl ▸ Hlt
    obtain ⟨y0, Hy⟩ : ∃ y, gs[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨x', Hx'⟩ : ∃ x', xs[sint.nat n]? = some x' := ⟨_, List.getElem?_eq_getElem Hlt'⟩
    have Hyx := forall₂_getElem Hrel (sint.nat n) Hlt Hlt'
    rw [Option.some.inj ((List.getElem?_eq_getElem Hlt).symm.trans Hy),
      Option.some.inj ((List.getElem?_eq_getElem Hlt').symm.trans Hx')] at Hyx
    have Hiff := votesHas_rel_iff Hyx Hgx
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1, Hif⟩))]
    wp_apply wp_load_slice_index sl (sint.Z n) gs DFrac.discard y0 Hn.1 $$ [Hgs] as -
    · isplitr
      · iexact Hgs
      ipureintro; exact Hy
    try wp_auto
    by_cases hyg : y0 = g
    · have hxx := Hiff.1 hyg
      subst hyg
      repeat' (wp_if_destruct)
      all_goals try (exfalso; contradiction)
      wp_for_post
      have : xs.contains x = true := List.contains_iff_mem.2 (hxx ▸ List.mem_of_getElem? Hx')
      rw [this]
      iapply HΦ; ipureintro; trivial
    · repeat' (wp_if_destruct)
      all_goals try (exfalso; apply hyg; obtain ⟨⟩ := y0; obtain ⟨⟩ := g; simp_all; done)
      all_goals
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hx']
        simp only [Option.toList_some, List.mem_append, List.mem_singleton, not_or]
        exact ⟨Hn.2.2, fun h => hyg (Hiff.2 h.symm)⟩
  · try wp_auto
    have hnx : sint.nat n = xs.length := by rw [← Hl, Hlen.1]; word
    have h := Hn.2.2
    rw [hnx, List.take_length] at h
    have : xs.contains x = false := by
      rw [Bool.eq_false_iff]; intro hc; exact h (List.contains_iff_mem.1 hc)
    rw [this]
    iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
