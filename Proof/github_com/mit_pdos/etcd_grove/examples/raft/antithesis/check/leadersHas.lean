/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `leadersHas`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.leadersHas
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
/-- The relation of `leadersRO` makes Go's `==` on `LeaderRec`s Lean's equality of the records. -/
theorem leadersHas_rel_iff {g g' : G.LeaderRec} {x x' : LeaderRec}
    (h : g.Server' = x.server ∧ sint.Z g.Term' = x.term) (h' : g'.Server' = x'.server ∧ sint.Z g'.Term' = x'.term) :
    g = g' ↔ x = x' := by
  obtain ⟨g1, g2⟩ := g
  obtain ⟨h1, h2⟩ := g'
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := x'
  obtain ⟨e1, e2⟩ := h
  obtain ⟨f1, f2⟩ := h'
  simp only [G.LeaderRec, github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.LeaderRec.mk.injEq,
    LeaderRec.mk.injEq]
  dsimp only at e1 e2 f1 f2
  subst e1 e2 f1 f2
  simp only [BitVec.toInt_inj]

theorem leadersHas.wp_proof : leadersHas.spec (GF := GF) (hG := hG) := by
  intro sl xs g x
  wp_start as ⟨#Hs, %Hgx⟩
  iunfold leadersRO at Hs
  icases Hs with ⟨%gs, #Hgs, %Hrel⟩
  ihave %Hlen := ownSlice_len $$ Hgs
  have Hl := Hrel.length_eq
  wp_auto
  ihave IH : iprop(∃ (n : w64) (y : G.LeaderRec),
      "i" ∷ i_ptr ↦ n ∗ "m" ∷ m_ptr ↦ y ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧ x ∉ xs.take (sint.nat n)⌝) $$ [i m]
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
    have Hiff := leadersHas_rel_iff Hyx Hgx
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
