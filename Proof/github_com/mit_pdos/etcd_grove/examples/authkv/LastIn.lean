/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/authkv/LastIn.lean`: the loop's invariant,
`last` is `lastInFrom 0` of the events visited. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.LastIn
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.InRange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode common

section lemmas
variable [GooseExts]

theorem lastInFrom_take_succ (evs : List wev) (j : Nat) (e : wev) (h : evs[j]? = some e) :
    lastInFrom (W64 0) (evs.take (j + 1)) =
      if inRangeK e.Key' then e.Rev' else lastInFrom (W64 0) (evs.take j) := by
  rw [List.take_add_one, h]
  simp [lastInFrom, List.foldl_append]

end lemmas

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

theorem LastIn.wp_proof (wp_InRange : InRange.spec (GF := GF) (hG := hG)) :
    LastIn.spec (GF := GF) (hG := hG) := by
  intro esl evs dq
  wp_start as Hevs
  ihave %Hel := ownSlice_len $$ Hevs
  wp_auto
  ihave HI : (∃ (j : w64) (e0 : wev) (l : w64),
      "i" ∷ i_ptr ↦ j ∗ "e" ∷ e_ptr ↦ e0 ∗ "last" ∷ last_ptr ↦ l ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z esl.len⌝ ∗
      "%Hl" ∷ ⌜l = lastInFrom (W64 0) (evs.take (sint.nat j))⌝ : IProp GF) $$ [i e last]
  · iexists W64 0, _, W64 0
    iframe
    ipureintro; refine ⟨⟨by word, by word⟩, by rw [show sint.nat (W64 0) = 0 by word]; rfl⟩
  wp_for HI
  wp_if_destruct
  · have Hlt : sint.Z j < sint.Z esl.len := 
      Classical.byContradiction fun h => by simp [h] at Hif
    have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z esl.len := ⟨Hj.1, Hlt⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem evs (sint.nat j) as x
    wp_apply wp_load_slice_index esl (sint.Z j) evs dq x Hj.1 $$ [Hevs] as Hevs
    · iframe; ipureintro; exact Hx_lookup
    (try wp_auto)
    wp_apply wp_InRange
    have Hs : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    by_cases hk : inRangeK x.Key'
    · simp only [hk, decide_true]
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, x, x.Rev'
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ?_⟩
      rw [Hs, lastInFrom_take_succ evs _ x Hx_lookup, if_pos hk]
    · simp only [hk, decide_false]
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, x, l
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ?_⟩
      rw [Hs, lastInFrom_take_succ evs _ x Hx_lookup, if_neg hk, Hl]
  · (try wp_auto)
    have Hjl : sint.nat j = evs.length := by word
    rw [Hjl, List.take_length] at Hl
    rw [Hl]
    unfold lastIn
    iapply HΦ
    iframe

end proof

end authkv
end EtcdGrove
end Perennial
