/-
Lean-first (no Rocq counterpart). #33 S3b W1 (2026-11-23): the proof of `State.Over` (B 153).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Over
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__EffTerm
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

theorem State.Over.wp_proof (wp_EffTerm : State.EffTerm.spec (GF := GF) (hG := hG)) :
    State.Over.spec (GF := GF) (hG := hG) := by
  intro p s t
  wp_start as #Hs
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  iunfold configRO at HCfg
  icases HCfg with ⟨%gc, #Hgc, #Hsrv, #-, %-⟩
  iStructNamed Hgc
  iunfold strsRO at Hsrv
  ihave %Hsl := ownSlice_len $$ Hsrv
  wp_auto
  ihave IH : iprop(∃ (n jv : w64),
      "i" ∷ i_ptr ↦ n ∗ "j" ∷ j_ptr ↦ jv ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z gc.Server'.len ∧
        ∀ j, j < sint.nat n → s.effTerm j > sint.Z t⌝) $$ [i j]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by word, by word, fun j hj => absurd hj (by simp)⟩
  wp_for IH
  obtain ⟨hn0, hn1, hall⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < s.cfg.server.length := by rw [Hsl.1]; word
    obtain ⟨x, Hx⟩ : ∃ x, s.cfg.server[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z gc.Server'.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index gc.Server' (sint.Z n) s.cfg.server DFrac.discard x hn0 $$ [Hsrv] as -
    · isplitr
      · iexact Hsrv
      ipureintro; exact Hx
    try wp_auto
    wp_apply wp_EffTerm p s n $$ [Hs] as %e %He
    · iframe Hs; ipureintro; exact ⟨hn0, by have := Hsl.1; word⟩
    try wp_auto
    wp_if_destruct
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      intro j hj
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · exact hall j hj
      · subst hj; rw [← He]; omega
    · -- `EffTerm(j) <= t`: not over
      try wp_auto
      wp_for_post
      try wp_auto
      have : s.over (sint.Z t) = false := by
        unfold State.over
        rw [List.all_eq_false]
        exact ⟨sint.nat n, List.mem_range.2 Hlt, by
          have : s.effTerm (sint.nat n) = sint.Z e := by rw [He]
          simp only [decide_eq_true_eq]; omega⟩
      rw [this]
      iapply HΦ; ipureintro; trivial
  · try wp_auto
    have hnx : sint.nat n = s.cfg.server.length := by rw [Hsl.1]; word
    have : s.over (sint.Z t) = true := by
      unfold State.over
      rw [List.all_eq_true]
      intro j hj
      simp only [decide_eq_true_eq]
      exact hall j (by rw [hnx]; exact List.mem_range.1 hj)
    rw [this]
    iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
