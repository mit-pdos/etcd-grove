/-
Lean-first (no Rocq counterpart).

The proof of `strHash`: the length, then each byte, mixed in (`mix`: some `w64`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.mix
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.strHash

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem strHash.wp_proof (wp_mix : mix.spec (GF := GF) (hG := hG)) :
    strHash.spec (GF := GF) (hG := hG) := by
  intro h s
  wp_start
  (try wp_auto)
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl
  wp_apply wp_mix as %h1 -
  (try wp_auto)
  ihave HI : (∃ (j : w64) (m : w64), "i" ∷ i_ptr ↦ j ∗ "h" ∷ h_ptr ↦ m ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ s.length⌝ : IProp GF) $$ [i h]
  · iexists W64 0, _
    iframe
    ipureintro; exact ⟨by word, by word⟩
  wp_for HI
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  wp_if_destruct
  · have Hlt : sint.Z j < sint.Z (BitVec.ofNat 64 s.length) := by
      apply Classical.byContradiction
      intro h
      simp only [h, decide_false] at Hif
      exact absurd (GoGlobalContext.intoVal_inj_bool Hif) (by decide)
    have hb : s[sint.nat j]? = some (s.getD (sint.nat j) (W8 0)) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by word)]; rfl
    rw [if_pos Hj.1, hb]
    (try wp_auto)
    wp_apply wp_mix as %h2 -
    (try wp_auto)
    wp_for_post
    iframe
    iexists j + W64 1, _
    iframe
    ipureintro
    exact ⟨by word, by word⟩
  · have Hge : ¬ (sint.Z j < sint.Z (W64 ↑s.length)) := by
      intro h; apply Hif; simp only [h, decide_true]
    simp only [Hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    (try wp_auto)
    iapply HΦ
    itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
