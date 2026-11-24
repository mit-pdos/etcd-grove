/-
Lean-first (no Rocq counterpart). #33 S3b W7 (2026-11-23): the proof of `violated` (`check.go`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.violated
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__ElectionSafety
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__OneVotePerTerm
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Init0Laws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
set_option linter.unusedSimpArgs false
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem violated.wp_proof
    (wp_ElectionSafety : State.ElectionSafety.spec (GF := GF) (hG := hG))
    (wp_OneVotePerTerm : State.OneVotePerTerm.spec (GF := GF) (hG := hG)) :
    violated.spec (GF := GF) (hG := hG) := by
  intro p s
  wp_start as #Hs
  iapply wp_fupd
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  wp_auto
  wp_apply wp_ElectionSafety p s $$ [Hs]
  · iexact Hs
  try wp_auto
  cases hES : s.electionSafety
  · try wp_auto
    wp_apply wp_slice_literal (V := GoString) [go!"ElectionSafety"]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    ipersist Hsl
    iapply HΦ
    unfold violated; simp only [hES, Bool.not_false, ↓reduceIte]
    imodintro; iunfold strsRO; iframe Hsl; ipureintro; intro h; cases h
  try wp_auto
  wp_apply wp_OneVotePerTerm p s $$ [Hs]
  · iexact Hs
  try wp_auto
  cases hOV : s.oneVotePerTerm
  · try wp_auto
    wp_apply wp_slice_literal (V := GoString) [go!"OneVotePerTerm"]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    ipersist Hsl
    iapply HΦ
    unfold violated; simp only [hES, hOV, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    imodintro; iunfold strsRO; iframe Hsl; ipureintro; intro h; cases h
  try wp_auto
  ihave %Hvl := strsRO_len _ _ $$ HViol
  have hv : violated s = s.viol := by
    unfold violated; simp only [hES, hOV, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hv]
  try wp_auto
  by_cases h0 : g.Viol'.len = W64 0
  · rw [decide_eq_true h0]
    have hnil : s.viol = [] := by
      rw [h0, sint_zero] at Hvl; exact List.eq_nil_of_length_eq_zero (by omega)
    try wp_auto
    iapply HΦ
    rw [hnil]
    imodintro
    iframe; isplitl
    · iapply Init0_strsNil
    · ipureintro; intro _; rfl
  · rw [decide_eq_false h0]
    try wp_auto
    iapply HΦ
    imodintro
    iframe HViol
    ipureintro; intro hn; rw [hn] at Hvl; exfalso; apply h0; simp at Hvl; word

end proof

end AntCheck
end EtcdGrove
end Perennial
