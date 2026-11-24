/-
Lean-first (no Rocq counterpart). #33 S3b W2 (2026-11-23): the proof of `State.SnapEv` (B 647-650).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__SnapEv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__index
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__term
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermAt
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws

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

theorem State.SnapEv.wp_proof
    (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_index : Event.index.spec (GF := GF) (hG := hG))
    (wp_term : Event.term.spec (GF := GF) (hG := hG))
    (wp_TermAt : TermAt.spec (GF := GF) (hG := hG)) :
    State.SnapEv.spec (GF := GF) (hG := hG) := by
  intro p s n e ev o
  wp_start as ⟨#Hs, #He, %Hn, %Hlt, %HBd, %Ho⟩
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp

  icases intsRO_at g.LastApplied' s.lastApplied n ⟨Hn, by rw [HWf.len_lastApplied]; exact Hlt⟩ $$ HLastApplied with ⟨%la, #Hlaa, %Hla⟩
  icases intsRO_at g.CommitIndex' s.commitIndex n ⟨Hn, by rw [HWf.len_commitIndex]; exact Hlt⟩ $$ HCommitIndex with ⟨%ci, #Hcia, %Hci⟩
  icases logsRO_at g.Log' s.log n ⟨Hn, by rw [HWf.len_log]; exact Hlt⟩ $$ HLog with ⟨%lg, #Hlga, #Hlg⟩
  ihave %Hlgl := logRO_len _ _ $$ Hlg
  unfold State.snapEv at Ho
  obtain ⟨c1, hc1, Ho⟩ := bind_ok Ho
  obtain ⟨x1, hx1, ht1, hf1⟩ := andM_ok hc1
  obtain ⟨i1, hi1, hx1⟩ := bind_ok hx1
  simp only [pure_ok, Except.ok.injEq] at hx1
  subst hx1
  wp_auto
  wp_apply wp_index e ev i1 $$ [He] as %ui %Hui
  · iframe He; ipureintro; exact hi1
  try wp_auto
  wp_apply wp_load_at _ _ la Hn $$ [Hlaa]
  · iexact Hlaa
  try wp_auto
  rw [Hui, Hla]
  by_cases h1 : i1 ≤ s.lastApplied[sint.nat n]!
  case neg =>
    rw [decide_eq_false h1]
    rw [hf1 (decide_eq_false h1)] at Ho
    simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  rw [decide_eq_true h1]
  have hx2 := ht1 (decide_eq_true h1)
  obtain ⟨i2, hi2, hx2⟩ := bind_ok hx2
  simp only [pure_ok, Except.ok.injEq] at hx2
  try wp_auto
  wp_apply wp_index e ev i2 $$ [He] as %ui2 %Hui2
  · iframe He; ipureintro; exact hi2
  try wp_auto
  wp_apply wp_load_at _ _ ci Hn $$ [Hcia]
  · iexact Hcia
  try wp_auto
  rw [Hui2, Hci]
  rw [hi1] at hi2; cases hi2
  by_cases h2 : i1 ≤ s.commitIndex[sint.nat n]!
  case neg =>
    rw [decide_eq_false h2]
    rw [← hx2] at Ho
    simp only [h2, decide_false, Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  rw [decide_eq_true h2]
  rw [← hx2] at Ho
  simp only [h2, decide_true, Bool.not_true, Bool.false_eq_true, ite_false] at Ho
  try wp_auto
  wp_apply wp_load_at _ _ lg Hn $$ [Hlga]
  · iexact Hlga
  try wp_auto
  wp_apply wp_index e ev i1 $$ [He] as %ui3 %Hui3
  · iframe He; ipureintro; exact hi1
  try wp_auto
  wp_apply wp_TermAt lg _ ui3 $$ [Hlg] as %r %Hr
  · iexact Hlg
  try wp_auto
  obtain ⟨i3, hi3, Ho⟩ := bind_ok Ho
  rw [hi1] at hi3; cases hi3
  obtain ⟨tt, htt, Ho⟩ := bind_ok Ho
  wp_apply wp_term e ev tt $$ [He] as %ut %Hut
  · iframe He; ipureintro; exact htt
  try wp_auto
  rw [decide_w64_eq, Hr, Hut, Hui3]
  by_cases h3 : termAt s.log[sint.nat n]! i1 = tt
  case neg =>
    rw [decide_eq_false h3]
    have : (termAt s.log[sint.nat n]! i1 != tt) = true := by simpa using h3
    simp only [this, ite_true, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  rw [decide_eq_true h3]
  simp only [h3, bne_self_eq_false, Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at Ho
  subst Ho
  try wp_auto
  wp_apply wp_clone p s $$ [Hs] as %q Hq
  · iexact Hs
  try wp_auto
  iapply HΦ
  iunfold succOwn
  isplitr
  · ipureintro; rfl
  iexact Hq

end proof

end AntCheck
end EtcdGrove
end Perennial
