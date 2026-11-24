/-
Lean-first (no Rocq counterpart). #33 S3b W1 (2026-11-23): the proof of `Recovered` (B 155-157).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Recovered
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__term
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__vote
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__commit
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__lastIndex
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__lastTerm
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem Recovered.wp_proof (wp_term : Event.term.spec (GF := GF) (hG := hG))
    (wp_vote : Event.vote.spec (GF := GF) (hG := hG))
    (wp_commit : Event.commit.spec (GF := GF) (hG := hG))
    (wp_lastIndex : Event.lastIndex.spec (GF := GF) (hG := hG))
    (wp_lastTerm : Event.lastTerm.spec (GF := GF) (hG := hG))
    (wp_TermAt : TermAt.spec (GF := GF) (hG := hG)) :
    Recovered.spec (GF := GF) (hG := hG) := by
  intro e ev t v c ll l b
  wp_start as ⟨#He, #Hl, %Hb⟩
  ihave %Hll := logRO_len _ _ $$ Hl
  unfold recovered at Hb
  wp_auto
  -- `ev.term() == t`
  obtain ⟨x1, hx1, ht1, hf1⟩ := andM_ok Hb
  obtain ⟨y1, hy1, rfl⟩ := fieldEq_ok hx1
  wp_apply wp_term e ev y1 $$ [He] as %u1 %Hu1
  · iframe He; ipureintro; exact hy1
  try wp_auto
  rw [decide_w64_eq, Hu1]
  by_cases c1 : y1 = sint.Z t
  case neg =>
    rw [decide_eq_false c1]
    try wp_auto
    rw [hf1 (by simp [c1])]
    iapply HΦ; ipureintro; trivial
  rw [decide_eq_true c1]
  have Hb := ht1 (by simp [c1])
  try wp_auto
  -- `ev.vote() == v`
  obtain ⟨x2, hx2, ht2, hf2⟩ := andM_ok Hb
  obtain ⟨y2, hy2, rfl⟩ := fieldEq_ok hx2
  wp_apply wp_vote e ev y2 $$ [He]
  · iframe He; ipureintro; exact hy2
  try wp_auto
  by_cases c2 : y2 = v
  case neg =>
    rw [decide_eq_false c2]
    try wp_auto
    rw [hf2 (by simp [c2])]
    iapply HΦ; ipureintro; trivial
  rw [decide_eq_true c2]
  have Hb := ht2 (by simp [c2])
  try wp_auto
  -- `ev.commit() == c`
  obtain ⟨x3, hx3, ht3, hf3⟩ := andM_ok Hb
  obtain ⟨y3, hy3, rfl⟩ := fieldEq_ok hx3
  wp_apply wp_commit e ev y3 $$ [He] as %u3 %Hu3
  · iframe He; ipureintro; exact hy3
  try wp_auto
  rw [decide_w64_eq, Hu3]
  by_cases c3 : y3 = sint.Z c
  case neg =>
    rw [decide_eq_false c3]
    try wp_auto
    rw [hf3 (by simp [c3])]
    iapply HΦ; ipureintro; trivial
  rw [decide_eq_true c3]
  have Hb := ht3 (by simp [c3])
  try wp_auto
  -- `ev.lastIndex() == len(l)`
  obtain ⟨x4, hx4, ht4, hf4⟩ := andM_ok Hb
  obtain ⟨y4, hy4, rfl⟩ := fieldEq_ok hx4
  wp_apply wp_lastIndex e ev y4 $$ [He] as %u4 %Hu4
  · iframe He; ipureintro; exact hy4
  try wp_auto
  rw [decide_w64_eq, Hu4, Hll]
  by_cases c4 : y4 = l.length
  case neg =>
    rw [decide_eq_false c4]
    try wp_auto
    rw [hf4 (by simp [c4])]
    iapply HΦ; ipureintro; trivial
  rw [decide_eq_true c4]
  have Hb := ht4 (by simp [c4])
  try wp_auto
  -- `ev.lastTerm() == TermAt(l, len(l))`
  obtain ⟨y5, hy5, rfl⟩ := fieldEq_ok Hb
  wp_apply wp_lastTerm e ev y5 $$ [He] as %u5 %Hu5
  · iframe He; ipureintro; exact hy5
  try wp_auto
  wp_apply wp_TermAt ll l ll.len $$ [Hl] as %r %Hr
  · iexact Hl
  try wp_auto
  rw [decide_w64_eq, Hu5, Hr, Hll]
  have : decide (y5 = termAt l l.length) = (y5 == termAt l l.length) := by
    by_cases h : y5 = termAt l l.length <;> simp [h]
  rw [this]
  iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
