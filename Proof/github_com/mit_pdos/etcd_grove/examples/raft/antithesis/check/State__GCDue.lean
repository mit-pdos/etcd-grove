/-
Lean-first (no Rocq counterpart). #33 S3b W6 (2026-11-23): the proof of `State.GCDue` (B 711).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__GCDue
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Garbage
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__OldVotes
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__StaleLed
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.W6Laws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Parts

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

theorem State.GCDue.wp_proof
    (wp_Garbage : State.Garbage.spec (GF := GF) (hG := hG))
    (wp_OldVotes : State.OldVotes.spec (GF := GF) (hG := hG))
    (wp_StaleLed : State.StaleLed.spec (GF := GF) (hG := hG)) :
    State.GCDue.spec (GF := GF) (hG := hG) := by
  intro p s b
  wp_start as ⟨#Hs, %HBd, %Ho⟩
  obtain ⟨bb, EE, hbb, HW⟩ := HBd
  unfold numBound at hbb
  unfold State.gcDue at Ho
  obtain ⟨gs, hgs, Ho⟩ := bind_ok Ho
  obtain ⟨vs, hvs, Ho⟩ := bind_ok Ho
  simp only [pure_ok, Except.ok.injEq] at Ho
  have hgl : gs.length ≤ 2 * bb := Nat.le_trans (W6Laws.filterM_length_le hgs) HW.msgs_len
  have hvl : vs.length ≤ bb := Nat.le_trans (W6Laws.filterM_length_le hvs) HW.votes_len
  wp_auto
  wp_apply wp_Garbage p s gs $$ [Hs] as %gsl #Hgs
  · iframe Hs; ipureintro; exact hgs
  ihave %Hgsl := factsRO_len _ _ $$ Hgs
  try wp_auto
  wp_apply wp_OldVotes p s vs $$ [Hs] as %vsl #Hvs
  · iframe Hs; ipureintro; exact hvs
  ihave %Hvsl := votesRO_len _ _ $$ Hvs
  try wp_auto
  have hsum : sint.Z (gsl.len + vsl.len) = gs.length + vs.length := by
    rw [sint_add (by omega) (by omega), Hgsl, Hvsl]
  rw [hsum, show sint.Z (W64 32) = 32 from rfl]
  subst Ho
  by_cases hge : (32 : Int) ≤ gs.length + vs.length
  · rw [decide_eq_true hge]
    have : decide (gs.length + vs.length ≥ gcBatch) = true := by
      unfold gcBatch; apply decide_eq_true; omega
    rw [this, Bool.true_or]
    try wp_auto
    iapply HΦ; ipureintro; trivial
  rw [decide_eq_false hge]
  have : decide (gs.length + vs.length ≥ gcBatch) = false := by
    unfold gcBatch; apply decide_eq_false; omega
  rw [this, Bool.false_or]
  try wp_auto
  wp_apply wp_StaleLed p s $$ [Hs] as %ssl #Hss
  · iexact Hs
  ihave %Hssl := intsRO_len _ _ $$ Hss
  try wp_auto
  rw [decide_w64_eq, Hssl, sint_zero]
  have : (s.staleLed.length != 0) = !decide ((s.staleLed.length : Int) = 0) := by
    by_cases h : s.staleLed.length = 0 <;> simp [h]
  rw [this]
  try wp_auto
  iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
