/-
Lean-first (no Rocq counterpart). #33 S3b W1 (2026-11-23): the proof of `State.queued` (B 441, 452).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__queued
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__by
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Init0

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

theorem State.queued.wp_proof (wp_by : Event.by.spec (GF := GF) (hG := hG)) :
    State.queued.spec (GF := GF) (hG := hG) := by
  intro p s n e ev q
  wp_start as ⟨#Hs, #He, %Hq⟩
  obtain ⟨Hn0, Hlt, Hq⟩ := Hq
  unfold State.queued at Hq
  obtain ⟨by_, hby, Hq⟩ := bind_ok Hq
  wp_auto
  wp_apply wp_by e ev by_ $$ [He]
  · iframe He; ipureintro; exact hby
  try wp_auto
  by_cases hr : by_ = go!"recv"
  · subst hr
    simp only [beq_self_eq_true, ite_true, pure_ok, Except.ok.injEq] at Hq
    subst Hq
    ihave #Hs' := Hs
    iunfold stateRO at Hs'
    iNamed Hs'
    iNamed Hf
    iStructNamed Hp
    icases pendingRO_at g.Pending' s.pending n ⟨Hn0, by rw [HWf.len_pending]; exact Hlt⟩ $$ HPending with ⟨%pv, #Hpa, #Hpm⟩
    wp_auto
    wp_apply wp_load_at _ _ pv Hn0 $$ [Hpa]
    · iexact Hpa
    try wp_auto
    iapply HΦ
    iunfold qitemRO
    iframe He Hpm
  · rw [decide_eq_false hr]
    simp only [beq_iff_eq, hr, ite_false, pure_ok, Except.ok.injEq] at Hq
    subst Hq
    try wp_auto
    iapply HΦ
    iunfold qitemRO
    iframe He
    iapply Init0_msgsNil

end proof

end AntCheck
end EtcdGrove
end Perennial
