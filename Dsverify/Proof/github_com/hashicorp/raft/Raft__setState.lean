/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__setState.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).setState`: clears the leader (`setLeader("", "")`), stores the state
in the state cell, and observes the new state if it changed (the observation's argument
`obsArg` is the caller's, passed through `observe`).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setState
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLeader
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__observe
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getState
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__setState

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto gprot

theorem github_com.hashicorp.raft.Raft.setState.wp_proof
    (wp_setLeader : github_com.hashicorp.raft.Raft.setLeader.spec (GF := GF) (hG := hG))
    (wp_getState : github_com.hashicorp.raft.raftState.getState.spec (GF := GF) (hG := hG))
    (wp_rsSetState : github_com.hashicorp.raft.raftState.setState.spec (GF := GF) (hG := hG))
    (wp_observe : github_com.hashicorp.raft.Raft.observe.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.setState.spec (GF := GF) (hG := hG) := by
  intro r γ rc i st0 st s tid
  wp_start as ⟨#His, Hst, %Hok, Harg, Htok⟩
  ihave #Hcell := isRaft_stateCell r γ rc i $$ His
  wp_auto
  wp_apply wp_setLeader $$ [$Htok] as Htok
  · iframe #
  wp_apply wp_getState.1 $$ [$Hst] as Hst
  · iframe #
  wp_apply wp_rsSetState $$ [$Hst] as Hst
  · iframe #; ipureintro; exact Hok
  wp_if_destruct
  · iapply HΦ; iframe
  · wp_apply wp_observe $$ [$Harg $Htok] as ⟨Harg, Htok⟩
    · iframe #
    iapply HΦ; iframe

end proof

end Perennial
