/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__State.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).State`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__State
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getState

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

open github_com.hashicorp.raft proto

theorem github_com.hashicorp.raft.Raft.State.wp_proof
    (wp_getState : github_com.hashicorp.raft.raftState.getState.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.State.spec (GF := GF) (hG := hG) := by
  intro r γ rc i
  wp_start as #Hr
  ihave #Hsc := isRaft_stateCell r γ rc i $$ Hr
  wp_auto
  wp_apply wp_getState.2 $$ [$Hsc] as %st %Hst
  iapply HΦ
  itrivial

end proof

end Perennial
