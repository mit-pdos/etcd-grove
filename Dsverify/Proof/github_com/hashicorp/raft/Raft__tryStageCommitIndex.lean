/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__tryStageCommitIndex.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).tryStageCommitIndex`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__tryStageCommitIndex

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

theorem github_com.hashicorp.raft.Raft.tryStageCommitIndex.wp_proof :
    github_com.hashicorp.raft.Raft.tryStageCommitIndex.spec (GF := GF) (hG := hG) :=
  fun r γ rc i c => by
  wp_start as #Hr
  ihave #Himm := isRaft_imm r γ rc i $$ Hr
  unfold raftImm
  icases Himm with ⟨-, -, -, -, -, #Hrcl⟩
  wp_auto
  wp_end
