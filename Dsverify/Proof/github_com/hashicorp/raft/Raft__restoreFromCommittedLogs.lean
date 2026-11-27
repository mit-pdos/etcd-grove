/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__restoreFromCommittedLogs.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).restoreFromCommittedLogs`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__restoreFromCommittedLogs

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

theorem github_com.hashicorp.raft.Raft.restoreFromCommittedLogs.wp_proof :
    github_com.hashicorp.raft.Raft.restoreFromCommittedLogs.spec (GF := GF) (hG := hG) := by
  intro r
  wp_start as #Hrcl
  wp_auto
  wp_end

end proof

end Perennial
