/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__compactLogs.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).compactLogs` (stage 3).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__compactLogs
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__compactLogsWithTrailing
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastLog
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__config

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

theorem github_com.hashicorp.raft.Raft.compactLogs.wp_proof
    (wp_getLastLog : github_com.hashicorp.raft.raftState.getLastLog.spec (GF := GF) (hG := hG))
    (wp_config : github_com.hashicorp.raft.Raft.config.spec (GF := GF) (hG := hG))
    (wp_compactLogsWithTrailing :
      github_com.hashicorp.raft.Raft.compactLogsWithTrailing.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.compactLogs.spec (GF := GF) (hG := hG) :=
  fun r γ rc i x tid => by
  wp_start as ⟨#Hr, #Hcx, #Hlx, %Hx, Htok⟩
  wp_auto
  wp_apply (wp_getLastLog.2 r γ rc i) $$ [$Hr] as %li %lt -
  wp_apply wp_config $$ [$Hr] as %c %Hc
  wp_apply wp_compactLogsWithTrailing r γ rc i x li _ tid $$ [$Hr $Hcx $Hlx $Htok] as %err ⟨%He, Htok⟩
  · ipureintro; exact Hx
  iapply HΦ; iframe; ipureintro; exact He

end proof

end Perennial
