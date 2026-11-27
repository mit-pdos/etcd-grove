/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/leader/Ccf.lean (241f27e).
-/
/-
(stage 4, package leader, shared) `respond` through `*configurationChangeFuture` (promoted through its
embedded `logFuture`), from `deferError.respond.spec`: `appendConfigurationEntry` (a refused change) and
`leaderLoop` (a transfer in progress).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.DeferRespond
public import Dsverify.Proof.github_com.hashicorp.raft.core.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.hashicorp.raft

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- `respond` through `*configurationChangeFuture` (promoted through its embedded `logFuture`). -/
theorem github_com.hashicorp.raft.deferError.respond_ccf
    (wp_respond : github_com.hashicorp.raft.deferError.respond.spec (GF := GF) (hG := hG))
    (f : Loc) (Q : GoInterface → IProp GF) (err : GoInterface) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     ((deferResp ((f.[configurationChangeFuture, go!"logFuture"]).[logFuture, go!"deferError"]) Q ∗ Q err) ∨
      deferDone ((f.[configurationChangeFuture, go!"logFuture"]).[logFuture, go!"deferError"])) }}
    (App (Val (f @!! go.GoType.PointerType configurationChangeFuture.ty @!! go!"respond")) (Val #err))
  {{ RET #(); deferDone ((f.[configurationChangeFuture, go!"logFuture"]).[logFuture, go!"deferError"]) }} := by
  have h := deferError.respond_logFuture wp_respond (f.[configurationChangeFuture, go!"logFuture"]) Q err
  wp_start as Hpre
  wp_method_call
  have e := MethodUnfold.method_unfold (t := go.GoType.PointerType logFuture.ty) (m := go!"respond")
    #(f.[configurationChangeFuture, go!"logFuture"])
  simp only [e] at h
  iapply h $$ [$Hpkg $Hpre] HΦ

end proof

end Perennial
