/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/DeferRespond.lean (241f27e).
-/
/-
`(*deferError).respond` through `*logFuture` (promotion), from `deferError.respond.spec` (REPL-4).
-/
module
public import Dsverify.Spec.github_com.hashicorp.raft.deferError__respond
@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.hashicorp.raft
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
/-- `respond` through `*logFuture` (promoted): `deferError.respond.spec` at the embedded `deferError`. -/
theorem github_com.hashicorp.raft.deferError.respond_logFuture
    (wp_respond : github_com.hashicorp.raft.deferError.respond.spec (GF := GF) (hG := hG))
  (f : Loc) (Q : GoInterface → IProp GF) (err : GoInterface) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ ((deferResp (f.[logFuture, go!"deferError"]) Q ∗ Q err) ∨ deferDone (f.[logFuture, go!"deferError"])) }}
    (App (Val (f @!! go.GoType.PointerType logFuture.ty @!! go!"respond")) (Val #err))
  {{ RET #(); deferDone (f.[logFuture, go!"deferError"]) }} := by
  have h := wp_respond (f.[logFuture, go!"deferError"]) Q err
  wp_start as Hpre
  wp_method_call
  have e := MethodUnfold.method_unfold (t := go.GoType.PointerType deferError.ty) (m := go!"respond")
    #(f.[logFuture, go!"deferError"])
  simp only [e] at h
  iapply h $$ [$Hpkg $Hpre] HΦ
end Perennial
