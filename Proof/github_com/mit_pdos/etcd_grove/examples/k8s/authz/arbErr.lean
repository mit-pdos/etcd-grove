/-
The proof of `arbErr.spec` (`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/authz/arbErr.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apimachinery.pkg.util.errors.ErrTreeOk
public import Perennial.Proof.errors.NewVar
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbErr
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbBool
public import Perennial.Spec.errors.New

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_authz

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer k8s_io.apiserver.pkg.authorization.union github_com.mit_pdos.etcd_grove.examples.k8s.authz EtcdGrove.authorizer EtcdGrove.union

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.authz.Assumptions]

theorem arbErr.wp_proof
    (wp_arbBool : EtcdGrove.k8s_authz.arbBool.spec (GF := GF) (hG := hG))
    (wp_errors_New : _root_.Perennial.errors.New.spec (GF := GF) (hG := hG)) :
    arbErr.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply wp_arbBool as %b _
  cases b
  · wp_auto
    wp_apply _root_.Perennial.errors.wp_New_errorString as %x ⟨#_, #Hx⟩
    (try wp_auto)
    iapply HΦ
    iapply utilerrors.errorString_errTreeOrNil x _
    iexact Hx
  · wp_auto
    iapply HΦ
    iapply utilerrors.errTreeOrNil_nil

end proof

end k8s_authz
end EtcdGrove
end Perennial
