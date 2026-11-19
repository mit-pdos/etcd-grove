/-
The proof of `arbErr.spec` (`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/authz/arbErr.lean`).
Lean-first (no Rocq counterpart).
-/
module

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
  sorry

end proof

end k8s_authz
end EtcdGrove
end Perennial
