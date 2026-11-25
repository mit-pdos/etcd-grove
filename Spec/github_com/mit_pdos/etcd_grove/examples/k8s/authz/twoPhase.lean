/-
`twoPhase(ctx, a, d, false)` (`authz.go`), for the union handler `a` and a well-formed decision
`d` within the bounds of the union handler's (`unionAuthzHandler.ConditionsAwareAuthorize`: its
`EvaluateConditions` joins reasons, fmt stage 1): returns (C1-C3 hold: the strict check, C3 for an Allow, is not claimed). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.authorization.union.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.authz.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_authz

open Iris Iris.BI k8s_io.apiserver.pkg.authorization.authorizer k8s_io.apiserver.pkg.authorization.union github_com.mit_pdos.etcd_grove.examples.k8s.authz EtcdGrove.authorizer EtcdGrove.union

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.authz.Assumptions]

/-- See the file header. -/
abbrev twoPhase.spec : Prop :=
  ∀ (ctx : GoInterface) (h : unionAuthzHandler) (d : ConditionsAwareDecision) (m : Dec),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.authz ∗ isUnionAuthz h ∗ isDecision d m ∗
      ⌜m.WF ∧ m.depth ≤ authzDepthMax + 1 ∧ m.size ≤ authzChainMax * authzSizeMax + 1⌝ ∗
      decNames authzNameMax d m }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.authz.twoPhase)) (Val #ctx))
      (Val #(interface.mkOk unionAuthzHandler.ty #h))) (Val #d)) (Val #false))
  {{ RET #(); True }}

end spec

end k8s_authz
end EtcdGrove
end Perennial
