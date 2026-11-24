/-
`z.EvaluateConditions(ctx, d, data)` (`authz.go`): some decision word, reason and error, for a
well-formed `d` that fits `strings.Join` (`isWFDecisionFit`, as `ecOk` gives it) (a lie, or the library's evaluation with arbitrary condition results). Lean-first
(no Rocq counterpart).
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
abbrev arbAuthorizer.EvaluateConditions.spec : Prop :=
  ∀ (z : arbAuthorizer) (ctx : GoInterface) (d : ConditionsAwareDecision) (data : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.authz ∗ isWFDecisionFit authzNameMax d }}
    (App (App (App (Val (z @!! arbAuthorizer.ty @!! go!"EvaluateConditions")) (Val #ctx)) (Val #d))
      (Val #data))
  {{ (dec : w64) (r : GoString) (e : GoInterface), RET (PairV (PairV #dec #r) #e); True }}

end spec

end k8s_authz
end EtcdGrove
end Perennial
