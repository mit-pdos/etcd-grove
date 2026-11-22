/-
`f.ConditionsAwareAuthorize(ctx, a)` (`interfaces.go`): the unconditional decision of `f(ctx, a)`,
well-formed. Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authorizer

open Iris Iris.BI k8s_io.apiserver.pkg.authorization.authorizer

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

/-- See the file header. -/
abbrev AuthorizerFunc.ConditionsAwareAuthorize.spec : Prop :=
  ∀ (f : GoFunc) (ctx a : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer ∗ authzFnOk f }}
    (App (App (Val (f @!! AuthorizerFunc.ty @!! go!"ConditionsAwareAuthorize")) (Val #ctx)) (Val #a))
  {{ (d : ConditionsAwareDecision), RET #d; isWFDecisionLe 0 d }}

end spec

end authorizer
end EtcdGrove
end Perennial
