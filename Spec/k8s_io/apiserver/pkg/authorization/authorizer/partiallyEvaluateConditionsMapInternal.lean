/-
`partiallyEvaluateConditionsMapInternal(ctx, c, data, fn)` (`evaluate.go`): a well-formed
leaf decision (depth `0`), for conditions and a partial evaluation function that can be called. Lean-first (no Rocq
counterpart).
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
abbrev partiallyEvaluateConditionsMapInternal.spec : Prop :=
  ∀ (ctx : GoInterface) (c : ConditionsMap) (dn no al : List GoInterface) (data : GoInterface)
    (f : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer ∗ isConditionsMap c dn no al ∗ maybeEvalFnOk f }}
    (App (App (App (App (Val (@! partiallyEvaluateConditionsMapInternal)) (Val #ctx)) (Val #c))
      (Val #data)) (Val #f))
  {{ (d : ConditionsAwareDecision), RET #d; isWFDecisionLe 0 d }}

end spec

end authorizer
end EtcdGrove
end Perennial
