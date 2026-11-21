/-
`ConditionEvaluationResultError(err)` (`evaluate.go`): an error result (with a fresh error for a
`nil` one). Lean-first (no Rocq counterpart).
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
abbrev ConditionEvaluationResultError.spec : Prop :=
  ∀ (e : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer ∗
      utilerrors.errTreeOrNil e }}
    (App (Val (@! ConditionEvaluationResultError)) (Val #e))
  {{ (e' : GoInterface), RET #(ConditionEvaluationResult.mk (W64 3) e'); utilerrors.errTreeOrNil e' }}

end spec

end authorizer
end EtcdGrove
end Perennial
