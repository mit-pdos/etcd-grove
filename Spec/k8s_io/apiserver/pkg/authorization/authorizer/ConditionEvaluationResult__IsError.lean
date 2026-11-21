/-
`r.IsError()` (`evaluate.go`): a test of the result type. Lean-first (no Rocq counterpart).
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
abbrev ConditionEvaluationResult.IsError.spec : Prop :=
  ∀ (r : ConditionEvaluationResult),
  {{ (True : IProp GF) }}
    (App (Val (r @!! ConditionEvaluationResult.ty @!! go!"IsError")) (Val #()))
  {{ RET #(decide (r.resultType' = W64 3)); True }}

end spec

end authorizer
end EtcdGrove
end Perennial
