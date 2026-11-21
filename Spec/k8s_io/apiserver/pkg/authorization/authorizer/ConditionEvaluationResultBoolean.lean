/-
`ConditionEvaluationResultBoolean(b)` (`evaluate.go`): true or false. Lean-first (no Rocq
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
abbrev ConditionEvaluationResultBoolean.spec : Prop :=
  ∀ (b : Bool),
  {{ (True : IProp GF) }}
    (App (Val (@! ConditionEvaluationResultBoolean)) (Val #b))
  {{ RET #(ConditionEvaluationResult.mk (if b then W64 1 else W64 2) interface.nil); True }}

end spec

end authorizer
end EtcdGrove
end Perennial
