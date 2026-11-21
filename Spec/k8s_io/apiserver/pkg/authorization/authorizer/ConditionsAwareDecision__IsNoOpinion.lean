/-
`d.IsNoOpinion()` (`conditions.go`): whether `d` is an unconditional NoOpinion (a test of the type
tag). Lean-first (no Rocq counterpart).
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
abbrev ConditionsAwareDecision.IsNoOpinion.spec : Prop :=
  ∀ (d : ConditionsAwareDecision),
  {{ (True : IProp GF) }}
    (App (Val (d @!! ConditionsAwareDecision.ty @!! go!"IsNoOpinion")) (Val #()))
  {{ RET #(decide (d.decisionType' = W64 12)); True }}

end spec

end authorizer
end EtcdGrove
end Perennial
