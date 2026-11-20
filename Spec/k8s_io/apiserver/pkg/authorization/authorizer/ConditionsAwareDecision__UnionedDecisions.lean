/-
`d.UnionedDecisions()` (`conditions.go`): an iterator over the (name, sub-decision) pairs of `d`'s
children slice. Lean-first (no Rocq counterpart).
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
abbrev ConditionsAwareDecision.UnionedDecisions.spec : Prop :=
  ∀ (d : ConditionsAwareDecision) (nds : List namedConditionsAwareDecision),
  {{ (d.union'.inner' ↦*□ nds : IProp GF) }}
    (App (Val (d @!! ConditionsAwareDecision.ty @!! go!"UnionedDecisions")) (Val #()))
  {{ (f : GoFunc), RET #f;
      seq2Ok (GF := GF) f (nds.map (fun nd => (nd.conditionalAuthorizerName', nd.d'))) }}

end spec

end authorizer
end EtcdGrove
end Perennial
