/-
`h.EvaluateConditions(ctx, d, data)` (`union.go`): for a well-formed `d` that fits `strings.Join`
with names of at most `authzNameMax` bytes (it joins one reason per child, fmt stage 1), a possible decision of
`d` or its failure decision, whatever the chain's authorizers return (it guards each conditional
child's evaluation with the child's possible decisions). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.authorization.union.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace union

open Iris Iris.BI k8s_io.apiserver.pkg.authorization.authorizer k8s_io.apiserver.pkg.authorization.union EtcdGrove.authorizer

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.union.Assumptions]

/-- See the file header. -/
abbrev unionAuthzHandler.EvaluateConditions.spec : Prop :=
  ∀ (h : unionAuthzHandler) (ctx : GoInterface) (d : ConditionsAwareDecision) (m : Dec) (data : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.union ∗ isUnionAuthz h ∗ isDecision d m ∗ ⌜m.WF ∧ Dec.foldFits authzNameMax m⌝ ∗
      decNames authzNameMax d m }}
    (App (App (App (Val (h @!! unionAuthzHandler.ty @!! go!"EvaluateConditions")) (Val #ctx)) (Val #d))
      (Val #data))
  {{ (dec : w64) (r : GoString) (e : GoInterface), RET (PairV (PairV #dec #r) #e); ⌜m.pd.has dec = true ∨ dec = m.pd.failure⌝ }}

end spec

end union
end EtcdGrove
end Perennial
