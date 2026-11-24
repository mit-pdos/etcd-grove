/-
`h.evaluateConditions(ctx, name, d, data)` (`union.go`): the named chain authorizer's evaluation
of the well-formed `d` (that fits `strings.Join` with names of at most `authzNameMax` bytes, as
the authorizers' `ecOk` asks) (anything), or `d`'s failure decision if there is none. Lean-first (no Rocq
counterpart).
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
abbrev unionAuthzHandler.evaluateConditions.spec : Prop :=
  ∀ (h : unionAuthzHandler) (ctx : GoInterface) (name : GoString) (d : ConditionsAwareDecision) (data : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.union ∗ isUnionAuthz h ∗ isWFDecisionFit authzNameMax d }}
    (App (App (App (App (Val (h @!! unionAuthzHandler.ty @!! go!"evaluateConditions")) (Val #ctx)) (Val #name))
      (Val #d)) (Val #data))
  {{ (dec : w64) (r : GoString) (e : GoInterface), RET (PairV (PairV #dec #r) #e); True }}

end spec

end union
end EtcdGrove
end Perennial
