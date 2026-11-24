/-
`h.ConditionsAwareAuthorize(ctx, a)` (`union.go`): a well-formed decision (the chain's decisions
in a union builder, up to the first containing an unconditional Allow or Deny), at most one level
deeper than the authorizers' and of at most `authzChainMax` times their size (`caaOk`), with names
of at most `authzNameMax` bytes (`isUnionAuthz`). Lean-first (no Rocq counterpart).
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
abbrev unionAuthzHandler.ConditionsAwareAuthorize.spec : Prop :=
  ∀ (h : unionAuthzHandler) (ctx attrs : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.union ∗ isUnionAuthz h }}
    (App (App (Val (h @!! unionAuthzHandler.ty @!! go!"ConditionsAwareAuthorize")) (Val #ctx)) (Val #attrs))
  {{ (d : ConditionsAwareDecision), RET #d;
      isWFDecisionBnd (authzDepthMax + 1) (authzChainMax * authzSizeMax + 1) authzNameMax d }}

end spec

end union
end EtcdGrove
end Perennial
