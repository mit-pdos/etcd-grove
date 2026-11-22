/-
`z.ConditionsAwareAuthorize(ctx, a)` (`authz.go`): a well-formed decision at most `z.depth` deep,
for `z.depth < 2 ^ 63 - 1` (an authorizer's decision, `caaOk`). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.authorization.union.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.authz.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_authz

open Iris Iris.BI k8s_io.apiserver.pkg.authorization.authorizer k8s_io.apiserver.pkg.authorization.union github_com.mit_pdos.etcd_grove.examples.k8s.authz EtcdGrove.authorizer EtcdGrove.union

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.authz.Assumptions]

/-- See the file header. -/
abbrev arbAuthorizer.ConditionsAwareAuthorize.spec : Prop :=
  ∀ (z : arbAuthorizer) (ctx a : GoInterface), uint.nat z.depth' < 2 ^ 63 - 1 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.authz }}
    (App (App (Val (z @!! arbAuthorizer.ty @!! go!"ConditionsAwareAuthorize")) (Val #ctx)) (Val #a))
  {{ (d : ConditionsAwareDecision), RET #d; isWFDecisionLe (uint.nat z.depth') d }}

end spec

end k8s_authz
end EtcdGrove
end Perennial
