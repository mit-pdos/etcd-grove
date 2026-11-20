/-
`arbEval(ctx, cond, data)` (`authz.go`): some boolean and error. Lean-first (no Rocq counterpart).
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
abbrev arbEval.spec : Prop :=
  ∀ (ctx cond data : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.authz }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbEval)) (Val #ctx)) (Val #cond)) (Val #data))
  {{ (b : Bool) (e : GoInterface), RET (PairV #b #e); True }}

end spec

end k8s_authz
end EtcdGrove
end Perennial
