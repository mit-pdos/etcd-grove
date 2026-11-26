/-
`Deployment.Endpoints()`: the members' client addresses, in the members' order, in a new slice.
Lean-first (no Rocq counterpart); N7-kv, M1 (`notes/etcd-dist-n7kv.md`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Base
@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : deployment.Assumptions]

/-- Of a Go value `v` holding `d`, `v.Endpoints()` returns a new slice of `d`'s members' client
addresses. -/
abbrev Deployment.Endpoints.spec : Prop :=
  ∀ (v : deployment.Deployment) (d : Deployment),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment ∗
      deploymentRepr v d }}
    (App (Val #(methods deployment.Deployment.ty go!"Endpoints" #v)) (Val #()))
  {{ (sl : GoSlice), RET #sl; sl ↦* d.members.map Member.client }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
