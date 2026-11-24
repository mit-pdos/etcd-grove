/-
`deployment.memberIDs(d)`: the member ids etcd computes for the cluster.
Lean-first (no Rocq counterpart); etcd_safe's deployment check (`notes/etcd-dist-plan.md`, D2).
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

/-- `memberIDs(v)`, of a value `v` holding the deployment `d`, returns a fresh slice of ids, the
members' ids `d.ids` (`membership.NewMember`'s, of each member's peer URL `http://Peer` and the token)
when every peer address is valid (`Net.addrOk`: the URL is then rendered as `http://Peer`). The fips140 setting off: `NewMember`'s premise. -/
abbrev deployment.memberIDs.spec : Prop :=
  ∀ (v : deployment.Deployment) (d : Deployment),
  crypto.fips140.GodebugFips140Off →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment ∗ deploymentRepr v d }}
    (App (Val (@! deployment.memberIDs)) (Val #v))
  {{ (sl : GoSlice) (ids : List w64), RET #sl; sl ↦* ids ∗
      ⌜(∀ m ∈ d.members, Net.addrOk m.peer = true) → ids = d.ids⌝ }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
