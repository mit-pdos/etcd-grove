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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : deployment.Assumptions]

/-- `memberIDs(v)`, of a value `v` holding the deployment `d`, returns a fresh slice of the
members' ids `d.ids` (`membership.NewMember`'s, of each member's peer URL `http://Peer` and the
token). The fips140 setting off: `NewMember`'s premise. -/
abbrev deployment.memberIDs.spec : Prop :=
  ∀ (v : deployment.Deployment) (d : Deployment),
  crypto.fips140.GodebugFips140Off →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment ∗ deploymentRepr v d }}
    (App (Val (@! deployment.memberIDs)) (Val #v))
  {{ (sl : GoSlice), RET #sl; sl ↦* d.ids }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
