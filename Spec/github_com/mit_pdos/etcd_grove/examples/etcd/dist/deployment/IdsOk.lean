/-
`deployment.IdsOk(d)`: the member ids apart in their low bits (soundness).
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

/-- `IdsOk(v)`, of a value `v` holding the deployment `d`, returns `true` only if its ids pass
`goIdsOk`, when every peer address is valid. The fips140 setting off: `NewMember`'s premise. -/
abbrev deployment.IdsOk.spec : Prop :=
  ∀ (v : deployment.Deployment) (d : Deployment),
  crypto.fips140.GodebugFips140Off →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment ∗ deploymentRepr v d }}
    (App (Val (@! deployment.IdsOk)) (Val #v))
  {{ (b : Bool), RET #b;
      ⌜(∀ m ∈ d.members, Net.addrOk m.peer = true) → b = true → goIdsOk d.ids d.workloads⌝ }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
