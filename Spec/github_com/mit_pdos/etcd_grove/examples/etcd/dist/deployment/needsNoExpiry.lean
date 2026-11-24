/-
`deployment.needsNoExpiry(k)`: whether a workload of kind `k` needs that no lease expires.
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

/-- `needsNoExpiry(k)` is `kindNeedsNoExpiry k`. -/
abbrev deployment.needsNoExpiry.spec : Prop :=
  ∀ (k : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment }}
    (App (Val (@! deployment.needsNoExpiry)) (Val #k))
  {{ RET #(kindNeedsNoExpiry k); True }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
