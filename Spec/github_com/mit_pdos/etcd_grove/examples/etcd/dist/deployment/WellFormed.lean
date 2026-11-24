/-
`deployment.WellFormed(d)`: every machine's first step; `nil` only for a well-formed deployment.

**The triple:** of a Go value `v` holding the deployment `d` (`deploymentRepr`, read-only),
`WellFormed(v)` returns an error, `nil` only if `d.WellFormed` (`DeploymentDefs.lean`: `d` encodes a
well-formed typed deployment). Soundness only: a well-formed deployment may be refused (it is not:
`TestWellFormed`, but the spec does not say so). The member ids are `membership.NewMember`'s (`memberId`, its proved
spec). The fips140 setting off: `NewMember`'s premise.
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

/-- See the file header. -/
abbrev deployment.WellFormed.spec : Prop :=
  ∀ (v : deployment.Deployment) (d : Deployment),
  crypto.fips140.GodebugFips140Off →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment ∗ deploymentRepr v d }}
    (App (Val (@! deployment.WellFormed)) (Val #v))
  {{ (err : GoInterface), RET #err; ⌜err = interface.nil → d.WellFormed⌝ }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
