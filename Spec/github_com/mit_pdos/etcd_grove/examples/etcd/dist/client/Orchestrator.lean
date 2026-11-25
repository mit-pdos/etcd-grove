/-
`client.Orchestrator(d, j)` (`clientProg d j`'s entry point), **kv deployments only** (M1's `KvOnly`):
`MainDeployment` with a `ready` that does nothing. Proved for any precondition `OP` of `Orch`.
The share and `KvOnly` are needed only of a well-formed `d`: the program reads them only after
`deployment.WellFormed` returned `nil` (on a malformed `d` it returns at once).
Lean-first (no Rocq counterpart); N7-kv, M1 (`notes/etcd-dist-n7kv.md`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.KvDefs
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
variable [package_sem : client.Assumptions]

/-- Of a Go value `v` holding `d`, `kv`-only if well formed, from workload `j`'s share if `d` is well
formed, `Orchestrator` does not panic. -/
abbrev Orchestrator.spec (OP : List GoString → w64 → IProp GF) : Prop :=
  ∀ (v : deployment.Deployment) (d : Deployment) (j : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      ⌜(d.WellFormed → KvOnly d) ∧ crypto.fips140.GodebugFips140Off⌝ ∗ deploymentRepr v d ∗ (⌜d.WellFormed⌝ -∗ orchShare OP d j) }}
    (App (App (Val (@! client.Orchestrator)) (Val #v)) (Val #j))
  {{ RET #(); True }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
