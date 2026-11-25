/-
`client.NodeDeployment(d, n)` (`nodeProg d n`'s entry point), **kv deployments only** (M1's `KvOnly`):
the deployment check, then `NodeMain` of the `n`-th client machine, a `kv` workload's by the premise.
Proved for any precondition `NP` of `Node`; the share is `nodeShare NP d n`.
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

/-- Of a Go value `v` holding a `kv`-only `d`, from the `n`-th client machine's share, `NodeDeployment`
does not panic. -/
abbrev NodeDeployment.spec (NP : w64 → GoString → List GoString → IProp GF) : Prop :=
  ∀ (v : deployment.Deployment) (d : Deployment) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      ⌜KvOnly d ∧ crypto.fips140.GodebugFips140Off⌝ ∗ deploymentRepr v d ∗ nodeShare NP d n }}
    (App (App (Val (@! client.NodeDeployment)) (Val #v)) (Val #n))
  {{ RET #(); True }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
