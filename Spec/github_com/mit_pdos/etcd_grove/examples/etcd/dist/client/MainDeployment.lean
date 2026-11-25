/-
`client.MainDeployment(d, j, ready)`, **kv deployments only** (M1's `KvOnly`): the deployment check, then
`MainReady` of workload `j`, a `kv` workload by the premise. Proved for any precondition `OP` of `Orch`;
the share is `orchShare OP d j`.
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

/-- Of a Go value `v` holding a `kv`-only `d`, from workload `j`'s share, `MainDeployment` does not
panic. -/
abbrev MainDeployment.spec (OP : List GoString → w64 → IProp GF) : Prop :=
  ∀ (v : deployment.Deployment) (d : Deployment) (j : w64) (ready : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      ⌜KvOnly d ∧ crypto.fips140.GodebugFips140Off⌝ ∗ deploymentRepr v d ∗ readySpec ready ∗
      orchShare OP d j }}
    (App (App (App (Val (@! client.MainDeployment)) (Val #v)) (Val #j)) (Val #ready))
  {{ (r : client.Result), RET #r; True }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
