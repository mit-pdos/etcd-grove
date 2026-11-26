/-
`client.NodeDeployment(d, n)` (`nodeProg d n`'s entry point): the deployment check, then `NodeMain` of the
`n`-th client machine.
- `NodeDeployment.spec` (F8, `notes/etcd-dist-plan.md` §27.3): any deployment, from `nodeShareF d n`
  (`client/Shares.lean`), the machine's level token and its pure facts (`nodeMachinePure`).
- `NodeDeployment.specKv` (M1): **kv deployments only** (`KvOnly`), for any precondition `NP` of `Node`; the
  share is `nodeShare NP d n`.
The share and `KvOnly` are needed only of a well-formed `d`: the program reads them only after
`deployment.WellFormed` returned `nil` (on a malformed `d` it returns at once).
Lean-first (no Rocq counterpart); N7-kv, M1 (`notes/etcd-dist-n7kv.md`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.KvDefs
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.NodeMain
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

/-- Of a Go value `v` holding `d`, `kv`-only if well formed, from the `n`-th client machine's share if
`d` is well formed, `NodeDeployment` does not panic. -/
abbrev NodeDeployment.specKv (NP : w64 → GoString → List GoString → IProp GF) : Prop :=
  ∀ (v : deployment.Deployment) (d : Deployment) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      ⌜(d.WellFormed → KvOnly d) ∧ crypto.fips140.GodebugFips140Off⌝ ∗ deploymentRepr v d ∗ (⌜d.WellFormed⌝ -∗ nodeShare NP d n) }}
    (App (App (Val (@! client.NodeDeployment)) (Val #v)) (Val #n))
  {{ RET #(); True }}

end spec

section specFull
open Net client etcd_dist_client
open github_com.mit_pdos.etcd_grove.examples.lib.remote

variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : client.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]


/-- Of a Go value `v` holding `d`, from the `n`-th client machine's share if `d` is well formed, the machine's
level token and its pure facts, `NodeDeployment` does not panic. -/
abbrev NodeDeployment.spec : Prop :=
  ∀ [π : NetProtoGS] [ρ : RemoteGS] (v : deployment.Deployment) (d : Deployment) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      ⌜crypto.fips140.GodebugFips140Off ∧ nodeMachinePure (GF := GF)⌝ ∗ levelTok 0 ∗ deploymentRepr v d ∗
      (⌜d.WellFormed⌝ -∗ nodeShareF (Gg := hG.goose_globalGS) d n) }}
    (App (App (Val (@! client.NodeDeployment)) (Val #v)) (Val #n))
  {{ RET #(); True }}

end specFull

end etcd_dist
end EtcdGrove
end Perennial
