/-
`client.MainDeployment(d, j, ready)`: the deployment check, then `MainReady` of workload `j`.
- `MainDeployment.spec` (F8, `notes/etcd-dist-plan.md` §27.3): any deployment; the share is `orchShareF d j`
  (`client/Shares.lean`), with the machine's thread token and its pure facts (`orchMachinePure`).
- `MainDeployment.specKv` (M1): **kv deployments only** (`KvOnly`), for any precondition `OP` of `Orch`; the
  share is `orchShare OP d j`.
The share and `KvOnly` are needed only of a well-formed `d`: the program reads them only after
`deployment.WellFormed` returned `nil` (on a malformed `d` it returns at once).
Lean-first (no Rocq counterpart); N7-kv, M1 (`notes/etcd-dist-n7kv.md`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.KvDefs
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.MainReady
@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

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
formed, `MainDeployment` does not panic. -/
abbrev MainDeployment.specKv (OP : List GoString → w64 → IProp GF) : Prop :=
  ∀ (v : deployment.Deployment) (d : Deployment) (j : w64) (ready : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      ⌜(d.WellFormed → KvOnly d) ∧ crypto.fips140.GodebugFips140Off⌝ ∗ deploymentRepr v d ∗ readySpec ready ∗
      (⌜d.WellFormed⌝ -∗ orchShare OP d j) }}
    (App (App (App (Val (@! client.MainDeployment)) (Val #v)) (Val #j)) (Val #ready))
  {{ (r : client.Result), RET #r; True }}

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


/-- Of a Go value `v` holding `d`, from workload `j`'s share if `d` is well formed, the machine's thread token
and its pure facts, `MainDeployment` does not panic. -/
abbrev MainDeployment.spec : Prop :=
  ∀ [π : NetProtoGS] [ρ : RemoteGS]
    -- (F7 S13) the auth arm's (`MainReadyAuth.spec`, `RunAuth.spec`) instances, the boot's (`EtcdBootNCAt`)
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    (v : deployment.Deployment) (d : Deployment) (j : w64) (ready : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      ⌜crypto.fips140.GodebugFips140Off ∧ orchMachinePure (GF := GF)⌝ ∗ threadTok ∗ deploymentRepr v d ∗
      readySpec ready ∗ (⌜d.WellFormed⌝ -∗ orchShareF (Gg := hG.goose_globalGS) d j) }}
    (App (App (App (Val (@! client.MainDeployment)) (Val #v)) (Val #j)) (Val #ready))
  {{ (r : client.Result), RET #r; True }}

end specFull

end etcd_dist
end EtcdGrove
end Perennial
