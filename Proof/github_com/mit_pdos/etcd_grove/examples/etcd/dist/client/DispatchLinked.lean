/- Lean-first (no Rocq counterpart).

# `etcd/dist/client`: the full dispatch, linked (F8, `notes/etcd-dist-plan.md` §27.3)

The orchestrator machine's and the client machine's entry points (`clientProg`, `nodeProg`) over every workload
kind, their callees' proofs linked:
- `wp_OrchestratorFull : Orchestrator.spec`: `Orchestrator`, `MainDeployment`, `MainReady` (F8's proofs) with the
  deployment's functions (`deployment`'s `Link`) and every arm's linked workload: kv M1's (`MainReady.wp_proofKv`,
  `RunKV`, `kvremote.wp_Orch`), watch `wp_RunWatch` (N10a, `WatchLinked`), cache `wp_RunCache` (F6, `CacheLinked`),
  compact `wp_RunCompact` (F5, `CompactLinked`), putget and durable `wp_RunPutGet`/`wp_RunDurable` (N9a,
  `KVWorkLinked`), the lease workloads `wp_RunLeaseRead`/`wp_RunLeaseCatchup`/`wp_RunLeaseExpiry` (F2/F7,
  `Results`), auth `wp_MainReadyAuth` (F7 S14, `RunAuthLinked`: `RunAuth` over the authd interim contracts and the
  `Auth_*` admin axioms), authLease `wp_RunAuthLease` (F7 fork, `RunAuthLeaseLinked`: `RunAuthLease` over the
  authd interim contracts, the `Lease_*On_dist` ones among them).
- `wp_NodeDeploymentFull : NodeDeployment.spec`: `NodeDeployment`, `NodeMain` (F8's proofs) with the kv arm M1's
  (`NodeMain.wp_proofKv`, `kvremote.wp_Node`), the writer arm `wp_NodeMainWatch` (N10a, `WatchLinked`) and the auth
  arm `wp_NodeMainAuth` (F7 S13, `PrincipalsLinked`: the principal machines, over the authd interim contracts).

No hypothesis, no `sorry`; the axioms are the workloads' interim contracts (`#print axioms` below).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Rotate
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunKV
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.MainReady
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.MainDeployment
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Orchestrator
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.NodeMain
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.NodeDeployment
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.WatchLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.CacheLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.CompactLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.KVWorkLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Results
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.PrincipalsLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunAuthLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunAuthLeaseLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Link

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Net client etcd_dist_client
open github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote

section links
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [etcdstart_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [rem_sem : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [NaInvG GF]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.membership.Assumptions] [_root_.Perennial.sort.Assumptions]
  [_root_.Perennial.crypto.sha1.Assumptions] [encoding.binary.Assumptions]

/-- **Workload `j`'s orchestrator machine, of any workload** (`Orchestrator.spec`; see the file header). -/
theorem wp_OrchestratorFull : Orchestrator.spec (GF := GF) (hG := hG) :=
  Orchestrator.wp_proof
    (MainDeployment.wp_proof wp_WellFormed Deployment.wp_Endpoints
      (MainReady.wp_proof wp_NodeCount
        (by
          intro π ρ
          exact MainReady.wp_proofKv _ wp_NodeCount
            (RunKV.wp_proof _ (fun nodes ns ops =>
              EtcdGrove.kvremote.wp_Orch (ρ := ρ) nodes ns ops (W64 120000000000))))
        wp_RunWatch wp_RunCache wp_RunCompact wp_RunPutGet wp_RunDurable
        wp_RunLeaseRead wp_RunLeaseCatchup wp_RunLeaseExpiry wp_MainReadyAuth wp_RunAuthLease))

/-- **The `n`-th client machine, of any workload** (`NodeDeployment.spec`; see the file header). -/
theorem wp_NodeDeploymentFull [ThreadBoundLe GF (2 ^ 30)] : NodeDeployment.spec (GF := GF) (hG := hG) :=
  NodeDeployment.wp_proof wp_WellFormed Deployment.wp_Endpoints Deployment.wp_Node
    (NodeMain.wp_proof wp_NodeCount
      (by
        intro π ρ
        exact NodeMain.wp_proofKv _ wp_NodeCount Rotate.wp_proof (EtcdGrove.kvremote.wp_Node (ρ := ρ)))
      wp_NodeMainWatch wp_NodeMainAuth)

end links

end etcd_dist
end EtcdGrove
end Perennial

end
