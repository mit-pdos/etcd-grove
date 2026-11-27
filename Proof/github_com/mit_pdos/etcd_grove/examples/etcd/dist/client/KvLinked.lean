/-
# `etcd/dist/client`: the kv dispatch, linked (N7-kv, M1)

The orchestrator machine's and the client machine's entry points (`clientProg`, `nodeProg`) of a `kv`-only
deployment, their callees' proofs linked: `wp_OrchestratorKv OP` and `wp_NodeDeploymentKv NP` hold for any
precondition `OP` of `kvremote.Orch` and `NP` of `kvremote.Node` whose schema is given (`Orch.specWith`,
`Node.specWith`: P9's specs of `Orch` and `Node`, §11.3 steps 3-4, are instances). The deployment's
functions are `deployment`'s `Link`. Hand-written (the two schemas are hypotheses until P9's specs land);
M1's theorem (§11.3 step 6) applies these. No axiom and no `sorry`.
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

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI

section links
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.membership.Assumptions] [_root_.Perennial.sort.Assumptions]
  [_root_.Perennial.crypto.sha1.Assumptions] [encoding.binary.Assumptions]

/-- **Workload `j`'s orchestrator machine of a `kv`-only deployment** (`Orchestrator.specKv OP`), from
`Orch`'s schema at `OP`. -/
theorem wp_OrchestratorKv (OP : List GoString → w64 → IProp GF)
    (hOrch : Orch.specWith (GF := GF) (hG := hG) OP) : Orchestrator.specKv (GF := GF) (hG := hG) OP :=
  Orchestrator.wp_proofKv OP
    (MainDeployment.wp_proofKv OP wp_WellFormed Deployment.wp_Endpoints
      (MainReady.wp_proofKv OP wp_NodeCount (RunKV.wp_proof OP hOrch)))

/-- **The `n`-th client machine of a `kv`-only deployment** (`NodeDeployment.specKv NP`), from `Node`'s
schema at `NP`. -/
theorem wp_NodeDeploymentKv (NP : w64 → GoString → List GoString → IProp GF)
    (hNode : Node.specWith (GF := GF) (hG := hG) NP) : NodeDeployment.specKv (GF := GF) (hG := hG) NP :=
  NodeDeployment.wp_proofKv NP wp_WellFormed Deployment.wp_Endpoints Deployment.wp_Node
    (NodeMain.wp_proofKv NP wp_NodeCount Rotate.wp_proof hNode)

end links

end etcd_dist
end EtcdGrove
end Perennial
