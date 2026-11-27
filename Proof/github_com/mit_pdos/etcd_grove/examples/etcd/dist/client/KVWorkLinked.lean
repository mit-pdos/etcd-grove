/-
**The putget and durable workloads of `examples/etcd/dist/client`, linked** (#50 N9a,
`notes/etcd-dist-plan.md` §23): each `wp_proof` at its callees' linked results, the cross-machine clientv3
calls at the interim axioms `etcd_dist.KV_Put_dist.wp_proof`/`KV_Get_dist.wp_proof` (N2's, reviewed:
`notes/axiom-review/n2-kv-dist.md`) and `Client.Close` at its existing trust-boundary axiom. No new axiom.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunPutGet
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunDurable
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.durableKey
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.durableValue
public import Proof.go_etcd_io.etcd.client.v3.WithPrefix
public import Proof.go_etcd_io.etcd.client.v3.getPrefix
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.newClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.checked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.ended
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVPutDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVGetDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Link
public import Proof.go_uber_org.zap.NewNop
public import Perennial.Proof.context.Link
public import Proof.context.Link
public import Proof.context.WithTimeoutBackground
public import Proof.strconv.Itoa
public import Proof.go_etcd_io.etcd.client.v3.Client__Close

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net
open etcd_dist

section linked
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem wp_newClientKVW : newClient.spec (GF := GF) (hG := hG) :=
  newClient.wp_proof zap.NewNop.wp_proof etcdstart.wp_NewClients

/-- **putget's orchestrator, linked.** -/
theorem wp_RunPutGet : RunPutGet.spec (GF := GF) (hG := hG) :=
  RunPutGet.wp_proof wp_newClientKVW checked.wp_proof ended.wp_proof EtcdGrove.strconv.Itoa.wp_proof
    context.wp_Background context.WithTimeoutBackground.wp_proof context.wp_ErrAny
    EtcdGrove.Client.Close.wp_proof KV_Put_dist.wp_proof KV_Get_dist.wp_proof

/-- **durable's orchestrator, linked.** -/
theorem wp_RunDurable : RunDurable.spec (GF := GF) (hG := hG) :=
  RunDurable.wp_proof wp_newClientKVW checked.wp_proof ended.wp_proof durableKey.wp_proof
    durableValue.wp_proof context.wp_Background context.WithTimeoutBackground.wp_proof context.wp_ErrAny
    (EtcdGrove.WithPrefix.wp_proof EtcdGrove.getPrefix.wp_proof) EtcdGrove.Client.Close.wp_proof
    KV_Put_dist.wp_proof KV_Get_dist.wp_proof

end linked

end etcd_dist_client
end EtcdGrove
end Perennial
