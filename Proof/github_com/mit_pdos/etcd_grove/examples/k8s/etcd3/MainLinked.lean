/-
`MainCluster`'s callees linked (step 1 of "k8s etcd3 over cluster3" in `notes/k8s-etcd3-plan.md`,
2026-11-06), by hand as the k8s compactor's `MainLinked.lean`: `k8s_etcd3.MainCluster.wp_proof`
applied to the linked results of the driver (its `Link.lean`, generated: `seed`, `Check`, the
contract's callees, as `wp_Main` takes them), of the three-member cluster (`cluster3`'s `Link.lean`)
and to `clusterConfig`'s proof; `MainPartition`'s the same, with the cluster's `Partitioner`
(step 2, 2026-11-07). `Results.lean` restates them.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MainCluster
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MainPartition
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.clusterConfig
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Link

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]
variable [NaInvG GF]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [ctxDescs : EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]

theorem wp_clusterConfig : EtcdGrove.k8s_etcd3.clusterConfig.spec (GF := GF) (hG := hG) :=
  EtcdGrove.k8s_etcd3.clusterConfig.wp_proof

/-- **The driver's `MainCluster` does not panic** (see the file header;
`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/MainCluster.lean`), under the semantic
premises of its callees' linked results (`Main`'s, and the three-member cluster's). -/
theorem wp_MainCluster [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    EtcdGrove.k8s_etcd3.MainCluster.spec (GF := GF) (hG := hG) :=
  EtcdGrove.k8s_etcd3.MainCluster.wp_proof zap.wp_NewNop wp_clusterConfig cluster3.wp_StartCluster
    kubernetes.wp_New wp_seed wp_noStreaming k8s.wp_New k8s.wp_NewDefaultLeaseManagerConfig wp_newObj
    runtime.wp_Encode codec.wp_Encode versioner.wp_UpdateObject versioner.wp_PrepareObjectForStorage
    versioner.wp_ObjectResourceVersion versioner.wp_ParseResourceVersion
    identity.wp_TransformFromStorage identity.wp_TransformToStorage decoder.wp_Decode
    runtime.wp_SetZeroValue Obj.wp_GetUID Obj.wp_GetResourceVersion wp_Check

/-- **The driver's `MainPartition` does not panic** (see the file header;
`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/MainPartition.lean`), under the semantic
premises of its callees' linked results (`MainCluster`'s, and the cluster's `Partitioner`). -/
theorem wp_MainPartition [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    EtcdGrove.k8s_etcd3.MainPartition.spec (GF := GF) (hG := hG) :=
  EtcdGrove.k8s_etcd3.MainPartition.wp_proof zap.wp_NewNop wp_clusterConfig cluster3.wp_StartCluster
    cluster3.wp_Partitioner kubernetes.wp_New wp_seed wp_noStreaming k8s.wp_New k8s.wp_NewDefaultLeaseManagerConfig
    wp_newObj runtime.wp_Encode codec.wp_Encode versioner.wp_UpdateObject
    versioner.wp_PrepareObjectForStorage versioner.wp_ObjectResourceVersion
    versioner.wp_ParseResourceVersion identity.wp_TransformFromStorage identity.wp_TransformToStorage
    decoder.wp_Decode runtime.wp_SetZeroValue Obj.wp_GetUID Obj.wp_GetResourceVersion wp_Check

end results

end k8s_etcd3
end EtcdGrove
end Perennial
