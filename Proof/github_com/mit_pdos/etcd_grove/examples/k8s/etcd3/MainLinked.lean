/-
`MainCluster`'s callees linked (step 1 of "k8s etcd3 over cluster3" in `notes/k8s-etcd3-plan.md`,
2026-11-06; `k` members since stage A of `notes/k8s-7f6-scope.md`, 2026-11-16), by hand as the k8s
compactor's `MainLinked.lean`: `k8s_etcd3.MainCluster.wp_proof` applied to the linked results of the
driver (its `Link.lean`, generated: `newStore`, `Check`, as `wp_Main` takes them)
and to `startCluster`'s proof over the examples' shared start (`etcdstart`'s and `cluster3`'s
`Link.lean`, as txnlinfaultsN's `MainLinked.lean`; the two mvcc laws its watch registrations take,
`persistent` and `mvccState_reachable`, discharged by their `_law_holds` as the compactor's, 7f-6
stage E); `MainPartition`'s the same, with the cluster's `Partitioner`. `Results.lean` restates them.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MainCluster
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MainPartition
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.startCluster
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.bridgeAddr
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.holdToken
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Link
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiResults

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

/-- **The driver's `startCluster(k)`** (stage A of `notes/k8s-7f6-scope.md`), over the examples'
shared start's linked `Members`, `StartMembers`, `Serve`, cluster3's `StartBridge` and the kubernetes
client's `New`, as txnlinfaultsN's. -/
theorem wp_startCluster [_root_.Perennial.net.FieldAssumptions] [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    EtcdGrove.k8s_etcd3.startCluster.spec (GF := GF) (hG := hG) :=
  EtcdGrove.k8s_etcd3.startCluster.wp_proof etcdstart.wp_Members etcdstart.wp_StartMembers
    etcdstart.wp_Serve kubernetes.wp_New cluster3.wp_StartBridge
    (EtcdGrove.k8s_etcd3.bridgeAddr.wp_proof etcdstart.strconv.wp_FormatUint)
    EtcdGrove.k8s_etcd3.holdToken.wp_proof mvcc.api.mvccApi_names_nonempty_law_holds
    mvcc.api.mvccApi_persistent_law_holds mvcc.api.mvccApi_mvccState_reachable_law_holds
    (fun dir ps h hl => rafthttp.bootCfg_of_le dir ps h (by unfold peersMax; omega))

/-- **The driver's `MainCluster` does not panic** (see the file header;
`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/MainCluster.lean`), under the semantic
premises of its callees' linked results (`Main`'s, and the `k`-member start's). -/
theorem wp_MainCluster [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    EtcdGrove.k8s_etcd3.MainCluster.spec (GF := GF) (hG := hG) :=
  EtcdGrove.k8s_etcd3.MainCluster.wp_proof zap.wp_NewNop wp_startCluster wp_newStore context.wp_ErrAny
    wp_Check

/-- **The driver's `MainPartition` does not panic** (see the file header;
`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/MainPartition.lean`), under the semantic
premises of its callees' linked results (`MainCluster`'s, and the cluster's `Partitioner`). -/
theorem wp_MainPartition [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    EtcdGrove.k8s_etcd3.MainPartition.spec (GF := GF) (hG := hG) :=
  EtcdGrove.k8s_etcd3.MainPartition.wp_proof zap.wp_NewNop wp_startCluster
    cluster3.wp_Partitioner wp_newStore context.wp_ErrAny wp_Check

end results

end k8s_etcd3
end EtcdGrove
end Perennial
