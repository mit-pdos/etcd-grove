/-
`Main`'s callees linked (K4 of `notes/k8s-compactor-plan.md`), by hand as `compactwatch`'s
`MainLinked.lean`: `k8s_compactor.Main.wp_proof` applied to the linked results of the examples'
shared start (`etcdstart`'s `Link.lean`), of Kubernetes' compactor (etcd3's `Link.lean`), of `context`, to `ready`, `writer`, `check` and `apiserver` over them, and to the trust-boundary axioms of
`zap.NewNop` and `strconv.Itoa`. `MainPartition` (K6, 2026-11-05; on `k` members since 2026-11-20) likewise, over the
`k`-member start's (`startCluster`, as the k8s etcd3 driver's) and the partitioner's (`cluster3`'s
`Link.lean`). `Results.lean` restates
them.
-/
module

public import Proof.google_golang_org.protobuf.proto.MarshalBootConfChange
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiResults
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.ready
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.writer
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.apiserver
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.check
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.MainPartition
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.startCluster
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.bridgeAddr
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.holdToken
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Link
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Link
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.InProcLinked
public import Proof.go_uber_org.zap.NewNop
public import Proof.strconv.Itoa
public import Perennial.Proof.context.Link
public import Proof.context.Link
public import Proof.context.WithTimeoutBackground
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Assumptions]

theorem k8s_compactor.wp_ready : k8s_compactor.ready.spec (GF := GF) (hG := hG) :=
  k8s_compactor.ready.wp_proof context.wp_Background context.WithTimeoutBackground.wp_proof
    context.wp_ErrAny client.client_Get_st_law_holds

theorem k8s_compactor.wp_writer : k8s_compactor.writer.spec (GF := GF) (hG := hG) :=
  k8s_compactor.writer.wp_proof context.wp_Background context.WithTimeoutBackground.wp_proof
    context.wp_ErrAny strconv.Itoa.wp_proof client.client_Put_kv_law_holds

theorem k8s_compactor.wp_check : k8s_compactor.check.spec (GF := GF) (hG := hG) :=
  k8s_compactor.check.wp_proof k8s.compactor.wp_CompactRevision k8s.compactor.wp_Stop
    strconv.ParseInt.wp_proof context.wp_Background context.WithTimeoutBackground.wp_proof
    context.wp_ErrAny client.client_Get_st_law_holds

theorem k8s_compactor.wp_apiserver : k8s_compactor.apiserver.spec (GF := GF) (hG := hG) :=
  k8s_compactor.apiserver.wp_proof k8s.wp_NewCompactor
    k8s.wp_StartCompactorPerEndpoint k8s_compactor.wp_check
    k8s.inProcEtcd_laws_law_holds

/-- **The compactor example's `Main` does not panic** (see the file header;
`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/compactor/Main.lean`), under the semantic premises
of its callees' linked results (as `compactwatch`'s). -/
theorem k8s_compactor.wp_Main :
    k8s_compactor.Main.spec (GF := GF) (hG := hG) :=
  k8s_compactor.Main.wp_proof zap.NewNop.wp_proof etcdstart.wp_StartCompactingServer
    etcdstart.wp_Serve etcdstart.wp_NewClient context.wp_ErrAny
    k8s_compactor.wp_ready k8s_compactor.wp_writer k8s_compactor.wp_apiserver mvcc.api.mvccApi_names_nonempty_law_holds
    mvcc.api.mvccApi_persistent_law_holds mvcc.api.mvccApi_mvccState_reachable_law_holds
    mvcc.api.mvccApi_mvccReaders_split_law_holds _root_.Perennial.EtcdGrove.proto.MarshalBootConfChange.wp_proof

/-- `startCluster`'s callees linked (the k8s etcd3 driver's `wp_startCluster`, without its
kubernetes client). -/
theorem k8s_compactor.wp_startCluster :
    k8s_compactor.startCluster.spec (GF := GF) (hG := hG) :=
  k8s_compactor.startCluster.wp_proof etcdstart.wp_Members etcdstart.wp_StartMembers
    etcdstart.wp_Serve cluster3.wp_StartBridge
    (k8s_compactor.bridgeAddr.wp_proof etcdstart.strconv.wp_FormatUint)
    k8s_compactor.holdToken.wp_proof mvcc.api.mvccApi_names_nonempty_law_holds
    mvcc.api.mvccApi_persistent_law_holds mvcc.api.mvccApi_mvccState_reachable_law_holds
    (fun dir ps h hl => rafthttp.bootCfg_of_le dir ps h (by unfold peersMax; omega)) _root_.Perennial.EtcdGrove.proto.MarshalBootConfChange.wp_proof

/-- **The compactor example's `MainPartition` does not panic** (K6;
`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/compactor/MainPartition.lean`), under the semantic
premises of its callees' linked results (`Main`'s, and the `k`-member cluster's). -/
theorem k8s_compactor.wp_MainPartition
    [go_etcd_io.etcd.cache.v3.Assumptions] :
    k8s_compactor.MainPartition.spec (GF := GF) (hG := hG) :=
  k8s_compactor.MainPartition.wp_proof zap.NewNop.wp_proof k8s_compactor.wp_startCluster
    etcdstart.wp_NewClients cluster3.wp_Partitioner context.wp_ErrAny
    k8s_compactor.wp_ready k8s_compactor.wp_writer k8s_compactor.wp_apiserver

end results

end EtcdGrove
end Perennial
