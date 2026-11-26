/-
`Main`'s callees linked (`notes/txnlinfaultsN-plan.md`, 2026-11-15), by hand, as putgetN's
(`putgetN/MainLinked.lean`): `etcd_txnlinfaultsN.Main.wp_proof` applied to the axiom of `zap.NewNop`,
`startCluster.wp_proof` (over the examples' shared start's linked `Members`, `StartMembers`, `Serve` and
`NewClients`, cluster3's linked `StartBridge`, `bridgeAddr.wp_proof` over `strconv.FormatUint`,
`holdToken.wp_proof`, and `rafthttp.bootCfg_of_le`: a directory of up to `1000` members is within the
transport's `peersMax`), cluster3's linked `Partitioner` and partition's linked `Check`. `Results.lean`
restates it.
-/
module

public import Proof.google_golang_org.protobuf.proto.MarshalBootConfChange
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiResults
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.startCluster
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.bridgeAddr
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.holdToken
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.partition.Link
public import Proof.go_uber_org.zap.NewNop

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.Assumptions]
variable [NaInvG GF]

/-- **txnlinfaultsN's `Main(k, clients, ops, sched)` does not panic, for every schedule** (see the file
header; `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/txnlinfaultsN/Main.lean`), under the semantic
premises of its callees' linked results (partition's and putgetN's). -/
theorem etcd_txnlinfaultsN.wp_Main [_root_.Perennial.net.FieldAssumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    :
    etcd_txnlinfaultsN.Main.spec (GF := GF) (hG := hG) :=
  etcd_txnlinfaultsN.Main.wp_proof zap.NewNop.wp_proof
    (etcd_txnlinfaultsN.startCluster.wp_proof etcdstart.wp_Members etcdstart.wp_StartMembers
      etcdstart.wp_Serve etcdstart.wp_NewClients cluster3.wp_StartBridge
      (etcd_txnlinfaultsN.bridgeAddr.wp_proof etcdstart.strconv.wp_FormatUint)
      etcd_txnlinfaultsN.holdToken.wp_proof mvcc.api.mvccApi_names_nonempty_law_holds
      (fun dir ps h hl => rafthttp.bootCfg_of_le dir ps h (by unfold peersMax; omega)) _root_.Perennial.EtcdGrove.proto.MarshalBootConfChange.wp_proof)
    cluster3.wp_Partitioner etcd_partition.wp_Check

end results

end EtcdGrove
end Perennial
