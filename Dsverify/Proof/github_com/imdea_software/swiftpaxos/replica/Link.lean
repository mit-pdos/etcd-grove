/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/Link.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The replica group's linked results for `replica/replica.go`, `replica/defs`, `rpc`: each proof
applied to its callees' linked results (the quorum's are in `QuorumLink.lean`, the state
machine's in `Proof/state/Link.lean`, cmap's in `Proof/cmap/Link.lean`, HashLog's in
`Proof/swift/HashLogLink.lean`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.New
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ReplicaListener
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.defs.WaitDuration
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.state.Link
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.WritersLink

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section link
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions] [state.Assumptions]
variable [github_com.emirpasic.gods.maps.treemap.Assumptions] [sync.Assumptions]
variable [io.Assumptions] [io.ExtraAssumptions] [errors.Assumptions]
variable [bufio.Assumptions] [net.Assumptions] [net.FieldAssumptions] [dlog.Assumptions]
  [time.Assumptions]

theorem replica.wp_NewTableId_link : rpc.NewTableId.spec (hG := hG) := rpc.NewTableId.wp_proof
theorem rpc.Table.wp_Register : rpc.Table.Register.spec (hG := hG) := rpc.Table.Register.wp_proof
theorem rpc.Table.wp_Get : rpc.Table.Get.spec (hG := hG) := rpc.Table.Get.wp_proof

theorem replica.defs.Beacon.wp_Unmarshal : replica.defs.Beacon.Unmarshal.spec (GF := netDistGF) :=
  replica.defs.Beacon.Unmarshal.wp_proof
theorem replica.defs.BeaconReply.wp_Unmarshal :
    replica.defs.BeaconReply.Unmarshal.spec (GF := netDistGF) :=
  replica.defs.BeaconReply.Unmarshal.wp_proof
theorem replica.defs.LatencyTable.wp_WaitDurationID :
    replica.defs.LatencyTable.WaitDurationID.spec (hG := hG) :=
  replica.defs.LatencyTable.WaitDurationID.wp_proof

theorem replica.wp_New : replica.New.spec (hG := hG) :=
  replica.New.wp_proof state.wp_InitState replica.wp_NewTableId_link

theorem replica.Replica.wp_replicaListener : replica.Replica.replicaListener.spec (hG := hG) :=
  replica.Replica.replicaListener.wp_proof replica.Replica.wp_ReplyBeacon
    replica.defs.LatencyTable.wp_WaitDurationID rpc.Table.wp_Get
    replica.defs.Beacon.wp_Unmarshal replica.defs.BeaconReply.wp_Unmarshal

end link

end Perennial.github_com.imdea_software.swiftpaxos
