/-
Ported from dsverify-lab examples/epaxos/proof/Epaxos/Proof/replica/Link.lean (notes/dsv-epaxos.md).

The replica package's results under the names its callers link against: for each spec
`<Fn>.spec : Prop` of `Interface/{ReplicaSpec,RpcTable}.lean`, `<Fn>.wp_proof : <Fn>.spec`,
closed: the package's own callees by its proofs (`<Fn>.spec_holds`, which take their callees'
specs as hypotheses), the other packages' by their linked results (`wire/Link.lean`: `dlog`,
`config.IsProxy`, `state.InitState`, the `defs` marshalers, `Serializable.*`; Perennial's
`time` link: `Now`, `UnixNano`). The lab's `net.TCPConn.RemoteAddr.wp_String` is proved here
(`tcpAddrString`, `replica/ClientListener.lean`), not a premise.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.New
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Connect
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.WaitPeers
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.WaitClients
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.ServeConn
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Dial
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.ClientListener
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.ReplicaListener
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.SendMsg
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.ReplyPropose
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Beacon
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.ClosestPeers
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Quorum
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.RpcTable
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Link
public import Perennial.Proof.time.Link
public import Net.Proof.net.Conn__Read
public import Net.Proof.net.Conn__Write
public import Net.Proof.net.Conn__Close
public import Net.Proof.net.Conn__RemoteAddr
public import Net.Proof.net.Dial
public import Net.Proof.net.Listen
public import Net.Proof.net.Listener__Accept
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.IoReadFull

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS] [io.Assumptions]
  [field_sem : net.FieldAssumptions]

/-! ## The library hypotheses of the replica proofs (`Interface/LibDeps.lean`), closed

Local instances of this section only (bufio's, `epBufioDeps_holds`, from `wire/Link.lean`). -/

theorem epNetDeps_holds : EpNetDeps GF where
  connRead := net.Conn.Read.wp_proof
  connWrite := net.Conn.Write.wp_proof
  connClose := net.Conn.Close.wp_proof
  connRemoteAddr := net.Conn.RemoteAddr.wp_proof
  dial := net.Dial.wp_proof
  listen := net.Listen.wp_proof
  accept := net.Listener.Accept.wp_proof

theorem epReplicaDeps_holds : EpReplicaDeps GF where
  newTableId := rpc.NewTableId.wp_proof
  tableGet := rpc.Table.Get.wp_proof
  readFull := ioReadFullPre.wp_proof ioReadAtLeastPre.wp_proof

attribute [local instance] epBufioDeps_holds epNetDeps_holds epReplicaDeps_holds

/-! ## Package-internal functions (closed) -/

theorem replica.Replica.ReplyBeacon.wpI : replica.Replica.ReplyBeacon.specI (GF := GF) :=
  replica.Replica.ReplyBeacon.specI_holds dlog.Logger.Printf.wp_proof
    replica.defs.BeaconReply.Marshal.wp_proof

theorem replica.Replica.replicaListener.wp_proof : replica.Replica.replicaListener.spec (GF := GF) :=
  replica.Replica.replicaListener.spec_holds replica.Replica.ReplyBeacon.wpI
    replica.defs.Beacon.Unmarshal.wp_proof replica.defs.BeaconReply.Unmarshal.wp_proof
    Serializable.New.wp_proof Serializable.Unmarshal.wp_proof time.wp_Now time.Time.wp_UnixNano

theorem replica.Replica.clientListener.wp_proof : replica.Replica.clientListener.spec (GF := GF) :=
  replica.Replica.clientListener.spec_holds dlog.Logger.Println.wp_proof
    config.ProxyInfo.IsProxy.wp_proof replica.defs.Propose.Unmarshal.wp_proof

theorem replica.Replica.serveConn.wp_proof : replica.Replica.serveConn.spec (GF := GF) :=
  replica.Replica.serveConn.spec_holds replica.Replica.clientListener.wp_proof
    replica.Replica.replicaListener.wp_proof dlog.Logger.Println.wp_proof
    dlog.Logger.Printf.wp_proof

theorem replica.Replica.serveConnDial.wp_proof : replica.Replica.serveConnDial.specX (GF := GF) :=
  replica.Replica.serveConnDial.spec_holds replica.Replica.clientListener.wp_proof
    dlog.Logger.Println.wp_proof dlog.Logger.Printf.wp_proof

theorem replica.Replica.waitForPeerConnections.wp_proof :
    replica.Replica.waitForPeerConnections.specX (GF := GF) :=
  replica.Replica.waitForPeerConnections.spec_holds replica.Replica.serveConnDial.wp_proof
    dlog.Logger.Println.wp_proof dlog.Logger.Fatal.wp_proof

/-! ## The frozen specs (`Interface/ReplicaSpec.lean`), closed -/

theorem replica.New.wp_proof [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions]
    [TreemapHyp GF] : replica.New.spec (GF := GF) :=
  replica.New.spec_holds state.InitState.wp_proof

theorem replica.Replica.ConnectToPeers.wp_proof : replica.Replica.ConnectToPeers.spec (GF := GF) :=
  replica.Replica.ConnectToPeers.spec_holds replica.Replica.waitForPeerConnections.wp_proof
    replica.Replica.replicaListener.wp_proof dlog.Logger.Println.wp_proof
    dlog.Logger.Printf.wp_proof

theorem replica.Replica.WaitForClientConnections.wp_proof :
    replica.Replica.WaitForClientConnections.spec (GF := GF) :=
  replica.Replica.WaitForClientConnections.spec_holds replica.Replica.serveConn.wp_proof
    dlog.Logger.Println.wp_proof

theorem replica.Replica.SendMsg.wp_proof : replica.Replica.SendMsg.spec (GF := GF) :=
  replica.Replica.SendMsg.spec_holds dlog.Logger.Printf.wp_proof Serializable.Marshal.wp_proof

theorem replica.Replica.ReplyProposeTS.wp_proof : replica.Replica.ReplyProposeTS.spec (GF := GF) :=
  replica.Replica.ReplyProposeTS.spec_holds replica.defs.ProposeReplyTS.Marshal.wp_proof

theorem replica.Replica.SendBeacon.wp_proof : replica.Replica.SendBeacon.spec (GF := GF) :=
  replica.Replica.SendBeacon.spec_holds dlog.Logger.Printf.wp_proof
    replica.defs.Beacon.Marshal.wp_proof time.wp_Now time.Time.wp_UnixNano

theorem replica.Replica.ReplyBeacon.wp_proof : replica.Replica.ReplyBeacon.spec (GF := GF) :=
  replica.Replica.ReplyBeacon.spec_holds dlog.Logger.Printf.wp_proof
    replica.defs.BeaconReply.Marshal.wp_proof

theorem replica.Replica.ComputeClosestPeers.wp_proof : replica.Replica.ComputeClosestPeers.spec (GF := GF) :=
  replica.Replica.ComputeClosestPeers.spec_holds replica.Replica.SendBeacon.wp_proof
    dlog.Logger.Println.wp_proof

-- `replica.Replica.FastQuorumSize.wp_proof`, `SlowQuorumSize.wp_proof` (`Quorum.lean`) and
-- `rpc.NewTableId.wp_proof`, `rpc.Table.Register.wp_proof`, `rpc.Table.Get.wp_proof`
-- (`RpcTable.lean`) are closed already.

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
