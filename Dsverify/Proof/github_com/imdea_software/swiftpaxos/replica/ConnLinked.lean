/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/ConnLinked.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The replica group's linked results for the connection setup and the clients' side of
`replica/replica.go`: `waitForPeerConnections`, `ConnectToPeers`, `clientListener`,
`WaitForClientConnections`, `ComputeClosestPeers`, `UpdatePreferredPeerOrder` (and
`Propose.Unmarshal`'s chain), each proof applied to its callees'
linked results. No gap: since the fork's R2 workaround (verify 0c5f2a8) P1 reads the first byte
with `ReadByte`, so no `Peek` is called.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.Results
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ConnectToPeers
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.Serve
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ClientListener
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ClientCallees
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.defs.ProposeUnmarshal
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.dlog.Results
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ClosestPeers
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.NetConn
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.Conn

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section link
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions] [state.Assumptions]
variable [github_com.emirpasic.gods.maps.treemap.Assumptions] [sync.Assumptions]
variable [io.Assumptions] [errors.Assumptions]
variable [bufio.Assumptions] [net.Assumptions] [net.rpc.Assumptions]
  [dlog.Assumptions] [time.Assumptions] [strings.Assumptions] [encoding.binary.Assumptions] [config.Assumptions]

theorem replica.Replica.wp_waitForPeerConnections :
    replica.Replica.waitForPeerConnections.spec (hG := hG) :=
  replica.Replica.waitForPeerConnections.wp_proof dlog.Logger.wp_Fatal
    dlog.Logger.wp_Println dlog.Logger.wp_Printf

theorem replica.Replica.wp_ConnectToPeers : replica.Replica.ConnectToPeers.spec (hG := hG) :=
  replica.Replica.ConnectToPeers.wp_proof replica.Replica.wp_waitForPeerConnections
    replica.Replica.wp_replicaListener dlog.Logger.wp_Println dlog.Logger.wp_Printf

theorem state.Value.wp_Unmarshal : state.Value.Unmarshal.spec (GF := netDistGF) :=
  state.Value.Unmarshal.wp_proof

theorem replica.defs.Propose.wp_Unmarshal : replica.defs.Propose.Unmarshal.spec (GF := netDistGF) :=
  replica.defs.Propose.Unmarshal.wp_proof state.Value.wp_Unmarshal

theorem replica.Replica.wp_clientListener : replica.Replica.clientListener.spec (hG := hG) :=
  replica.Replica.clientListener.wp_proof replica.defs.Propose.wp_Unmarshal
    replica.defs.LatencyTable.WaitDuration.wp_proof replica.defs.NewDelayProposeChan.wp_proof
    replica.defs.DelayProposeChan.Write.wp_proof config.ProxyInfo.IsProxy.wp_proof
    dlog.Logger.wp_Println net.TCPConn.RemoteAddr.labProof net.TCPConn.Close.labProof
    strings.wp_Split

theorem replica.Replica.wp_WaitForClientConnections :
    replica.Replica.WaitForClientConnections.spec (hG := hG) :=
  replica.Replica.WaitForClientConnections.wp_proof replica.Replica.wp_clientListener
    dlog.Logger.wp_Println

theorem replica.Replica.wp_UpdatePreferredPeerOrder :
    replica.Replica.UpdatePreferredPeerOrder.spec (hG := hG) :=
  replica.Replica.UpdatePreferredPeerOrder.wp_proof

theorem replica.Replica.wp_ComputeClosestPeers :
    replica.Replica.ComputeClosestPeers.spec (hG := hG) :=
  replica.Replica.ComputeClosestPeers.wp_proof replica.Replica.wp_SendBeacon
    replica.Replica.wp_UpdatePreferredPeerOrder dlog.Logger.wp_Println

end link

end Perennial.github_com.imdea_software.swiftpaxos
