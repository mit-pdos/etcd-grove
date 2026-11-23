/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/Link.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The client group's proofs applied to their callees' results. `dlog.Logger.Println`'s linked
result is the dlog package's (not in this worktree): it stays a hypothesis here.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.BufferClient__Write
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.BufferClient__Read
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Client__SendWrite
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Client__SendRead
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Client__SendProposal
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.NewClientLog
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.NewBufferClient
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.BufferClient__Disconnect
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.BufferClient__Connect
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Client__dialMaster
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Client__dial
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Client__call
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Client__callMaster
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Client__findClosest
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.HandleReply
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.NewClient
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.dlog.Link
public import Perennial.Proof.bytes.Link

-- PORT: lab imports dropped: Harness.Proof.net.rpc.Client, Harness.Proof.net.TCPConn__Close

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section link
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [client.Assumptions] [net.Assumptions] [net.model.Assumptions]
variable [bufio.Assumptions] [state.Assumptions] [encoding.binary.Assumptions]
variable [replica.defs.Assumptions] [dlog.Assumptions]
variable [net.rpc.Assumptions] [github_com.google.uuid.Assumptions] [math.rand.Assumptions] [time.Assumptions]

theorem client.Client.wp_SendProposal
    (wp_Println : dlog.Logger.Println.spec (GF := netDistGF) (hG := hG)) : client.Client.SendProposal.specI (hG := hG) :=
  client.Client.SendProposal.wp_proof wp_Println

theorem client.Client.wp_SendWrite
    (wp_Println : dlog.Logger.Println.spec (GF := netDistGF) (hG := hG)) : client.Client.SendWrite.specI (hG := hG) :=
  client.Client.SendWrite.wp_proof (client.Client.wp_SendProposal wp_Println)

theorem client.Client.wp_SendRead
    (wp_Println : dlog.Logger.Println.spec (GF := netDistGF) (hG := hG)) : client.Client.SendRead.specI (hG := hG) :=
  client.Client.SendRead.wp_proof (client.Client.wp_SendProposal wp_Println)

theorem client.BufferClient.wp_WriteI
    (wp_Println : dlog.Logger.Println.spec (GF := netDistGF) (hG := hG)) : client.BufferClient.Write.specI (hG := hG) :=
  client.BufferClient.Write.wp_proofI (client.Client.wp_SendWrite wp_Println)
    client.theGhost.wp_proof client.Ghost.Invoke.wp_proof client.Ghost.Accept.wp_proof

theorem client.BufferClient.wp_ReadI
    (wp_Println : dlog.Logger.Println.spec (GF := netDistGF) (hG := hG)) : client.BufferClient.Read.specI (hG := hG) :=
  client.BufferClient.Read.wp_proofI (client.Client.wp_SendRead wp_Println)
    client.theGhost.wp_proof client.Ghost.Invoke.wp_proof client.Ghost.Accept.wp_proof

theorem client.BufferClient.wp_Write
    (wp_Println : dlog.Logger.Println.spec (GF := netDistGF) (hG := hG)) : client.BufferClient.Write.spec (hG := hG) :=
  client.BufferClient.Write.wp_proof (client.Client.wp_SendWrite wp_Println)
    client.theGhost.wp_proof client.Ghost.Invoke.wp_proof client.Ghost.Accept.wp_proof

theorem client.BufferClient.wp_Read
    (wp_Println : dlog.Logger.Println.spec (GF := netDistGF) (hG := hG)) : client.BufferClient.Read.spec (hG := hG) :=
  client.BufferClient.Read.wp_proof (client.Client.wp_SendRead wp_Println)
    client.theGhost.wp_proof client.Ghost.Invoke.wp_proof client.Ghost.Accept.wp_proof

theorem client.wp_NewClientLog : client.NewClientLog.spec (hG := hG) :=
  client.NewClientLog.wp_proof

theorem client.wp_NewBufferClient : client.NewBufferClient.spec (hG := hG) :=
  client.NewBufferClient.wp_proof

theorem client.BufferClient.wp_Disconnect : client.BufferClient.Disconnect.spec (hG := hG) :=
  client.BufferClient.Disconnect.wp_proof net.rpc.Client.Close.wp_proof net.TCPConn.Close.wp_proof

end link

/-! ## The swift client's handler (swift/client.go) and `replica.MsgSet` (round 4) -/

section handler
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [client.Assumptions] [time.Assumptions]
  [dlog.Assumptions] [bytes.Assumptions]

theorem replica.mset.wp_ReinitMsgSet : replica.mset.MsgSet.ReinitMsgSet.specI (hG := hG) :=
  replica.mset.MsgSet.ReinitMsgSet.wp_proof replica.mset.NewMsgSet.wp_proofQ

theorem swift.handler.wp_handleFastAndSlowAcks :
    swift.handler.handleFastAndSlowAcks.specI (hG := hG) :=
  swift.handler.handleFastAndSlowAcks.wp_proof client.BufferClient.RegisterReply.wp_proof
    dlog.Logger.wp_Println

theorem swift.handler.wp_initMsgSets : swift.handler.initMsgSets.specI (hG := hG) :=
  swift.handler.initMsgSets.wp_proof replica.mset.wp_ReinitMsgSet
    swift.handler.wp_handleFastAndSlowAcks
    (swift.handler.SHashesEq.wp_proof bytes.wp_Equal) swift.handler.Dep.Equals.wp_proof

theorem swift.handler.wp_handleFastAck : swift.handler.handleFastAck.specI (hG := hG) :=
  swift.handler.handleFastAck.wp_proof swift.handler.wp_initMsgSets
    replica.mset.MsgSet.Add.wp_proof replica.leader.Leader.wp_proof

theorem swift.handler.wp_handleLightSlowAck : swift.handler.handleLightSlowAck.specI (hG := hG) :=
  swift.handler.handleLightSlowAck.wp_proof swift.handler.wp_handleFastAck
    swift.handler.wp_initMsgSets replica.mset.MsgSet.Add.wp_proof replica.leader.Leader.wp_proof
    swift.handler.newFastAck.wp_proof
    (swift.handler.copyFastAck.wp_proof swift.handler.newFastAck.wp_proof)

theorem swift.handler.wp_handleReply : swift.handler.handleReply.specI (hG := hG) :=
  swift.handler.handleReply.wp_proof swift.handler.wp_handleFastAck
    swift.handler.wp_initMsgSets replica.mset.MsgSet.Add.wp_proof
    swift.handler.newFastAck.wp_proof
    (swift.handler.copyFastAck.wp_proof swift.handler.newFastAck.wp_proof)

theorem swift.handler.wp_handleMsgs : swift.handler.handleMsgs.specI (hG := hG) :=
  swift.handler.handleMsgs.wp_proof swift.handler.wp_handleReply swift.handler.wp_handleFastAck
    swift.handler.wp_handleLightSlowAck swift.handler.newFastAck.wp_proof

end handler

/-! ## `swift.NewClient`: the readers, the table, the handler (round 5) -/

section newclient
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [client.Assumptions] [time.Assumptions]
  [dlog.Assumptions] [bytes.Assumptions] [net.Assumptions] [net.model.Assumptions]
  [rpc.Assumptions] [replica.defs.Assumptions] [io.Assumptions] [io.ExtraAssumptions]
  [errors.Assumptions] [bufio.Assumptions]

theorem swift.rd.wp_RegisterRPCTable : swift.rd.RegisterRPCTable.specI (hG := hG) :=
  swift.rd.RegisterRPCTable.wp_proof

/-- `swift.NewClient`, linked; it rests on the change log C6 record (`facts`: the swift
package's state on the client node, owned by the swift prover). -/
theorem swift.wp_NewClient (facts : swift.handler.ClientPkgFacts (hG := hG)) :
    swift.NewClient.spec (hG := hG) :=
  swift.NewClient.wp_proof facts dlog.Logger.wp_Println swift.rd.initCs.wp_proof
    swift.rd.wp_RegisterRPCTable swift.handler.wp_handleMsgs
    replica.quorum.NewMajorityOf.wp_proof replica.quorum.NewThreeQuartersOf.wp_proof

end newclient

/-! ## `Connect` (round 6) -/

section connect
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [client.Assumptions] [net.Assumptions] [net.model.Assumptions] [net.rpc.Assumptions]
variable [examples.swiftnet.Assumptions] [bufio.Assumptions] [replica.defs.Assumptions]
variable [dlog.Assumptions] [errors.Assumptions] [time.Assumptions] [fmt.Assumptions]
variable [strings.Assumptions]

theorem client.Client.wp_call : client.Client.call.specI (hG := hG) :=
  client.Client.call.wp_proof dlog.Logger.wp_Println

/-- `Connect`, linked; it rests on the change log C6 record (`facts`: `defs.LatencyConf` is
`""`, the defs package's state on the client node). -/
theorem client.BufferClient.wp_Connect (facts : swift.handler.ClientPkgFacts (hG := hG)) :
    client.BufferClient.Connect.spec (hG := hG) :=
  client.BufferClient.Connect.wp_proof facts dlog.Logger.wp_Println
    (client.Client.dialMaster.wp_proof dlog.Logger.wp_Println)
    (client.Client.callMasterRL.wp_proof client.Client.wp_call)
    (client.Client.callMasterL.wp_proof client.Client.wp_call)
    (client.Client.findClosest.wp_proof dlog.Logger.wp_Println)
    (client.Client.dial.wp_proof dlog.Logger.wp_Println)

end connect

/-! ## `Connect`/`Disconnect` over a codec (decision D6): the link uses them at `kitCodecC` -/

section connectC
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [client.Assumptions] [net.Assumptions] [net.model.Assumptions] [net.rpc.Assumptions]
variable [examples.swiftnet.Assumptions] [bufio.Assumptions] [replica.defs.Assumptions]
variable [dlog.Assumptions] [errors.Assumptions] [time.Assumptions] [fmt.Assumptions]
variable [strings.Assumptions]
variable [C : net.rpc.RpcCodec netDistGF] [KitLike C]

theorem client.Client.wp_callG : client.Client.call.specI (hG := hG) :=
  client.Client.call.wp_proof dlog.Logger.wp_Println

theorem client.BufferClient.wp_ConnectG (facts : swift.handler.ClientPkgFacts (hG := hG)) :
    client.BufferClient.Connect.specG (hG := hG) :=
  client.BufferClient.Connect.wp_proofG facts dlog.Logger.wp_Println
    (client.Client.dialMaster.wp_proof dlog.Logger.wp_Println)
    (client.Client.callMasterRL.wp_proof client.Client.wp_callG)
    (client.Client.callMasterL.wp_proof client.Client.wp_callG)
    (client.Client.findClosest.wp_proof dlog.Logger.wp_Println)
    (client.Client.dial.wp_proof dlog.Logger.wp_Println)

theorem client.BufferClient.wp_DisconnectG : client.BufferClient.Disconnect.specG (hG := hG) :=
  client.BufferClient.Disconnect.wp_proofG net.rpc.Client.Close.wp_proof net.TCPConn.Close.wp_proof

end connectC

end Perennial.github_com.imdea_software.swiftpaxos
