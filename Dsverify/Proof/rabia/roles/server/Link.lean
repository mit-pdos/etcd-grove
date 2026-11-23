/-
The server's links (as paxos's `Link.lean`, hand-written): each Go function's proof applied to its
callees' linked results, `wp_X : X.spec`, bottom up: `bufio`'s and `message`'s framing, tcp's
endpoints (over `net`'s proofs, `TcpDeps`), the queue and the ledger, the three layers, then
`ServerInit`, `Server.Prologue` and `Server.ServerMain`. The only module where the server's proofs
meet (CLAUDE.md, "Import tiers": a proof file takes its callees' specs as hypotheses). The library
hypotheses stay instance arguments (`zerolog.Hyps`, `os.signal.NoSignals`, `math.rand.Hyps`): the
closed statement carries them.
-/
module

public import Dsverify.Proof.rabia.roles.server.ServerInit
public import Dsverify.Proof.rabia.roles.server.Server__Prologue
public import Dsverify.Proof.rabia.roles.server.Server__ServerMain
public import Dsverify.Proof.rabia.roles.server.Server__TerminalLogger
public import Dsverify.Proof.rabia.roles.server.layers.proxy.ProxyInit
public import Dsverify.Proof.rabia.roles.server.layers.proxy.Prologue
public import Dsverify.Proof.rabia.roles.server.layers.proxy.CmdReceiver
public import Dsverify.Proof.rabia.roles.server.layers.proxy.KVSExecutor
public import Dsverify.Proof.rabia.roles.server.layers.network.Prologue
public import Dsverify.Proof.rabia.roles.server.layers.network.MsgRouter
public import Dsverify.Proof.rabia.roles.server.layers.network.MsgSerializer
public import Dsverify.Proof.rabia.roles.server.layers.consensus.ConsensusInit
public import Dsverify.Proof.rabia.roles.server.layers.consensus.SlotStats
public import Dsverify.Proof.rabia.roles.server.layers.consensus.ExecutorFinal
public import Dsverify.Proof.rabia.roles.server.layers.consensus.MsgHandler
public import Dsverify.Proof.rabia.internal.system.SigListen
public import Dsverify.Proof.rabia.internal.logger.InitLogger
public import Dsverify.Proof.rabia.internal.queue.heapInit
public import Dsverify.Proof.rabia.internal.queue.heapPush
public import Dsverify.Proof.rabia.internal.queue.heapPop
public import Dsverify.Proof.rabia.internal.queue.PQueue__Len
public import Dsverify.Proof.rabia.internal.message.ProxySeqId
public import Dsverify.Proof.rabia.internal.message.Marshal
public import Dsverify.Proof.rabia.internal.message.BufRead
public import Dsverify.Proof.rabia.internal.message.BufWrite
public import Dsverify.Proof.rabia.internal.message.WriteFlush
public import Dsverify.Proof.rabia.internal.message.MarshalWriteFlush
public import Dsverify.Proof.rabia.internal.message.ReadUnmarshal
public import Dsverify.Proof.rabia.internal.message.Msg__Unmarshal
public import Dsverify.Proof.rabia.internal.message.Command__Unmarshal
public import Dsverify.Proof.rabia.internal.message.ConsensusObj__Unmarshal
public import Dsverify.Proof.rabia.internal.ledger.Slot__Reset
public import Dsverify.Proof.rabia.internal.ledger.Slot__GetDecisionOrWake
public import Dsverify.Proof.rabia.internal.ledger.Slot__GetIsDone
public import Dsverify.Proof.rabia.internal.ledger.Slot__GetHasRecvDec
public import Dsverify.Proof.rabia.internal.ledger.Slot__SetHasRecvDec
public import Dsverify.Proof.rabia.internal.ledger.Slot__SetDecision
public import Dsverify.Proof.rabia.internal.ledger.Slot__RecvProposalsMajV
public import Dsverify.Proof.rabia.internal.ledger.Slot__RecvProposalsMajT
public import Dsverify.Proof.rabia.internal.ledger.Slot__RecvBCMsgsMajV
public import Dsverify.Proof.rabia.internal.ledger.Slot__RecvBCMsgsMajT
public import Dsverify.Proof.rabia.internal.ledger.Slot__SetMyProposal
public import Dsverify.Proof.rabia.internal.ledger.Slot__GetMyProposal
public import Dsverify.Proof.rabia.internal.ledger.Slot__SetMyBCMsgs
public import Dsverify.Proof.rabia.internal.ledger.Slot__GetMyBCMsgs
public import Dsverify.Proof.rabia.internal.ledger.Slot__IncrPhaseDecrRound
public import Dsverify.Proof.rabia.internal.ledger.Slot__HasEnoughMsg
public import Dsverify.Proof.rabia.internal.ledger.Slot__PutRecvProposals
public import Dsverify.Proof.rabia.internal.ledger.Slot__PutRecvBCMsgs
public import Dsverify.Proof.rabia.internal.tcp.ProxyTcpInit
public import Dsverify.Proof.rabia.internal.tcp.ProxyTCP__Connect
public import Dsverify.Proof.rabia.internal.tcp.ProxyTCP__NumConns
public import Dsverify.Proof.rabia.internal.tcp.ProxyTCP__ClientSendChan
public import Dsverify.Proof.rabia.internal.tcp.NetTCPInit
public import Dsverify.Proof.rabia.internal.tcp.NetTCP__Connect
public import Dsverify.Proof.rabia.internal.tcp.ClientTcpInit
public import Dsverify.Proof.rabia.internal.tcp.ClientTCP__Connect
public import Net.Proof.net.Listen
public import Net.Proof.net.Dial
public import Net.Proof.net.Listener__Accept
public import Net.Proof.net.Conn__Read
public import Net.Proof.net.Conn__Write
public import Net.Proof.net.Conn__Close
public import Net.Proof.net.TCPConn__SetWriteBuffer
public import Net.Proof.net.TCPConn__SetReadBuffer
public import Net.Proof.net.TCPConn__SetKeepAlive
public import Net.Proof.net.TCPConn__SetKeepAlivePeriod
public import Proof.bufio.Reader__ReadOk
public import Proof.bufio.Writer__Write
public import Proof.bufio.Writer__Flush
public import Proof.bufio.NewReaderSize
public import Proof.bufio.NewWriterSize
public import Perennial.Proof.fmt.Printf

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

-- (in `EtcdGrove.`, as every `Link.lean`: `etc/proof_roots.py`'s `namespace()` is their common prefix)
namespace EtcdGrove.dsvrabia

open Iris Iris.BI Net
open rabia.roles.server rabia.roles.server.layers rabia.internal.message rabia.internal.ledger
  rabia.internal.queue rabia.internal.tcp

section link
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.roles.server.Assumptions]
variable [tcp_sem : rabia.internal.tcp.Assumptions] [msg_sem : rabia.internal.message.Assumptions]
variable [_root_.Perennial.bufio.Assumptions] [_root_.Perennial.io.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [go.BasicIntoValInj] [sync.Assumptions]

-- bufio and message's framing
theorem wp_bufio_Writer_Write : EtcdGrove.bufio.Writer.Write.spec (GF := GF) (hG := hG) :=
  EtcdGrove.bufio.Writer.Write.wp_proof EtcdGrove.bufio.Writer.Flush.wp_proof
theorem wp_BufWrite : BufWrite.spec (GF := GF) := BufWrite.wp_proof wp_bufio_Writer_Write
theorem wp_BufReadB : BufRead.specB (GF := GF) :=
  BufRead.wp_proofB EtcdGrove.bufio.Reader.Read.wp_proofOk
theorem wp_BufRead : BufRead.spec (GF := GF) := BufRead.wp_proof EtcdGrove.bufio.Reader.Read.wp_proofOk
theorem wp_WriteFlush : WriteFlush.spec (GF := GF) :=
  WriteFlush.wp_proof wp_BufWrite EtcdGrove.bufio.Writer.Flush.wp_proof
theorem wp_Command_MarshalWriteFlush : Command.MarshalWriteFlush.spec (GF := GF) :=
  Command.MarshalWriteFlush.wp_proof Command.Marshal.wp_proof wp_BufWrite BufWrite.wp_proofTooLong
    EtcdGrove.bufio.Writer.Flush.wp_proof
theorem wp_Msg_MarshalWriteFlush : Msg.MarshalWriteFlush.spec (GF := GF) :=
  Msg.MarshalWriteFlush.wp_proof Msg.Marshal.wp_proof wp_BufWrite BufWrite.wp_proofTooLong
    EtcdGrove.bufio.Writer.Flush.wp_proof
theorem wp_Msg_Unmarshal : Msg.Unmarshal.spec (GF := GF) :=
  Msg.Unmarshal.wp_proof ConsensusObj.Unmarshal.wp_proof
theorem wp_Msg_ReadUnmarshal : Msg.ReadUnmarshal.spec (GF := GF) :=
  Msg.ReadUnmarshal.wp_proof wp_BufReadB wp_Msg_Unmarshal
theorem wp_Command_ReadUnmarshal : Command.ReadUnmarshal.spec (GF := GF) :=
  Command.ReadUnmarshal.wp_proof wp_BufReadB Command.Unmarshal.wp_proof

-- tcp's endpoints
theorem tcpDeps : TcpDeps (GF := GF) where
  setWriteBuffer := net.TCPConn.SetWriteBuffer.wp_proof
  setReadBuffer := net.TCPConn.SetReadBuffer.wp_proof
  setKeepAlive := net.TCPConn.SetKeepAlive.wp_proof
  setKeepAlivePeriod := net.TCPConn.SetKeepAlivePeriod.wp_proof
  read := net.Conn.Read.wp_proof
  write := net.Conn.Write.wp_proof
  close := net.Conn.Close.wp_proof
  dial := net.Dial.wp_proof
  accept := net.Listener.Accept.wp_proof
  newReaderSize := EtcdGrove.bufio.NewReaderSize.wp_proof
  newWriterSize := EtcdGrove.bufio.NewWriterSize.wp_proof
  cmdReadUnmarshal := wp_Command_ReadUnmarshal
  msgReadUnmarshal := wp_Msg_ReadUnmarshal
  cmdMarshalWriteFlush := wp_Command_MarshalWriteFlush
  msgMarshalWriteFlush := wp_Msg_MarshalWriteFlush
  writeFlush := wp_WriteFlush
theorem wp_NetTCPInit : NetTCPInit.spec (GF := GF) := NetTCPInit.wp_proof net.Listen.wp_proof
theorem wp_ProxyTcpInit : ProxyTcpInit.spec (GF := GF) := ProxyTcpInit.wp_proof net.Listen.wp_proof
theorem wp_NetTCP_Connect : NetTCP.Connect.spec (GF := GF) := NetTCP.Connect.wp_proof tcpDeps
theorem wp_ProxyTCP_Connect : ProxyTCP.Connect.spec (GF := GF) := ProxyTCP.Connect.wp_proof tcpDeps
theorem wp_ClientTCP_Connect : ClientTCP.Connect.spec (GF := GF) := ClientTCP.Connect.wp_proof tcpDeps
theorem wp_ClientTcpInit : ClientTcpInit.spec (GF := GF) := ClientTcpInit.wp_proof

-- the queue and the ledger
theorem wp_heapInit : heapInit.spec (GF := GF) :=
  heapInit.wp_proof PQueue.Len.wp_proof ProxySeqIdLessThan.wp_proof
theorem wp_heapPush : heapPush.spec (GF := GF) :=
  heapPush.wp_proof PQueue.Len.wp_proof ProxySeqIdLessThan.wp_proof
theorem wp_heapPop : heapPop.spec (GF := GF) :=
  heapPop.wp_proof PQueue.Len.wp_proof ProxySeqIdLessThan.wp_proof
theorem wp_RecvProposalsMajV : Slot.RecvProposalsMajV.spec (GF := GF) :=
  Slot.RecvProposalsMajV.wp_proof ProxySeqIdLessThan.wp_proof
theorem wp_RecvProposalsMajT : Slot.RecvProposalsMajT.spec (GF := GF) :=
  Slot.RecvProposalsMajT.wp_proof ProxySeqIdLessThan.wp_proof
theorem wp_PutRecvProposals : Slot.PutRecvProposals.spec (GF := GF) :=
  Slot.PutRecvProposals.wp_proof ProxySeqIdEqual.wp_proof

-- the layers
theorem wp_ConsensusInit [github_com.rs.zerolog.Hyps GF] : consensus.ConsensusInit.spec (GF := GF) :=
  consensus.ConsensusInit.wp_proof rabia.internal.logger.InitLogger.wp_proof wp_heapInit
theorem wp_ProxyInit [github_com.rs.zerolog.Hyps GF] : proxy.ProxyInit.spec (GF := GF) :=
  proxy.ProxyInit.wp_proof rabia.internal.logger.InitLogger.wp_proof wp_ProxyTcpInit
theorem wp_NetworkInit : network.NetworkInit.spec (GF := GF) :=
  network.NetworkInit.wp_proof wp_NetTCPInit
theorem wp_Network_Prologue : network.Network.Prologue.spec (GF := GF) :=
  network.Network.Prologue.wp_proof wp_NetTCP_Connect _root_.Perennial.fmt.Printf.wp_proof
theorem wp_Proxy_Prologue : proxy.Proxy.Prologue.spec (GF := GF) :=
  proxy.Proxy.Prologue.wp_proof wp_ProxyTCP_Connect
theorem wp_TerminalLogger [github_com.rs.zerolog.Hyps GF] : Server.TerminalLogger.spec (GF := GF) :=
  Server.TerminalLogger.wp_proof rabia.internal.logger.InitLogger.wp_proof ProxyTCP.NumConns.wp_proof
    consensus.Consensus.SlotStats.wp_proof
theorem wp_KVSExecutor [github_com.rs.zerolog.Hyps GF] : proxy.Proxy.KVSExecutor.spec (GF := GF) :=
  proxy.Proxy.KVSExecutor.wp_proof Slot.GetDecisionOrWake.wp_proof ProxyTCP.ClientSendChan.wp_proof
theorem wp_MsgRouter : network.Network.MsgRouter.spec (GF := GF) :=
  network.Network.MsgRouter.wp_proof Msg.Marshal.wp_proof
theorem wp_MsgSerializer : network.Network.MsgSerializer.spec (GF := GF) :=
  network.Network.MsgSerializer.wp_proof Msg.Marshal.wp_proof
theorem wp_Executor [math.rand.Hyps GF] : consensus.Consensus.Executor.spec (GF := GF) :=
  consensus.Consensus.Executor.wp_proof
    { getIsDone := Slot.GetIsDone.wp_proof, getHasRecvDec := Slot.GetHasRecvDec.wp_proof,
      setDecision := Slot.SetDecision.wp_proof,
      majV := wp_RecvProposalsMajV, majT := wp_RecvProposalsMajT,
      bcMajV := Slot.RecvBCMsgsMajV.wp_proof, bcMajT := Slot.RecvBCMsgsMajT.wp_proof,
      setMyProposal := Slot.SetMyProposal.wp_proof, getMyProposal := Slot.GetMyProposal.wp_proof,
      setMyBC := Slot.SetMyBCMsgs.wp_proof, getMyBC := Slot.GetMyBCMsgs.wp_proof,
      incr := Slot.IncrPhaseDecrRound.wp_proof, push := wp_heapPush, pop := wp_heapPop,
      len := PQueue.Len.wp_proof, seqIdEq := ProxySeqIdEqual.wp_proof }
theorem wp_MsgHandler [math.rand.Hyps GF] : consensus.Consensus.MsgHandler.spec (GF := GF) :=
  consensus.Consensus.MsgHandler.wp_proof Slot.GetIsDone.wp_proof Slot.GetHasRecvDec.wp_proof
    Slot.SetHasRecvDec.wp_proof Slot.HasEnoughMsg.wp_proof wp_PutRecvProposals
    Slot.PutRecvBCMsgs.wp_proof wp_heapPush wp_RecvProposalsMajT wp_RecvProposalsMajV

-- the server
theorem wp_ServerInit [github_com.rs.zerolog.Hyps GF] : ServerInit.spec (GF := GF) :=
  ServerInit.wp_proof Slot.Reset.wp_proof wp_ProxyInit wp_NetworkInit wp_ConsensusInit

theorem wp_Prologue [github_com.rs.zerolog.Hyps GF] [os.signal.NoSignals os.signal.quietSigs GF] :
    Server.Prologue.spec (GF := GF) :=
  Server.Prologue.wp_proof rabia.internal.system.SigListen.wp_proof wp_Network_Prologue
    wp_Proxy_Prologue wp_TerminalLogger

theorem wp_ServerMain [github_com.rs.zerolog.Hyps GF] [math.rand.Hyps GF] :
    Server.ServerMain.spec (GF := GF) :=
  Server.ServerMain.wp_proof proxy.Proxy.CmdReceiver.wp_proof wp_KVSExecutor wp_MsgRouter
    wp_MsgSerializer wp_Executor wp_MsgHandler

end link

end EtcdGrove.dsvrabia

end Perennial
