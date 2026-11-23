/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/WritersLink.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The replica's writing side, linked: each proof applied to its callees' linked results
(dlog's `Printf`, the quorum's `Contains`, and the proofs of Writers.lean / Sender.lean).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.Sender
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.Writers
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumLink
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.dlog.Link

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section link
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [bufio.Assumptions] [net.Assumptions] [net.FieldAssumptions] [dlog.Assumptions]
  [time.Assumptions]

theorem replica.Replica.wp_ReplyBeacon : replica.Replica.ReplyBeacon.spec (hG := hG) :=
  replica.Replica.ReplyBeacon.wp_proof dlog.Logger.wp_Printf
theorem replica.Replica.wp_SendMsg : replica.Replica.SendMsg.spec (hG := hG) :=
  replica.Replica.SendMsg.wp_proof dlog.Logger.wp_Printf
theorem replica.Replica.wp_SendClientMsg : replica.Replica.SendClientMsg.spec (hG := hG) :=
  replica.Replica.SendClientMsg.wp_proof dlog.Logger.wp_Printf
theorem replica.Replica.wp_SendMsgP : replica.Replica.SendMsgP.spec (hG := hG) :=
  replica.Replica.SendMsgP.wp_proof dlog.Logger.wp_Printf
theorem replica.Replica.wp_SendClientMsgP : replica.Replica.SendClientMsgP.spec (hG := hG) :=
  replica.Replica.SendClientMsgP.wp_proof dlog.Logger.wp_Printf
theorem replica.Replica.wp_SendBeacon : replica.Replica.SendBeacon.spec (hG := hG) :=
  replica.Replica.SendBeacon.wp_proof dlog.Logger.wp_Printf
theorem replica.wp_sendToAll : replica.sendToAll.spec (hG := hG) :=
  replica.sendToAll.wp_proof replica.Replica.wp_SendMsgP
theorem replica.wp_sendToAllExcept : replica.sendToAllExcept.spec (hG := hG) :=
  replica.sendToAllExcept.wp_proof replica.Replica.wp_SendMsgP
theorem replica.wp_sendToQuorum : replica.sendToQuorum.spec (hG := hG) :=
  replica.sendToQuorum.wp_proof replica.Replica.wp_SendMsgP replica.Quorum.wp_Contains
theorem replica.wp_sendExcept : replica.sendExcept.spec (hG := hG) :=
  replica.sendExcept.wp_proof replica.Replica.wp_SendMsgP replica.Quorum.wp_Contains
theorem replica.wp_NewSender : replica.NewSender.spec (hG := hG) :=
  replica.NewSender.wp_proof replica.Replica.wp_SendMsgP replica.Replica.wp_SendClientMsgP
    replica.wp_sendToAll replica.wp_sendToAllExcept replica.wp_sendToQuorum replica.wp_sendExcept
theorem replica.Sender.wp_SendToAllAndFree : replica.Sender.SendToAllAndFree.spec (hG := hG) :=
  replica.Sender.SendToAllAndFree.wp_proof
theorem replica.Sender.wp_SendToAll : replica.Sender.SendToAll.spec (hG := hG) :=
  replica.Sender.SendToAll.wp_proof replica.Sender.wp_SendToAllAndFree
theorem replica.Sender.wp_SendToAllAndFreeP : replica.Sender.SendToAllAndFreeP.spec (hG := hG) :=
  replica.Sender.SendToAllAndFreeP.wp_proof
theorem replica.Sender.wp_SendToAllP : replica.Sender.SendToAllP.spec (hG := hG) :=
  replica.Sender.SendToAllP.wp_proof replica.Sender.wp_SendToAllAndFreeP
theorem replica.Sender.wp_SendToAllExecptAndFree : replica.Sender.SendToAllExecptAndFree.spec (hG := hG) :=
  replica.Sender.SendToAllExecptAndFree.wp_proof
theorem replica.Sender.wp_SendToAllExecpt : replica.Sender.SendToAllExecpt.spec (hG := hG) :=
  replica.Sender.SendToAllExecpt.wp_proof replica.Sender.wp_SendToAllExecptAndFree
theorem replica.Sender.wp_SendToQuorumAndFree : replica.Sender.SendToQuorumAndFree.spec (hG := hG) :=
  replica.Sender.SendToQuorumAndFree.wp_proof
theorem replica.Sender.wp_SendToQuorum : replica.Sender.SendToQuorum.spec (hG := hG) :=
  replica.Sender.SendToQuorum.wp_proof replica.Sender.wp_SendToQuorumAndFree
theorem replica.Sender.wp_SendExceptAndFree : replica.Sender.SendExceptAndFree.spec (hG := hG) :=
  replica.Sender.SendExceptAndFree.wp_proof
theorem replica.Sender.wp_SendExcept : replica.Sender.SendExcept.spec (hG := hG) :=
  replica.Sender.SendExcept.wp_proof replica.Sender.wp_SendExceptAndFree
theorem replica.Sender.wp_SendToClientAndFree : replica.Sender.SendToClientAndFree.spec (hG := hG) :=
  replica.Sender.SendToClientAndFree.wp_proof
theorem replica.Sender.wp_SendToClient : replica.Sender.SendToClient.spec (hG := hG) :=
  replica.Sender.SendToClient.wp_proof replica.Sender.wp_SendToClientAndFree
theorem replica.Sender.wp_SendToAndFree : replica.Sender.SendToAndFree.spec (hG := hG) :=
  replica.Sender.SendToAndFree.wp_proof
theorem replica.Sender.wp_SendTo : replica.Sender.SendTo.spec (hG := hG) :=
  replica.Sender.SendTo.wp_proof replica.Sender.wp_SendToAndFree

end link

end Perennial.github_com.imdea_software.swiftpaxos
