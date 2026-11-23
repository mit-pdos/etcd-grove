/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/Link.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The swift replica's linked results: each proof applied to its callees' proved results (the
replica group's quorum system and the concurrent map's). The codec functions' specs the
receiver's dispatch calls are hypotheses until the codec group proves them (Rcvr.lean).
`handleSync` and `handleNewLeaderAckNs` are linked in Proof/swift/SyncLink.lean (imported here:
`swift.Replica.wp_handleSync`, `swift.Replica.wp_handleNewLeaderAckNs`, with their open hypotheses
marked OPEN).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.CodecFns
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.codec.CodecFns
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumSystem
public import Dsverify.Proof.github_com.orcaman.concurrent_map.Link
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ServersSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewProof
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ReplyChan
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Batcher
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.PoolFns
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ClientChecksum
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HashLogLink
public import Perennial.Proof.slices.Link
public import Perennial.Proof.sync.atomic.Link
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.InitCsR
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.CmapBridge
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.New
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.state.Link
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.WritersLink
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.dlog.Link
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.MarshalOpt
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.MarshalFac
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.PutVarint
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncLink

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section link
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [github_com.orcaman.concurrent_map.Assumptions]
  [sync.Assumptions] [examples.swiftnet.Assumptions]

/-- `BeTheLeader`, linked. -/
theorem swift.Replica.wp_BeTheLeader : swift.Replica.BeTheLeader.spec :=
  swift.Replica.BeTheLeader.wp_proof sync.atomic.Bool.wp_Load
    replica.QuorumSystem.BallotAt.wp_proof replica.Leader.wp_proof

/-- The receiver, linked. -/
theorem swift.rcvr_ok : swift.rcvr.spec :=
  swift.rcvr.wp_proof swift.Replica.wp_BeTheLeader
    examples.swiftnet.rpcDecodeAs_defs_BeTheLeaderArgs.wp_proof
    examples.swiftnet.rpcDecodeAs_defs_PingArgs.wp_proof
    examples.swiftnet.rpcPutU64.specNil.wp_proof
    examples.swiftnet.rpcEnc_defs_BeTheLeaderReply.wp_proof
    examples.swiftnet.rpcEnc_defs_PingReply.wp_proof

end link

section newLink
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [github_com.orcaman.concurrent_map.Assumptions]
  [sync.Assumptions] [examples.swiftnet.Assumptions] [dlog.Assumptions] [hook.Assumptions]
  [time.Assumptions] [config.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
  [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions]
  [io.Assumptions] [io.ExtraAssumptions] [errors.Assumptions] [bufio.Assumptions]
  [net.Assumptions] [net.FieldAssumptions]

/-- `swift.New`, linked to its proved callees; the hypotheses still open: the package states'
facts (proved at the link with `pkgStates`), the batcher's and the reply channel's goroutines,
`hook.HookUser1`, and the run loop (notes/prove-swift.md §10). -/
theorem swift.wp_New (facts : swift.SrvPkgFacts)
    (wp_batcher : swift.NewBatcher.specI (hG := hG))
    (wp_rc : swift.NewReplyChan.specI (hG := hG))
    (wp_hook : hook.HookUser1.specI (hG := hG))
    (wp_run : swift.Replica.run.specI (hG := hG)) : swift.New.spec (hG := hG) :=
  swift.New.wp_proof facts (replica.New.wp_proof state.wp_InitState rpc.NewTableId.wp_proof)
    github_com.orcaman.concurrent_map.wp_NewV
    replica.wp_NewMajorityOf replica.wp_NewThreeQuartersOf replica.wp_NewSender wp_batcher wp_rc
    replica.wp_NewQuorumSystem replica.QuorumSystem.wp_BallotAt replica.QuorumSystem.wp_AQ
    swift.initCs.wp_proofR replica.wp_Leader dlog.Logger.wp_Println dlog.Logger.wp_Fatal wp_hook
    wp_run swift.rcvr_ok

/-- The reply channel's goroutine, linked (open: `clientChecksum`'s spec and `MReply`'s
`Marshal`, Proof/swift/ReplyChan.lean). -/
theorem swift.wp_NewReplyChan (wp_cc : swift.clientChecksum.specR (hG := hG))
    (hmar : swift.MReply.marshalH (hG := hG)) : swift.NewReplyChan.specI (hG := hG) :=
  swift.NewReplyChan.wp_proof wp_cc hmar replica.Sender.wp_SendToClient replica.wp_Leader

/-- `clientChecksum`, linked (`slices.SortFunc`, `cmdIdCmp`, `hash` over the harness's
`Sum256`). -/
theorem swift.wp_clientChecksum [crypto.sha256.Assumptions] [slices.Assumptions]
    [math.bits.Assumptions] [cmp.Assumptions] : swift.clientChecksum.specR (hG := hG) :=
  swift.clientChecksum.wp_proof slices.wp_SortFunc (swift.cmdIdCmp.wp_proof swift.cmdIdLess.wp_proof)
    swift.wp_hash

/-- The batcher's goroutine, linked (open: the four messages' `Marshal`, `clientChecksum`,
`releaseFastAck`: Proof/swift/Batcher.lean). -/
theorem swift.wp_NewBatcher (wp_cc : swift.clientChecksum.specR (hG := hG))
    (wp_rel : swift.releaseFastAck.specR (hG := hG))
    (hmo : swift.MOptAcks.marshalH (hG := hG)) (hma : swift.MAcks.marshalH (hG := hG))
    (hmf : swift.MFastAckClient.marshalH (hG := hG))
    (hms : swift.MLightSlowAck.marshalH (hG := hG)) : swift.NewBatcher.specI (hG := hG) :=
  swift.NewBatcher.wp_proof wp_cc wp_rel hmo hma hmf hms replica.Sender.wp_SendToClient
    replica.Sender.wp_SendToAll

/-- The descriptor proofs' cmap hypotheses, linked. -/
theorem swift.wp_cmapHasV (dm : GoSlice) (γdl : GName) : swift.cmapHasV.spec dm γdl :=
  swift.cmapHasV_of github_com.orcaman.concurrent_map.ConcurrentMap.wp_HasV dm γdl
theorem swift.wp_cmapSetV (dm : GoSlice) (γdl : GName) : swift.cmapSetV.spec dm γdl :=
  swift.cmapSetV_of github_com.orcaman.concurrent_map.ConcurrentMap.wp_SetV dm γdl

end newLink

section marshalLink
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [swift.Assumptions]

/-! The swift messages' `Marshal` (Proof/swift/Marshal*.lean), linked: `MLightSlowAck`'s and
`MNewLeader`'s directly; the four others with `putVarint`'s proved spec (fork change P1,
`swift.PutVarint.wp_proof`, Proof/swift/PutVarint.lean). -/

theorem swift.wp_MLightSlowAck_marshal : swift.MLightSlowAck.marshalH (hG := hG) :=
  swift.MLightSlowAck.marshal_proof
theorem swift.wp_MNewLeader_marshal : swift.MNewLeader.marshalH (hG := hG) :=
  swift.MNewLeader.marshal_proof
theorem swift.wp_MFastAckClient_marshal : swift.MFastAckClient.marshalH (hG := hG) :=
  swift.MFastAckClient.marshal_proof swift.PutVarint.wp_proof
theorem swift.wp_MReply_marshal : swift.MReply.marshalH (hG := hG) :=
  swift.MReply.marshal_proof swift.PutVarint.wp_proof
theorem swift.wp_MOptAcks_marshal : swift.MOptAcks.marshalH (hG := hG) :=
  swift.MOptAcks.marshal_proof swift.PutVarint.wp_proof
theorem swift.wp_MAcks_marshal : swift.MAcks.marshalH (hG := hG) :=
  swift.MAcks.marshal_proof swift.PutVarint.wp_proof

end marshalLink

section maxDesc
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [SwiftNetPkgState GF]

/-- The adapter's store to `swift.MaxDescRoutines` (change log C2, C14). -/
theorem setMaxDesc.wp_proof : setMaxDesc.spec (GF := GF) := by
  intro d d0 _
  wp_start as H
  wp_apply (wp_store (V := w64)) $$ [$H] as H
  iapply HΦ
  iexact H

end maxDesc

end Perennial.github_com.imdea_software.swiftpaxos
