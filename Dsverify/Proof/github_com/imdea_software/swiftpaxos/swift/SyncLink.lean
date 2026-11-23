/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/SyncLink.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`handleSync` and `handleNewLeaderAckNs` linked (round 14, sv-swa): their proofs
(HandleSyncProof.lean, NewLeaderAckNs.lean) applied to their callees' proved results. The
hypotheses still open are the linked theorems' own, each marked OPEN with its owner
(notes/prove-swift.md §18 round 14): the epoch's machinery (sv-swb's descriptors (`freeDesc`
proved, round 16): `stopDescs` (D16: no `propsBack`), `getCmdDesc` with a `*syncEntry`; sv-swc's
reply channel and pool: `replyChan.stop`, `NewReplyChan.specIH` (GAP H-size), `EpS_start`),
`MSync`'s marshaling (`swift.MSync.marshalHG`, proved: `swift.MSync.marshal_proofG`,
MarshalSync.lean; a hypothesis here, applied where gob's/net's instance assumptions are in scope).
GAP C-wf is closed by `sp.cmdIs_wf` (change log C20, D15; round 15, sv-swb).
Separate from Link.lean to keep that module's build under the memory cap; Link.lean imports it.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleSyncProof
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewLeaderAckNs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SortedProposes
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncOrder
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecSyncLink
public import Dsverify.Proof.github_com.orcaman.concurrent_map.Link
public import Dsverify.Proof.github_com.orcaman.concurrent_map.IterCbN
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumLink
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.WritersLink
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.MsgSet
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.state.Link
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.MarshalSync
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.MarshalBase
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.FreeDesc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunAlloc
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Perennial.Proof.slices.Link

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section helpers
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [sync.Assumptions] [log.Assumptions] [time.Assumptions]
  [replica.Assumptions] [rpc.Assumptions] [replica.defs.Assumptions]

/-- `EpS_start` at the run loop's names (`swift.epRun_fresh`, then the descriptor side's
`EpS_of`). -/
theorem swift.epS_start_of (γ : sp.Names) (γc γm : GName) (rp : Loc) (x : swift.RunX)
    (EpS : sp.SyncMsg → List sp.CmdId → IProp netDistGF)
    (EpS_of : ∀ M : sp.SyncMsg, swift.epRun γ γc γm rp x ∗ swift.descsFresh x.γd rp ∗
      swift.cntFrozen x.γn false ⊢ EpS M []) :
    ∀ (b' : Nat) (M : sp.SyncMsg), 0 < b' →
      swift.epFresh γ γc γm x.syncN x.γe x.γd rp x.rr b' ⊢ |={⊤}=> EpS M [] := by
  intro b' M hb
  iintro Hf
  imod swift.epRun_fresh γ γc γm rp x b' hb $$ Hf with Hr
  imodintro
  iapply EpS_of M $$ Hr

/-- `replyChan.stop.specI` at the run loop's epoch (`swift.epRun_stop`, `PR` framed). -/
theorem swift.epR_stop_of (γ : sp.Names) (γc γm : GName) (rp : Loc) (x : swift.RunX)
    (PR : GMap swift.CommandId Loc → IProp netDistGF) :
    swift.replyChan.stop.specI (hG := hG) (fun pM => iprop(swift.epRun γ γc γm rp x ∗ PR pM))
      (fun pM => iprop(swift.epHalted rp x ∗ PR pM)) rp := by
  intro rc pM
  iintro %Φ ⟨-, ⟨Hr, HP⟩, Hrc⟩ HΦ
  iapply (swift.epRun_stop swift.replyChan.stop.wp_proof γ γc γm rp x rc) $$ [Hr Hrc]
  · iframe
  inext
  iintro ⟨Hh, Hrc⟩
  iapply HΦ
  iframe Hrc
  simp only []
  iframe

end helpers

section link
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [github_com.orcaman.concurrent_map.Assumptions]
  [sync.Assumptions] [sync.atomic.Assumptions] [state.Assumptions] [log.Assumptions]
  [slices.Assumptions] [time.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
  [github_com.emirpasic.gods.maps.treemap.Assumptions] [net.model.Assumptions]

/-- **`handleSync`, linked** at the run loop's names `x` (round 16; round 23: generic in the
epoch's states, instantiated with the descriptors' state in SyncLinkD.lean): the running epoch
`EpR`, the halted one `EpH`, the new one `EpS`, the stopped descriptors' `DF`, with their
hypotheses (`replyChan.stop`, `stopDescs`, `EpS_start`, `getCmdDesc.syncSpecI`); every other
callee linked. -/
theorem swift.Replica.wp_handleSync (γ : sp.Names) (γc γm : GName) (rp : Loc) (x : swift.RunX)
    (EpR EpH : GMap swift.CommandId Loc → IProp netDistGF)
    (EpS : sp.SyncMsg → List sp.CmdId → IProp netDistGF) (DF : Nat → Loc → IProp netDistGF)
    (PS : Nat → GMap GoString GoInterface → IProp netDistGF)
    (PC : IProp netDistGF)
    -- (sv-swc: `= NewReplyChan.specI`, proved: `swift.wp_NewReplyChan`, Link.lean)
    (wp_NRC : swift.NewReplyChan.specIH (hG := hG))
    (EpS_start : ∀ (N r b' : Nat) (M : sp.SyncMsg), 0 < b' →
      swift.syncCtx γ N r x.syncN rp ∗ □ PC ∗ swift.epFresh γ γc γm x.syncN x.γe x.γd rp x.rr b' ⊢
        |={⊤}=> EpS M [])
    (wp_stop : swift.replyChan.stop.specI (hG := hG) EpR EpH rp)
    (wp_stopD : swift.Replica.stopDescs.specI (hG := hG) EpH γ x.syncN x.γe x.γd DF PS x.rr rp)
    (wp_getCD : swift.Replica.getCmdDesc.syncSpecI (hG := hG) EpS γ x.syncN.γcl x.syncN.γdl rp x.N) :
    swift.Replica.handleSync.specI (hG := hG) EpR EpS DF PS γ γc γm x.γl x.γw x.γv x.γd x.γe x.γo
      x.syncN rp x.rr PC :=
  swift.Replica.handleSync.wp_proof EpR EpH EpS DF PS
    γ γc γm x.γl x.γw x.γv x.γd x.γe x.γo x.syncN rp x.rr PC time.wp_Now
    (swift.sortedProposes.wp_proof slices.wp_SortFunc
      (swift.cmdIdCmp.wp_proof swift.cmdIdLess.wp_proof))
    github_com.orcaman.concurrent_map.ConcurrentMap.IterCbVN.wp_proof
    replica.mset.MsgSet.Free.wp_proofQ (fun b => swift.Replica.freeDesc.wp_proof (DF b)) state.wp_InitState
    github_com.orcaman.concurrent_map.ConcurrentMap.wp_IterCbV
    github_com.orcaman.concurrent_map.ConcurrentMap.wp_RemoveV sync.atomic.Bool.wp_Store
    github_com.orcaman.concurrent_map.wp_NewV replica.QuorumSystem.wp_AQ wp_NRC
    (swift.syncOrder.wp_proof
      (swift.sortedIds.wp_proof slices.wp_SortFunc (swift.cmdIdCmp.wp_proof swift.cmdIdLess.wp_proof))
      swift.recOrder.wp_proof)
    swift.keysOf.wp_proof swift.lki.newLightKeyInfo.wp_proof swift.lki.lightKeyInfo.add.wp_proof
    EpS_start wp_stop wp_stopD wp_getCD replica.wp_Leader replica.Sender.wp_SendToClient
    swift.MLightSlowAck.marshal_proof time.Time.wp_Sub
    (fun γ γc γm γl x c => sp.cmdIs_wf (γ := γ) (γc := γc) (γm := γm) (γl := γl) x c)

/-- `wp_handleSync` with the run loop's own reader (`specIR`, round 25 SW4). -/
theorem swift.Replica.wp_handleSyncR (γ : sp.Names) (γc γm : GName) (rp : Loc) (x : swift.RunX)
    (EpR EpH : GMap swift.CommandId Loc → IProp netDistGF)
    (EpS : sp.SyncMsg → List sp.CmdId → IProp netDistGF) (DF : Nat → Loc → IProp netDistGF)
    (PS : Nat → GMap GoString GoInterface → IProp netDistGF)
    (PC : IProp netDistGF)
    -- (sv-swc: `= NewReplyChan.specI`, proved: `swift.wp_NewReplyChan`, Link.lean)
    (wp_NRC : swift.NewReplyChan.specIH (hG := hG))
    (EpS_start : ∀ (N r b' : Nat) (M : sp.SyncMsg), 0 < b' →
      swift.syncCtx γ N r x.syncN rp ∗ □ PC ∗ swift.epFresh γ γc γm x.syncN x.γe x.γd rp x.rr b' ⊢
        |={⊤}=> EpS M [])
    (wp_stop : swift.replyChan.stop.specI (hG := hG) EpR EpH rp)
    (wp_stopD : swift.Replica.stopDescs.specI (hG := hG) EpH γ x.syncN x.γe x.γd DF PS x.rr rp)
    (wp_getCD : swift.Replica.getCmdDesc.syncSpecI (hG := hG) EpS γ x.syncN.γcl x.syncN.γdl rp x.N) :
    swift.Replica.handleSync.specIR (hG := hG) EpR EpS DF PS γ γc γm x.γl x.γw x.γv x.γd x.γe x.γo
      x.syncN rp x.rr PC :=
  swift.Replica.handleSync.wp_proofR EpR EpH EpS DF PS
    γ γc γm x.γl x.γw x.γv x.γd x.γe x.γo x.syncN rp x.rr PC time.wp_Now
    (swift.sortedProposes.wp_proof slices.wp_SortFunc
      (swift.cmdIdCmp.wp_proof swift.cmdIdLess.wp_proof))
    github_com.orcaman.concurrent_map.ConcurrentMap.IterCbVN.wp_proof
    replica.mset.MsgSet.Free.wp_proofQ (fun b => swift.Replica.freeDesc.wp_proof (DF b)) state.wp_InitState
    github_com.orcaman.concurrent_map.ConcurrentMap.wp_IterCbV
    github_com.orcaman.concurrent_map.ConcurrentMap.wp_RemoveV sync.atomic.Bool.wp_Store
    github_com.orcaman.concurrent_map.wp_NewV replica.QuorumSystem.wp_AQ wp_NRC
    (swift.syncOrder.wp_proof
      (swift.sortedIds.wp_proof slices.wp_SortFunc (swift.cmdIdCmp.wp_proof swift.cmdIdLess.wp_proof))
      swift.recOrder.wp_proof)
    swift.keysOf.wp_proof swift.lki.newLightKeyInfo.wp_proof swift.lki.lightKeyInfo.add.wp_proof
    EpS_start wp_stop wp_stopD wp_getCD replica.wp_Leader replica.Sender.wp_SendToClient
    swift.MLightSlowAck.marshal_proof time.Time.wp_Sub
    (fun γ γc γm γl x c => sp.cmdIs_wf (γ := γ) (γc := γc) (γm := γm) (γl := γl) x c)

/-- **`handleNewLeaderAckNs`, linked** (over the linked `handleSync`): the same hypotheses, and
`MSync`'s marshaling `hmarsh` (round 18: proved, `swift.MSync.marshal_proofG` at the link's
codec, MarshalSync.lean; the send is `SendToAllP`'s). -/
theorem swift.Replica.wp_handleNewLeaderAckNs (γ : sp.Names) (γc γm : GName) (rp : Loc)
    (x : swift.RunX) (EpR EpH : GMap swift.CommandId Loc → IProp netDistGF)
    (EpS : sp.SyncMsg → List sp.CmdId → IProp netDistGF) (DF : Nat → Loc → IProp netDistGF)
    (PS : Nat → GMap GoString GoInterface → IProp netDistGF)
    (PC : IProp netDistGF)
    (wp_NRC : swift.NewReplyChan.specIH (hG := hG))
    (EpS_start : ∀ (N r b' : Nat) (M : sp.SyncMsg), 0 < b' →
      swift.syncCtx γ N r x.syncN rp ∗ □ PC ∗ swift.epFresh γ γc γm x.syncN x.γe x.γd rp x.rr b' ⊢
        |={⊤}=> EpS M [])
    (wp_stop : swift.replyChan.stop.specI (hG := hG) EpR EpH rp)
    (wp_stopD : swift.Replica.stopDescs.specI (hG := hG) EpH γ x.syncN x.γe x.γd DF PS x.rr rp)
    (wp_getCD : swift.Replica.getCmdDesc.syncSpecI (hG := hG) EpS γ x.syncN.γcl x.syncN.γdl rp x.N)
    -- proved: `swift.MSync.marshal_proofG` (MarshalSync.lean), at the link's codec
    (hmarsh : swift.MSync.marshalHG (hG := hG)) :
    swift.Replica.handleNewLeaderAckNs.specI (hG := hG) EpR
      EpS DF PS γ γc γm x.γl x.γw x.γv x.γd x.γe x.γo x.syncN rp x.rr PC :=
  swift.Replica.handleNewLeaderAckNs.wp_proof _ EpS DF PS
    γ γc γm x.γl x.γw x.γv x.γd x.γe x.γo x.syncN rp x.rr PC swift.Replica.wp_recoveredSync
    replica.Sender.wp_SendToAllP
    (swift.Replica.wp_handleSyncR γ γc γm rp x EpR EpH EpS DF PS PC wp_NRC EpS_start wp_stop wp_stopD
      wp_getCD)
    hmarsh

end link

end Perennial.github_com.imdea_software.swiftpaxos
