/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/DescLink.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**The descriptor goroutine's and the inline call's specs at the run loop's records** (round 43,
sv-swb; D52 (2)): `handleDesc.specD` and `seqSpecD` at `RC := swift.RCh γ0 γc γm` (round 45,
D54/D55 (1); before: `RC := True`), from the top-down proofs
(HandleDescProof.lean, SeqSpecProof.lean) with every remaining callee a named `sorry -- TD: …`.
`getCmdDescWith.wp_proofD` (GetDescWith.lean) and ServersLink's descriptor arms use these.

Round 44 (D53 (1), gap 43-1 repaired): the case specs are linked at the records of the replica's
`str` (`c.str = x.str`, `x.str = cmdStr`): `handleMsg.wp_proofAck` over `handleFastAck`,
`fastAckFromLeader`, `commonCaseFastAck`, `handleLightSlowAck`, `depsAccepted` and `deliver`;
`wp_proofProp` over `handlePropose`. The reply channel's `reply.specI` (request SWC-2) and the fast-ack
pool's `newFastAck`/`copyFastAck` (ServersLink's pool fact) stay hypotheses, as for `newDesc`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SeqSpecProof
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SlotProofS
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SlotProofG
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DescBundle
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.GetDescOwner
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewDescLinked
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.FastAck
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleProposeProof
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DeliverProofE
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleSyncEntry
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ReplyChan
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.CmdStr
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Results
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.PoolFns
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.state.Results
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.MsgSet
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumLinked
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.WritersLinked
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.hook.OptCondF
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.bytes.Link
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.BatcherFast
public import Dsverify.Proof.github_com.orcaman.concurrent_map.Linked

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section link
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [hook.Assumptions] [github_com.orcaman.concurrent_map.Assumptions]
variable [sync.atomic.Assumptions] [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions]
variable [bytes.Assumptions] [examples.swiftnet.Assumptions] [dlog.Assumptions] [time.Assumptions]
  [config.Assumptions] [io.Assumptions] [errors.Assumptions] [bufio.Assumptions]
  [net.Assumptions] [net.FieldAssumptions]

/-- The callees of the case specs that are linked in ServersLink (round 44): the fast-ack pool's
functions (the server's pool fact). Round 46 (D-SWC2-6): the reply channel's `reply.specI` is
gone; `deliver.specE` uses `reply.specE`, proved (`swift.replyChan.reply.wp_proofE`). -/
structure swift.DescLinkH : Prop where
  newFA : swift.newFastAck.specP
  copyFA : swift.copyFastAck.specP

/-- `commonCaseFastAck` at the records of `x.str` (round 44; round 45: any `RC`). -/
theorem swift.common_linked (x : swift.RunX) (hstr : x.str = swift.cmdStr)
    (RC : Loc → w32 → IProp netDistGF) (MP : GoInterface → IProp netDistGF) :
    ∀ c : swift.DC, c.str = x.str →
      swift.Replica.commonCaseFastAck.specIc RC MP c :=
  swift.Replica.commonCaseFastAck.wp_proof RC MP replica.mset.MsgSet.Add.wp_proofQ replica.wp_Leader
    x.str (by rw [hstr]; exact swift.CommandId.String.wp_proof) swift.wp_cmapHasV

/-- `handleLightSlowAck` at the records of `x.str` (round 44; round 45: any `RC`). -/
theorem swift.lsa_linked (x : swift.RunX) (hstr : x.str = swift.cmdStr) (H : swift.DescLinkH)
    (RC : Loc → w32 → IProp netDistGF) (MP : GoInterface → IProp netDistGF) :
    ∀ c : swift.DC, c.str = x.str →
      swift.Replica.handleLightSlowAck.specIc RC MP c :=
  swift.Replica.handleLightSlowAck.wp_proof RC MP H.newFA x.str (swift.common_linked x hstr RC MP)

/-- `fastAckFromLeader` at the records of `x.str` (round 44; round 45: any `RC`). -/
theorem swift.lead_linked (x : swift.RunX) (hstr : x.str = swift.cmdStr) (H : swift.DescLinkH)
    (RC : Loc → w32 → IProp netDistGF) (MP : GoInterface → IProp netDistGF) :
    ∀ c : swift.DC, c.str = x.str →
      swift.Replica.fastAckFromLeader.specIc RC MP swift.ackCtx c :=
  swift.Replica.fastAckFromLeader.wp_proof RC MP hook.ocf.OptCondF.Call.wp_proof replica.wp_Leader
    x.str (by rw [hstr]; exact swift.CommandId.String.wp_proof) (by rw [hstr]; exact swift.cmdStr_inj)
    swift.wp_cmapHasV
    (swift.Replica.depsAccepted.wp_proof x.str (by rw [hstr]; exact swift.cmdStr_inj)
      (by rw [hstr]; exact swift.CommandId.String.wp_proof) swift.wp_cmapHasV)
    swift.Dep.Equals.wp_proofAny swift.Dep.Equals.wp_proofPerm (swift.SHashesEq.wp_proofAny bytes.wp_Equal)
    replica.mset.MsgSet.Add.wp_proofQ swift.Replica.markAccepted.wp_proof
    swift.Batcher.SendLightSlowAck.wp_proof swift.Batcher.SendLightSlowAckClient.wp_proof
    (swift.lsa_linked x hstr H RC MP) replica.Sender.wp_SendToClient swift.wp_MLightSlowAck_marshal

/-- `handleFastAck` at the records of `x.str` (round 44; round 45: any `RC`). -/
theorem swift.hfa_linked (x : swift.RunX) (hstr : x.str = swift.cmdStr) (H : swift.DescLinkH)
    (RC : Loc → w32 → IProp netDistGF) (MP : GoInterface → IProp netDistGF) :
    ∀ c : swift.DC, c.str = x.str →
      swift.Replica.handleFastAck.specIc RC MP swift.ackCtx c :=
  swift.Replica.handleFastAck.wp_proof RC MP replica.wp_Leader swift.ackCtx x.str
    (swift.lead_linked x hstr H RC MP) (swift.common_linked x hstr RC MP)

/-- `deliver` at `x.str` (as in `newDesc.wp_linked`; round 46, D-SWC2-6: `deliver.specE`, over
the reply channel's proved `reply.specE`). -/
theorem swift.deliver_linked (x : swift.RunX) (hstr : x.str = swift.cmdStr)
    (MP : GoInterface → IProp netDistGF) (hMP : swift.mpTy MP) :
    ∀ γdl, swift.Replica.deliver.specE x.str γdl MP := fun γdl =>
  swift.Replica.deliver.wp_proofE x.str (by rw [hstr]; exact swift.cmdStr_inj) γdl MP hMP
    (by rw [hstr]; exact swift.CommandId.String.wp_proof)
    (fun dm => swift.wp_cmapHasV dm γdl) (fun dm => swift.wp_cmapSetV dm γdl)
    state.Command.wp_Execute replica.wp_Leader swift.replyChan.reply.wp_proofE sync.atomic.Bool.wp_Store

/-- `handleMsg`'s ack/string case at `RC := RCh … c.rp` (round 44: linked, gap 43-1 repaired;
round 45: the reply channel object, D54). -/
theorem swift.ackSpec_linked (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX)
    (hstr : x.str = swift.cmdStr) (H : swift.DescLinkH) :
    ∀ MP, swift.mpTy MP → ∀ c : swift.DC, c.str = x.str → c.γ = γ0 → c.γc = γc → c.γm = γm →
      swift.Replica.handleMsg.ackSpecIc (swift.RCh γ0 γc γm c.rp) MP swift.ackCtx c :=
  fun MP hMP c hc h1 h2 h3 =>
  swift.Replica.handleMsg.wp_proofAck _ MP swift.ackCtx x.str (swift.hfa_linked x hstr H _ MP)
    (swift.lsa_linked x hstr H _ MP) (swift.lead_linked x hstr H _ MP)
    (swift.deliver_linked x hstr MP hMP) swift.ackCtx_ufp c hc (by rw [h1, h2, h3])

/-- `handleMsg`'s proposal case at `RC := RCh … c.rp` (round 44: linked, gap 43-1 repaired). -/
theorem swift.propSpec_linked (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX)
    (hstr : x.str = swift.cmdStr) (H : swift.DescLinkH) :
    ∀ MP, swift.mpTy MP → ∀ c : swift.DC, c.str = x.str → c.γ = γ0 → c.γc = γc → c.γm = γm →
      swift.Replica.handleMsg.propSpecIc (swift.RCh γ0 γc γm c.rp) MP swift.proposeCtx c :=
  fun MP hMP c hc h1 h2 h3 =>
  swift.Replica.handleMsg.wp_proofProp _ MP swift.proposeCtx x.str
    (swift.Replica.handlePropose.wp_proof _ MP hook.ocf.OptCondF.Recall.wp_proof x.str
      (by rw [hstr]; exact swift.CommandId.String.wp_proof) swift.wp_cmapHasV replica.wp_Leader
      H.newFA H.copyFA (swift.deliver_linked x hstr MP hMP)
      (swift.hfa_linked x hstr H _ MP) swift.Batcher.SendFastAck.wp_proof
      swift.Batcher.SendFastAckClient.wp_proof) c hc (by rw [h1, h2, h3])

/-- `handleMsg`'s sync entry case (`handleSyncEntry`, T24) at `RC := RCh … c.rp` (round 48:
linked, `swift.Replica.handleMsg.wp_proofSync`, HandleSyncEntry.lean, over `deliver.specE`). -/
theorem swift.syncSpec_linked (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX)
    (hstr : x.str = swift.cmdStr) :
    ∀ MP, swift.mpTy MP → ∀ c : swift.DC, c.str = x.str → c.γ = γ0 → c.γc = γc → c.γm = γm →
      swift.Replica.handleMsg.syncSpecIc (swift.RCh γ0 γc γm c.rp) MP c :=
  fun MP hMP c hc h1 h2 h3 =>
  swift.Replica.handleMsg.wp_proofSync _ MP x.str (swift.deliver_linked x hstr MP hMP) c hc
    (by rw [h1, h2, h3])

/-- **`depAll` under the bundle's hypothesis** (round 44, D53 (3); round O1: `wp_coreO`,
GetDescOwner.lean): `getCmdDesc` from an owner record (`depSpecR`), whose creation forks
`handleDesc` at the hypothesis `▷ handleDescR`. Round O1: takes `hstr`/`H` for `wp_coreO`'s callees
(`newDesc` at the replica's records, `newDesc.wp_linked`). -/
theorem swift.depAll_of_linked (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX)
    (hstr : x.str = swift.cmdStr) (H : swift.DescLinkH) :
    ⊢ □ ▷ swift.handleDescR γ0 γc γm x (swift.RCh γ0 γc γm) -∗ swift.depAll γ0 γc γm x :=
  swift.depAll_of_coreO γ0 γc γm x (by rw [hstr]; exact swift.CommandId.String.wp_proof)
    (by rw [hstr]; exact swift.cmdStr_inj) swift.wp_cmapHasV
    github_com.orcaman.concurrent_map.ConcurrentMap.wp_UpsertVL
    (swift.Replica.newDesc.wp_linked x γ0 γc γm hstr)

/-- **The bundle at `RC := swift.RCh γ0 γc γm`** (DescBundle.lean; round 45). -/
theorem swift.handleDescR_linked (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX)
    (hstr : x.str = swift.cmdStr) (H : swift.DescLinkH) :
    ⊢ swift.handleDescR γ0 γc γm x (swift.RCh γ0 γc γm) :=
  swift.descBundle γ0 γc γm x _
    (swift.Replica.handleDesc.wp_proofT γ0 γc γm x _
      (swift.Replica.handleMsg.wp_proofG γ0 γc γm x _ (swift.ackSpec_linked γ0 γc γm x hstr H)
        (swift.propSpec_linked γ0 γc γm x hstr H) (swift.syncSpec_linked γ0 γc γm x hstr)
        (swift.Replica.handleMsg.slotSpecG.wp_proof γ0 γc γm x (by rw [hstr]; exact swift.cmdStr_inj)
          (by rw [hstr]; exact swift.CommandId.String.wp_proof)
          github_com.orcaman.concurrent_map.ConcurrentMap.wp_RemoveL replica.mset.MsgSet.Free.wp_proofQ))
      swift.Replica.drainStops.wp_proof (swift.Replica.freeDesc.wp_proof _))
    (swift.depAll_of_linked γ0 γc γm x hstr H)

/-- **`go r.handleDesc(desc, cmdId)` at `RC := swift.RCh γ0 γc γm`** (round 45). -/
theorem swift.Replica.handleDesc.wp_linked (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX)
    (hstr : x.str = swift.cmdStr) (H : swift.DescLinkH) :
    swift.Replica.handleDesc.specD γ0 γc γm x (swift.RCh γ0 γc γm) :=
  swift.Replica.handleDesc.specD_of γ0 γc γm x _ (swift.handleDescR_linked γ0 γc γm x hstr H)

/-- **The run loop's inline `handleMsg`, `seqSpecD`**. -/
theorem swift.Replica.handleMsg.seqSpecD.wp_linked (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX)
    (hstr : x.str = swift.cmdStr) (H : swift.DescLinkH) :
    swift.Replica.handleMsg.seqSpecD γ0 γc γm x :=
  swift.Replica.handleMsg.seqSpecD.wp_proofT γ0 γc γm x
    (swift.Replica.handleMsg.wp_proofS γ0 γc γm x _ (swift.ackSpec_linked γ0 γc γm x hstr H)
      (swift.propSpec_linked γ0 γc γm x hstr H) (swift.syncSpec_linked γ0 γc γm x hstr)
      (swift.Replica.handleMsg.slotSpecS.wp_proof γ0 γc γm x (by rw [hstr]; exact swift.cmdStr_inj)
        (by rw [hstr]; exact swift.CommandId.String.wp_proof)
        github_com.orcaman.concurrent_map.ConcurrentMap.wp_RemoveL
        replica.mset.MsgSet.Free.wp_proofQ (swift.Replica.freeDesc.wp_proof _)))
    (swift.Replica.handleMsg.slotSpecS.wp_proof γ0 γc γm x (by rw [hstr]; exact swift.cmdStr_inj)
      (by rw [hstr]; exact swift.CommandId.String.wp_proof)
      github_com.orcaman.concurrent_map.ConcurrentMap.wp_RemoveL
      replica.mset.MsgSet.Free.wp_proofQ (swift.Replica.freeDesc.wp_proof _))
    (swift.depAll_of_bundle γ0 γc γm x _ (swift.handleDescR_linked γ0 γc γm x hstr H)
      (swift.depAll_of_linked γ0 γc γm x hstr H))

end link

end Perennial.github_com.imdea_software.swiftpaxos
