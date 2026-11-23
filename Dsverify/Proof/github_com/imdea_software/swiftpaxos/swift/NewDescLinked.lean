/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/NewDescLink.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**`newDesc` linked at the replica's records** (round 39, sv-swb; decision D43 (5), notes/prove-swift.md
§47): `newDesc.wp_proofc` over its callees' proved specs (allocDesc, the acks handler with
`deliver`, ReinitCondF, ReinitMsgSet, Dep.Equals), for every message predicate with `deliver`'s
`int` payload fact (`swift.mpTy`; the descriptors' `MPi g y γi` have it, `swift.mpOk_ty`) and at
the records whose `str` is the replica's (`x.str = cmdStr`, recorded by `runInv`): `deliver` is
proved only for that `str`. The reply channel's `reply.specI` (request SWC-2) stays a hypothesis;
round 45 (D54): at the replica's reply channel object `swift.RCh γ0 γc γm rp`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewDesc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DescDS
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AcksHandler
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DeliverProofE
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ReplyChan
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ReplyDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.CmdStr
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Results
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.state.Results
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.MsgSet
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumLinked
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.hook.OptCondF
public import Perennial.Proof.sync.atomic.Link
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AllocDesc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DepEqualsV

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section link
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [github_com.orcaman.concurrent_map.Assumptions]
  [sync.Assumptions] [examples.swiftnet.Assumptions] [dlog.Assumptions] [hook.Assumptions]
  [time.Assumptions] [config.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
  [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions]
  [io.Assumptions] [errors.Assumptions] [bufio.Assumptions]
  [net.Assumptions] [net.FieldAssumptions] [sync.atomic.Assumptions]

/-- **`newDesc` at the replica's kind-free records** (see the file header). -/
theorem swift.Replica.newDesc.wp_linked (x : swift.RunX) (γ0 : sp.Names) (γc γm : GName)
    (hstr : x.str = swift.cmdStr) :
    ∀ (rp : Loc) (MP : GoInterface → IProp netDistGF), swift.mpTy MP →
      swift.Replica.newDesc.specNc (x.dc γ0 γc γm rp) (swift.RCh γ0 γc γm rp) MP := by
  intro rp MP hMP
  exact swift.Replica.newDesc.wp_proofc (x.dc γ0 γc γm rp) _ MP swift.Replica.allocDesc.wp_proof
    (swift.getFastAndSlowAcksHandler.wp_proofS _ MP (fun _ _ => inferInstance) x.str x.γdl
      (swift.Replica.deliver.wp_proofE x.str (by rw [hstr]; exact swift.cmdStr_inj) x.γdl MP hMP
        (by rw [hstr]; exact swift.CommandId.String.wp_proof)
        (fun dm => swift.wp_cmapHasV dm x.γdl) (fun dm => swift.wp_cmapSetV dm x.γdl)
        state.Command.wp_Execute replica.wp_Leader swift.replyChan.reply.wp_proofE
        sync.atomic.Bool.wp_Store)
      (x.dc γ0 γc γm rp) rfl rfl rfl)
    (hook.ocf.OptCondF.ReinitCondF.wp_proof hook.ocf.NewOptCondF.wp_proof)
    replica.mset.MsgSet.ReinitMsgSet.wp_proofD swift.Dep.Equals.wp_proofAnyV

end link

end Perennial.github_com.imdea_software.swiftpaxos
