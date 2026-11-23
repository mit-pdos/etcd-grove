/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/SyncDLinked.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`handleSync`/`handleNewLeaderAckNs` linked at the descriptors' state (round 23, sv-swb; task 3):
SyncLinked.lean's generic theorems at `EpR := descDS`, `EpH := descDSH` (DescDS.lean), `EpS :=
descEpS` (DescFresh.lean), `DF := descDFA x.γsh`, with `replyChan.stop` by `swift.epR_stop_ofD`
(over the proved `replyChan.stop.specR`), `stopDescs` by `swift.Replica.stopDescs.wp_specI`,
`EpS_start` by `swift.descEpS_of`. Open: `getCmdDesc.syncSpecI (descEpS …)` (the descriptor
side's task 4) and `NewReplyChan.specIH` (passed by Link.lean).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncLinked
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DescFresh
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ReplyChan

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section link
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [github_com.orcaman.concurrent_map.Assumptions]
  [sync.Assumptions] [sync.atomic.Assumptions] [state.Assumptions] [log.Assumptions]
  [slices.Assumptions] [time.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
  [github_com.emirpasic.gods.maps.treemap.Assumptions] [net.FieldAssumptions]

/-- **`handleSync` at the descriptors' state** (see the file header). -/
theorem swift.Replica.wp_handleSyncD (γ : sp.Names) (γc γm : GName) (rp : Loc) (x : swift.RunX)
    (wp_NRC : swift.NewReplyChan.specIH (hG := hG))
    -- OPEN (sv-swb, task 4): a committed command's descriptor (`*syncEntry`)
    (wp_getCD : swift.Replica.getCmdDesc.syncSpecI (hG := hG) (swift.descEpS γ γc γm x rp) γ
      x.syncN.γcl x.syncN.γdl rp x.N) :
    swift.Replica.handleSync.specI (hG := hG) (fun _ => swift.descDS γ γc γm x rp)
      (swift.descEpS γ γc γm x rp) (fun b => swift.descDF (x.DR γ b)) (swift.stopPS x) γ γc γm x.γl x.γw x.γv x.γd x.γe x.γo
      x.syncN rp x.rr (swift.descPC γ γc γm x rp) :=
  swift.Replica.wp_handleSync γ γc γm rp x (fun _ => swift.descDS γ γc γm x rp)
    (fun _ => swift.descDSH γ x rp) (swift.descEpS γ γc γm x rp) (fun b => swift.descDF (x.DR γ b)) (swift.stopPS x)
    (swift.descPC γ γc γm x rp) wp_NRC
    (swift.descEpS_of γ γc γm x rp)
    (swift.epR_stop_ofD swift.replyChan.stop.wp_proof γ γc γm x rp)
    (swift.Replica.stopDescs.wp_specI γ x rp) wp_getCD

/-- **`handleNewLeaderAckNs` at the descriptors' state** (see the file header). -/
theorem swift.Replica.wp_handleNewLeaderAckNsD (γ : sp.Names) (γc γm : GName) (rp : Loc)
    (x : swift.RunX) (wp_NRC : swift.NewReplyChan.specIH (hG := hG))
    (wp_getCD : swift.Replica.getCmdDesc.syncSpecI (hG := hG) (swift.descEpS γ γc γm x rp) γ
      x.syncN.γcl x.syncN.γdl rp x.N)
    (hmarsh : swift.MSync.marshalHG (hG := hG)) :
    swift.Replica.handleNewLeaderAckNs.specI (hG := hG) (fun _ => swift.descDS γ γc γm x rp)
      (swift.descEpS γ γc γm x rp) (fun b => swift.descDF (x.DR γ b)) (swift.stopPS x) γ γc γm x.γl x.γw x.γv x.γd x.γe x.γo
      x.syncN rp x.rr (swift.descPC γ γc γm x rp) :=
  swift.Replica.wp_handleNewLeaderAckNs γ γc γm rp x (fun _ => swift.descDS γ γc γm x rp)
    (fun _ => swift.descDSH γ x rp) (swift.descEpS γ γc γm x rp) (fun b => swift.descDF (x.DR γ b)) (swift.stopPS x)
    (swift.descPC γ γc γm x rp) wp_NRC
    (swift.descEpS_of γ γc γm x rp)
    (swift.epR_stop_ofD swift.replyChan.stop.wp_proof γ γc γm x rp)
    (swift.Replica.stopDescs.wp_specI γ x rp) wp_getCD hmarsh

end link

end Perennial.github_com.imdea_software.swiftpaxos
