/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RecSyncLinked.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`recoveredSync` linked: its proof (Proof/swift/RecSyncProof.lean) applied to its callees' proved
results, `slices.SortFunc.specOn` among them (Proof/slices/SortFuncOn.lean).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecSyncProof
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumLinked
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecOrder
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecHelpers
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecReaches
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SortedIds
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Key
public import Perennial.Proof.slices.Link
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOnLinked
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecKept

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section link
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [slices.Assumptions]

/-- `recoveredSync` linked. -/
theorem swift.Replica.wp_recoveredSync : swift.Replica.recoveredSync.specI (hG := hG) :=
  swift.Replica.recoveredSync.wp_proof slices.wp_SortFuncOn
    (swift.sortedIds.wp_proofC slices.wp_SortFunc (swift.cmdIdCmp.wp_proof swift.cmdIdLess.wp_proof))
    swift.recReaches.wp_proofM swift.recOrder.wp_proof
    (swift.inConflict.wp_proof state.Conflict.wp_proof) swift.keysOf.wp_proof
    swift.Dep.Contains.wp_proof swift.Dep.Equals.wp_proofG replica.wp_Leader
    replica.QuorumSystem.wp_AQ replica.Quorum.wp_Contains swift.lki.newLightKeyInfo.wp_proof
    swift.lki.lightKeyInfo.add.wp_proof swift.lki.lightKeyInfo.getConflictCmds.wp_proof

end link

end Perennial.github_com.imdea_software.swiftpaxos
