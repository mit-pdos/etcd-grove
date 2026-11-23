/-
The linked results of `UpdateLogs.lean` (moved out of it for the import tiers, CLAUDE.md
"Import tiers": a proof file sees its callees through their specs; this linking module composes the
proofs).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.UpdateLogs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DepHash
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecordLeaderHash
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HashLogLinked

@[expose] public section
noncomputable section
set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv
attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section link
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions] [crypto.sha256.Assumptions] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]

/-- `updateLogs` linked. -/
theorem swift.Replica.wp_updateLogs : swift.Replica.updateLogs.specT :=
  swift.Replica.updateLogs.wp_proof swift.keysOf.wp_proofNS swift.wp_NewHashLog
    swift.HashLog.wp_Update

/-- `recordLeaderHash` linked (round 19, change log C22). -/
theorem swift.Replica.wp_recordLeaderHash : swift.Replica.recordLeaderHash.specT :=
  swift.Replica.recordLeaderHash.wp_proofT swift.Replica.wp_updateLogs

end link

end Perennial.github_com.imdea_software.swiftpaxos
