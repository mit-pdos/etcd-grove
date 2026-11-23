/-
The linked results of `DepHash.lean` (moved out of it for the import tiers, CLAUDE.md
"Import tiers": a proof file sees its callees through their specs; this linking module composes the
proofs).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DepHash
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Key
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

/-- `getDepAndHashes` linked (its callees proved: keys.go's `lightKeyInfo`, the hash logs). -/
theorem swift.Replica.wp_getDepAndHashes : swift.Replica.getDepAndHashes.specI :=
  swift.Replica.getDepAndHashes.wp_proof swift.keysOf.wp_proofNS
    swift.lki.newLightKeyInfo.wp_proof swift.lki.lightKeyInfo.add.wp_proof
    swift.lki.lightKeyInfo.getConflictCmds.wp_proof swift.wp_NewHashLog swift.HashLog.wp_Append

end link

end Perennial.github_com.imdea_software.swiftpaxos
