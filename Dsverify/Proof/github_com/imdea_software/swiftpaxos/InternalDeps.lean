/-
The kit's own callees that its shared lemma modules (defs tier) call, as hypotheses (CLAUDE.md,
"Import tiers": a module below the linking ones sees a proved function through its spec only):
`client.GhostStep` (`swift/GhostSteps.lean`: the replicas' ghost steps) and the quorums' `Size` and
`Contains` methods (`replica/MsgSetQ.lean`, `swift/FastAckDefs.lean`,
`swift/HandleProposeProofDefs.lean`: a quorum interface's dispatch) and concurrent-map's pinned
`IterCb` (`swift/StopDescsProof.lean`). The proofs take
`SwiftKitDeps` as an instance argument (a section `variable [SwiftKitDeps]` beside `SwiftHyps`, in every kit module
above the ones proving its fields), and the kit's `Link` closes it with their proofs
(`InternalDepsLinked.lean`: `swiftKitDeps_holds`, a local instance of
`examples/swiftnet/Link.lean` and `TopLevelRobustness.lean`). No `instance` of it exists.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.GhostDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumSpecs
public import Dsverify.Proof.github_com.orcaman.concurrent_map.IterCbPDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- The kit's callees of its shared lemma modules (the file header). -/
class SwiftKitDeps [GoGlobalContext] [hG : HeapGS HasLC.hasLC netDistGF] [go.Semantics]
    [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF]
    [SwiftNetDeps netDistGF] : Prop where
  ghostStep : ∀ [client.Assumptions], client.GhostStep.specG (hG := hG)
  majSize : ∀ [replica.Assumptions], replica.Majority.Size.spec (hG := hG)
  majContains : ∀ [replica.Assumptions], replica.Majority.Contains.spec (hG := hG)
  tqSize : ∀ [replica.Assumptions], replica.ThreeQuarters.Size.spec (hG := hG)
  tqContains : ∀ [replica.Assumptions], replica.ThreeQuarters.Contains.spec (hG := hG)
  qSize : ∀ [replica.Assumptions], replica.Quorum.Size.spec (hG := hG)
  qContains : ∀ [replica.Assumptions], replica.Quorum.Contains.spec (hG := hG)
  iterCbVP : ∀ [github_com.orcaman.concurrent_map.Assumptions] [sync.Assumptions],
    github_com.orcaman.concurrent_map.ConcurrentMap.IterCbVP.spec (GF := netDistGF)

end Perennial.github_com.imdea_software.swiftpaxos
