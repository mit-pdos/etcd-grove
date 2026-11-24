/-
The kit's own callees of its shared lemma modules (`InternalDeps.lean`: `SwiftKitDeps`), closed by
their proofs (`client/Ghost.lean`, `replica/QuorumArith.lean`, `replica/QuorumMaps.lean`, concurrent-map's `IterCbP.lean`). A local
instance of the kit's top modules (`examples/swiftnet/Link.lean`, `TopLevelRobustness.lean`); no
`instance` of it exists.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.InternalDeps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Ghost
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumArith
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumMaps
public import Dsverify.Proof.github_com.orcaman.concurrent_map.IterCbP

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section heap
variable [GoGlobalContext] [hG : HeapGS HasLC.hasLC netDistGF] [go.Semantics]
variable [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF]
  [SwiftNetDeps netDistGF]

theorem swiftKitDeps_holds : SwiftKitDeps where
  majSize := replica.Majority.Size.wp_proof
  majContains := replica.Majority.Contains.wp_proof
  tqSize := replica.ThreeQuarters.Size.wp_proof
  tqContains := replica.ThreeQuarters.Contains.wp_proof
  qSize := replica.Quorum.Size.wp_proof
  qContains := replica.Quorum.Contains.wp_proof
  iterCbVP := github_com.orcaman.concurrent_map.ConcurrentMap.IterCbVP.wp_proof

end heap

end Perennial.github_com.imdea_software.swiftpaxos
