/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/QuorumLink.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`replica/quorum.go`'s (and `Leader`, `NextBallotOf`'s) linked results: each proof applied to its
callees' linked results. Every callee is in this package (`subsets`' `delete` now goes through
the underlying map type, fix3: `wp_mapDelete`, no gap).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumSystem
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumSubsets
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumArith
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumMaps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumSet

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section link
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [replica.Assumptions]

theorem replica.wp_Leader : replica.Leader.spec := replica.Leader.wp_proof
theorem replica.wp_NextBallotOf : replica.NextBallotOf.spec := replica.NextBallotOf.wp_proof
theorem replica.wp_NewMajorityOf : replica.NewMajorityOf.spec := replica.NewMajorityOf.wp_proof
theorem replica.wp_NewThreeQuartersOf : replica.NewThreeQuartersOf.spec :=
  replica.NewThreeQuartersOf.wp_proof
theorem replica.Majority.wp_Size : replica.Majority.Size.spec := replica.Majority.Size.wp_proof
theorem replica.Majority.wp_Contains : replica.Majority.Contains.spec :=
  replica.Majority.Contains.wp_proof
theorem replica.ThreeQuarters.wp_Size : replica.ThreeQuarters.Size.spec :=
  replica.ThreeQuarters.Size.wp_proof
theorem replica.ThreeQuarters.wp_Contains : replica.ThreeQuarters.Contains.spec :=
  replica.ThreeQuarters.Contains.wp_proof
theorem replica.wp_NewQuorum : replica.NewQuorum.spec := replica.NewQuorum.wp_proof
theorem replica.wp_NewQuorumsOfLeader : replica.NewQuorumsOfLeader.spec :=
  replica.NewQuorumsOfLeader.wp_proof
theorem replica.Quorum.wp_Size : replica.Quorum.Size.spec := replica.Quorum.Size.wp_proof
theorem replica.Quorum.wp_Contains : replica.Quorum.Contains.spec :=
  replica.Quorum.Contains.wp_proof
theorem replica.Quorum.wp_copy : replica.Quorum.copy.spec :=
  replica.Quorum.copy.wp_proof replica.wp_NewQuorum
theorem replica.wp_subsets : replica.subsets.spec := replica.subsets.wp_proof replica.Quorum.wp_copy
theorem replica.wp_newQuorumSetAdvance : replica.newQuorumSetAdvance.spec :=
  replica.newQuorumSetAdvance.wp_proof replica.wp_NewQuorum replica.wp_NewQuorumsOfLeader
    replica.wp_subsets
theorem replica.wp_NewQuorumSet : replica.NewQuorumSet.spec :=
  replica.NewQuorumSet.wp_proof replica.wp_newQuorumSetAdvance
theorem replica.QuorumSet.wp_AQ : replica.QuorumSet.AQ.spec :=
  replica.QuorumSet.AQ.wp_proof replica.wp_Leader
theorem replica.wp_NewQuorumsFromFile : replica.NewQuorumsFromFile.spec :=
  replica.NewQuorumsFromFile.wp_proof
theorem replica.wp_NewQuorumSystem : replica.NewQuorumSystem.spec :=
  replica.NewQuorumSystem.wp_proof replica.wp_NewQuorumsFromFile replica.wp_NewQuorumSet
theorem replica.QuorumSystem.wp_BallotAt : replica.QuorumSystem.BallotAt.spec :=
  replica.QuorumSystem.BallotAt.wp_proof
theorem replica.QuorumSystem.wp_NumAQ : replica.QuorumSystem.NumAQ.spec :=
  replica.QuorumSystem.NumAQ.wp_proof
theorem replica.QuorumSystem.wp_AQ : replica.QuorumSystem.AQ.spec :=
  replica.QuorumSystem.AQ.wp_proof replica.QuorumSet.wp_AQ
theorem replica.QuorumSystem.wp_SameHigher : replica.QuorumSystem.SameHigher.spec :=
  replica.QuorumSystem.SameHigher.wp_proof replica.wp_Leader

end link

end Perennial.github_com.imdea_software.swiftpaxos

end
