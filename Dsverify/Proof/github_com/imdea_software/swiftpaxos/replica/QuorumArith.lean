/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/QuorumArith.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`Leader`, `NextBallotOf`, `NewMajorityOf`, `NewThreeQuartersOf`, and the `Majority` /
`ThreeQuarters` methods: proofs, and the exact values of the int32 arithmetic.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumArithDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace replica.quorum

end replica.quorum

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF]
variable [sem : go.Semantics] [replica.Assumptions] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]

set_option goose.wp.extras true

open replica.quorum

theorem replica.Leader.wp_proof : replica.Leader.spec := by
  intro b n
  wp_start as %Hn
  wp_auto
  rw [if_neg (by
    have : sint.Z (W32 (sint.Z n)) = sint.Z n := by word
    omega)]
  wp_auto
  iapply HΦ; itrivial

theorem replica.NextBallotOf.wp_proof : replica.NextBallotOf.spec := by
  intro rid old n
  wp_start as %Hn
  wp_auto
  rw [if_neg (by
    have : sint.Z (W32 (sint.Z n)) = sint.Z n := by word
    omega)]
  wp_auto
  rw [show (W32 1 : w32) = 1 by rfl]
  iapply HΦ; itrivial

theorem replica.NewMajorityOf.wp_proof : replica.NewMajorityOf.spec := by
  intro N
  wp_start as %HN
  wp_auto
  rw [show BitVec.sdiv (W64 (N : Int)) (W64 2) + W64 1 = W64 ((N : Int) / 2 + 1) by word]
  iapply HΦ; itrivial

theorem replica.NewThreeQuartersOf.wp_proof : replica.NewThreeQuartersOf.spec := by
  intro N
  wp_start as %HN
  wp_auto
  have e : W64 3 * W64 (N : Int) = W64 (3 * (N : Int)) := by simp only [W64, BitVec.ofInt_mul]
  have e2 : BitVec.sdiv (W64 (3 * (N : Int))) (W64 4) + W64 1 = W64 (3 * (N : Int) / 4 + 1) := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_add, BitVec.toInt_sdiv]
    rw [show (W64 (3 * (N:Int))).toInt = 3 * N from sint_W64 _ (by omega) (by omega)]
    rw [show (W64 4).toInt = 4 by rfl, show (W64 1).toInt = 1 by rfl]
    rw [show (W64 (3 * (N:Int) / 4 + 1)).toInt = 3 * (N:Int) / 4 + 1 from
      sint_W64 _ (by omega) (by omega)]
    rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
    rw [Int.bmod_eq_of_le (n := 3 * (N:Int) / 4) (by omega) (by omega)]
    rw [Int.bmod_eq_of_le (by omega) (by omega)]
  rw [e, e2]
  iapply HΦ; itrivial

theorem replica.Majority.Size.wp_proof : replica.Majority.Size.spec := by
  intro m
  wp_start
  wp_auto
  iapply HΦ; itrivial

theorem replica.Majority.Contains.wp_proof : replica.Majority.Contains.spec := by
  intro m r
  wp_start
  wp_auto
  iapply HΦ; itrivial

theorem replica.ThreeQuarters.Size.wp_proof : replica.ThreeQuarters.Size.spec := by
  intro m
  wp_start
  wp_auto
  iapply HΦ; itrivial

theorem replica.ThreeQuarters.Contains.wp_proof : replica.ThreeQuarters.Contains.spec := by
  intro m r
  wp_start
  wp_auto
  iapply HΦ; itrivial

end proofs

end Perennial.github_com.imdea_software.swiftpaxos

end
