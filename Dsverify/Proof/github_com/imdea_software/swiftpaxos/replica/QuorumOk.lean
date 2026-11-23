/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/QuorumOk.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
R-Q1's bounded ballot arithmetic (round 25, sv-swc; the swift run loop's `recBal` arm,
`recoveryBallot`): `MaxBallot`, `NextBallotOfOk`, `QuorumSystem.SameHigherOk`, specs and proofs.
Each `ok` result is a ballot in `[0, MaxBallot(N)]` (`replica.maxBallot N`).

`MaxBallot` is `2147483647 - 2*int32(repNum)` (the fork writes `math.MaxInt32` as its literal,
D28: Goose's `math.MaxInt32` is an opaque `axiom val`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumLemmas
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumArithDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumOkDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF]
variable [sem : go.Semantics] [replica.Assumptions] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]

open replica.quorum

end specs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF]
variable [sem : go.Semantics] [replica.Assumptions] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]

set_option goose.wp.extras true

open replica.quorum

theorem replica.MaxBallot.wp_proof : replica.MaxBallot.spec := by
  intro N
  wp_start as %HN
  wp_auto
  rw [show (W32 2147483647 - W32 2 * W32 (sint.Z (W64 (N : Int))) : w32) = replica.maxBallot N from rfl]
  iapply HΦ; itrivial

theorem replica.NextBallotOfOk.wp_proof (wp_Max : replica.MaxBallot.spec)
    (wp_Next : replica.NextBallotOf.spec) : replica.NextBallotOfOk.spec := by
  intro rid old N
  wp_start as %HN
  obtain ⟨hN1, hN7, hr0, hrN⟩ := HN
  have hM := replica.maxBallot_val N hN7
  have hN64 : sint.Z (W64 (N : Int)) = N := sint_W64 _ (by omega) (by omega)
  try wp_auto
  wp_if_destruct
  · -- `old < 0`
    try wp_auto
    iapply HΦ; ipureintro; intro h; cases h
  · wp_apply (wp_Max N)
    · ipureintro; omega
    wp_if_destruct
    · skip
      iapply HΦ; ipureintro; intro h; cases h
    · wp_apply wp_Next
      · ipureintro; omega
      wp_apply (wp_Max N)
      · ipureintro; omega
      rw [hN64]
      wp_if_destruct
      · skip
        iapply HΦ; ipureintro; intro h; cases h
      · skip
        iapply HΦ; ipureintro; intro _
        rename_i h1 h2 h3
        have hz : sint.Z (W32 0) = 0 := rfl
        have ho : 0 ≤ sint.Z old := by omega
        have hv := nextBallot_val rid old N ⟨by omega, by omega⟩ ho hr0 (by
          have : sint.Z old / N ≤ sint.Z old := Int.ediv_le_self _ ho
          have : sint.Z old / N * N ≤ sint.Z old := Int.ediv_mul_le _ (by omega)
          rw [Int.add_mul]; omega)
        refine ⟨?_, by omega, ?_⟩
        · rw [hv]
          have : 0 ≤ sint.Z old / N := Int.ediv_nonneg ho (by omega)
          have : 0 ≤ (sint.Z old / N + 1) * (N : Int) := Int.mul_nonneg (by omega) (by omega)
          omega
        · -- D56 N1-c: the next ballot is `rid`'s
          rw [hv, Int.add_comm, Int.add_mul_emod_self_right]
          exact Int.emod_eq_of_lt hr0 (by omega)

theorem replica.QuorumSystem.SameHigherOk.wp_proof (wp_Leader : replica.Leader.spec)
    (wp_Max : replica.MaxBallot.spec) : replica.QuorumSystem.SameHigherOk.spec := by
  intro sys N sameAs higherThan
  wp_start as #Hs
  iunfold isQS at Hs
  icases Hs with ⟨%qs, #Hs, #Hqs⟩
  iStructNamed Hs
  wp_auto
  iunfold qsIs at Hqs
  icases Hqs with ⟨%HN, #Hqs⟩
  have hN64 : sint.Z (W64 (N : Int)) = N := sint_W64 _ (by omega) (by omega)
  have hM := replica.maxBallot_val N HN.2
  ihave Hacc0 := qsOwn_acc qs N (lqs N) DFrac.discard 0 (by omega) $$ Hqs
  icases Hacc0 with ⟨%m, %p0, #Hm, -, %Hdom, -, -⟩
  wp_apply (wp_map_len (K := w32) (V := Loc) (t := replica.QuorumSet.ty)) $$ [$Hm] as -
  rw [lqs_size m N (by omega) Hdom]
  wp_apply wp_Leader
  · ipureintro; omega
  rw [hN64]
  wp_if_destruct
  · -- `l < 0`
    try wp_auto
    iapply HΦ; ipureintro; intro h; cases h
  · have hl0' : 0 ≤ sint.Z (BitVec.srem sameAs (W32 (N : Int))) := by
      have hc : sint.Z (W32 0) = 0 := rfl
      have : ¬ sint.Z (BitVec.srem sameAs (W32 (N : Int))) < sint.Z (W32 0) := Hif
      omega
    obtain ⟨hlw, hlN⟩ := replica.srem_lt sameAs N ⟨by omega, by omega⟩ hl0'
    generalize hln : (sint.Z (BitVec.srem sameAs (W32 (N : Int)))).toNat = ln at hlw hlN
    rw [hlw]
    ihave Hacc := qsOwn_acc qs N (lqs N) DFrac.discard ln hlN $$ Hqs
    icases Hacc with ⟨%m', %p, #Hm', %Hp, %Hdom', #Hl, -⟩
    iunfold lqsOwn at Hl
    icases Hl with ⟨%mi, #Hmi, %Hdomi, -⟩
    obtain ⟨hpos, h35⟩ := numAQ_pos N ln HN hlN
    unfold numAQ at hpos h35
    have hL64 : sint.Z (W64 ((lqs N ln).length : Int)) = (lqs N ln).length :=
      sint_W64 _ (by omega) (by omega)
    wp_apply (wp_map_lookup1 (K := w32) (V := Loc)) $$ [$Hm'] as -
    rw [Hp]
    simp only [Option.getD_some]
    wp_apply (wp_map_len (K := w32) (V := Loc) (t := replica.QuorumsOfLeader.ty)) $$ [$Hmi] as -
    rw [lqs_size mi _ Hdomi.1 Hdomi.2]
    rw [if_neg (by rw [hL64]; omega)]
    wp_auto
    wp_apply (wp_map_len (K := w32) (V := Loc) (t := replica.QuorumSet.ty)) $$ [$Hm'] as -
    rw [lqs_size m' N (by omega) Hdom']
    wp_if_destruct
    · iapply HΦ; ipureintro; intro h; cases h
    · wp_apply (wp_map_len (K := w32) (V := Loc) (t := replica.QuorumSet.ty)) $$ [$Hm'] as -
      rw [lqs_size m' N (by omega) Hdom']
      wp_apply (wp_Max N)
      · ipureintro; omega
      wp_if_destruct
      · iapply HΦ; ipureintro; intro h; cases h
      · iapply HΦ; ipureintro; intro _
        rename_i hlo _
        refine ⟨(replica.sameHigher_range _ _ N HN.2 hlo Hif rfl).1,
          (replica.sameHigher_range _ _ N HN.2 hlo Hif rfl).2, ?_⟩
        exact replica.sameHigher_leader sameAs higherThan _ N _ rfl ⟨hpos, h35⟩ HN hlo Hif

/-- `MaxBallot`, linked. -/
theorem replica.wp_MaxBallot : replica.MaxBallot.spec (hG := hG) :=
  replica.MaxBallot.wp_proof

end proofs

end Perennial.github_com.imdea_software.swiftpaxos

end
