/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/QuorumArith.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`Leader`, `NextBallotOf`, `NewMajorityOf`, `NewThreeQuartersOf`, and the `Majority` /
`ThreeQuarters` methods: proofs, and the exact values of the int32 arithmetic.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumSpecs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace replica.quorum

/-- `Leader(b, N)` of a non-negative ballot is `b mod N`. -/
theorem leader_val (b : w32) (N : Nat) (hN : 0 < N ∧ N < 2 ^ 31) (hb : 0 ≤ sint.Z b) :
    sint.Z (BitVec.srem b (W32 (N : Int))) = sint.Z b % N := by
  have hNz : sint.Z (W32 (N : Int)) = N := by word
  have h := BitVec.toInt_srem b (W32 (N : Int))
  show (BitVec.srem b (W32 (N : Int))).toInt = b.toInt % N
  rw [h]
  rw [show (W32 (N : Int)).toInt = N from hNz]
  rw [Int.tmod_eq_emod_of_nonneg hb]

/-- `NextBallotOf(rid, old, N)` when the result fits an int32. -/
theorem nextBallot_val (rid old : w32) (N : Nat) (hN : 0 < N ∧ N < 2 ^ 31)
    (ho : 0 ≤ sint.Z old) (hr : 0 ≤ sint.Z rid)
    (hfit : (sint.Z old / N + 1) * N + sint.Z rid < 2 ^ 31) :
    sint.Z ((BitVec.sdiv old (W32 (N : Int)) + 1) * W32 (N : Int) + rid) =
      (sint.Z old / N + 1) * N + sint.Z rid := by
  have hNz : sint.Z (W32 (N : Int)) = N := by word
  have hd : sint.Z (BitVec.sdiv old (W32 (N : Int))) = sint.Z old / N := by
    have h := BitVec.toInt_sdiv old (W32 (N : Int))
    show (BitVec.sdiv old (W32 (N : Int))).toInt = _
    rw [h, show (W32 (N : Int)).toInt = N from hNz]
    rw [Int.tdiv_eq_ediv_of_nonneg ho]
    have := Int.ediv_le_self (N : Int) ho
    have := Int.ediv_nonneg ho (by omega : (0 : Int) ≤ N)
    have : sint.Z old < 2 ^ 31 := by word
    rw [Int.bmod_eq_of_le] <;> omega
  have hq0 : 0 ≤ sint.Z old / N := Int.ediv_nonneg ho (by omega)
  generalize hD : BitVec.sdiv old (W32 (N : Int)) = D at hd ⊢
  generalize hW : W32 (N : Int) = W at hNz ⊢
  have e1 : D = W32 (sint.Z old / N) := by rw [← hd]; word
  have e2 : W = W32 (N : Int) := by rw [← hNz]; word
  have e3 : rid = W32 (sint.Z rid) := by word
  have : (D + 1) * W + rid = W32 ((sint.Z old / N + 1) * N + sint.Z rid) := by
    rw [e1, e2]; conv => lhs; rw [e3]
    simp only [W32, BitVec.ofInt_add, BitVec.ofInt_mul]; rfl
  rw [this]
  have : 0 ≤ (sint.Z old / N + 1) * (N : Int) := Int.mul_nonneg (by omega) (by omega)
  exact sint_W32 _ (by omega) hfit

theorem srem_nat (x : w32) (n : Nat) (hn : 0 < n ∧ n < 2 ^ 31) (hx : 0 ≤ sint.Z x) :
    BitVec.srem x (W32 (n : Int)) = w32n ((sint.Z x).toNat % n) := by
  apply BitVec.eq_of_toInt_eq
  have h1 := leader_val x n hn hx
  show sint.Z _ = sint.Z _
  rw [h1]
  unfold w32n
  have : sint.Z x < 2 ^ 31 := by word
  have hm : (sint.Z x).toNat % n < n := Nat.mod_lt _ hn.1
  rw [sint_W32 _ (by omega) (by omega)]
  have e : (((sint.Z x).toNat % n : Nat) : Int) = sint.Z x % n := by
    rw [Int.natCast_emod, Int.toNat_of_nonneg hx]
  omega

theorem sdiv_nat (x : w32) (n : Nat) (hn : 0 < n ∧ n < 2 ^ 31) (hx : 0 ≤ sint.Z x) :
    sint.Z (BitVec.sdiv x (W32 (n : Int))) = sint.Z x / n := by
  have hNz : sint.Z (W32 (n : Int)) = n := by word
  have h := BitVec.toInt_sdiv x (W32 (n : Int))
  show (BitVec.sdiv x (W32 (n : Int))).toInt = _
  rw [h, show (W32 (n : Int)).toInt = n from hNz]
  rw [Int.tdiv_eq_ediv_of_nonneg hx]
  have := Int.ediv_le_self (n : Int) hx
  have := Int.ediv_nonneg hx (by omega : (0 : Int) ≤ n)
  have : sint.Z x < 2 ^ 31 := by word
  rw [Int.bmod_eq_of_le] <;> omega

theorem toNat_ediv (x : Int) (N : Nat) (h : 0 ≤ x) : (x / (N : Int)).toNat = x.toNat / N := by
  have hx : x = ((x.toNat : Nat) : Int) := (Int.toNat_of_nonneg h).symm
  rw [hx]
  norm_cast

end replica.quorum

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF]
variable [sem : go.Semantics] [replica.Assumptions] [SwiftNetPkgState netDistGF]

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
