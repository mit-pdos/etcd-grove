/-
The definitions, specs and lemmas of `QuorumArith.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

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
variable [sem : go.Semantics] [replica.Assumptions] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]

set_option goose.wp.extras true

open replica.quorum

end proofs

end Perennial.github_com.imdea_software.swiftpaxos

end
