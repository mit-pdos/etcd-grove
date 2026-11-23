/-
The definitions, specs and lemmas of `QuorumOk.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumLemmas
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumArithDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- `MaxBallot(N)` (R-Q1): `MaxInt32 - 2N`. -/
def replica.maxBallot (N : Nat) : w32 := W32 2147483647 - W32 2 * W32 (sint.Z (W64 (N : Int)))

theorem replica.maxBallot_val (N : Nat) (hN : N ≤ 7) :
    sint.Z (replica.maxBallot N) = 2147483647 - 2 * (N : Int) := by
  unfold replica.maxBallot
  have h1 : sint.Z (W64 (N : Int)) = N := replica.quorum.sint_W64 _ (by omega) (by omega)
  rw [h1]
  have h2 : (W32 2147483647 - W32 2 * W32 (N : Int) : w32) = W32 (2147483647 - 2 * (N : Int)) := by
    match N, hN with
    | 0, _ => decide
    | 1, _ => decide
    | 2, _ => decide
    | 3, _ => decide
    | 4, _ => decide
    | 5, _ => decide
    | 6, _ => decide
    | 7, _ => decide
  rw [h2]
  exact replica.quorum.sint_W32 _ (by omega) (by omega)

/-- `|srem x n| < n`: a non-negative `Leader(x, n)` is below `n`. -/
theorem replica.srem_lt (x : w32) (n : Nat) (hn : 0 < n ∧ n < 2 ^ 31)
    (h0 : 0 ≤ sint.Z (BitVec.srem x (W32 (n : Int)))) :
    BitVec.srem x (W32 (n : Int)) = replica.quorum.w32n (sint.Z (BitVec.srem x (W32 (n : Int)))).toNat ∧
      (sint.Z (BitVec.srem x (W32 (n : Int)))).toNat < n := by
  have hNz : sint.Z (W32 (n : Int)) = n := by word
  have h := BitVec.toInt_srem x (W32 (n : Int))
  have hlt : sint.Z (BitVec.srem x (W32 (n : Int))) < n := by
    show (BitVec.srem x (W32 (n : Int))).toInt < n
    rw [h, show (W32 (n : Int)).toInt = n from hNz]
    exact Int.tmod_lt_of_pos _ (by omega)
  refine ⟨?_, by omega⟩
  apply BitVec.eq_of_toInt_eq
  show sint.Z _ = sint.Z _
  unfold replica.quorum.w32n
  rw [Int.toNat_of_nonneg h0, replica.quorum.sint_W32 _ (by omega) (by omega)]

/-- The range check of `SameHigherOk` (helper; kept apart so that no `lqs` term is unfolded). -/
theorem replica.sameHigher_range (X : w64) (M : w32) (N : Nat) (hN : N ≤ 7)
    (hlo : ¬ sint.Z X < sint.Z (W64 0)) (hhi : ¬ sint.Z (W64 (sint.Z M)) < sint.Z X)
    (hM : M = replica.maxBallot N) :
    0 ≤ sint.Z (W32 (sint.Z X)) ∧ sint.Z (W32 (sint.Z X)) ≤ sint.Z M := by
  subst hM
  have hM2 := replica.maxBallot_val N hN
  have hz : sint.Z (W64 0) = 0 := rfl
  have hmx : sint.Z (W64 (sint.Z (replica.maxBallot N))) = sint.Z (replica.maxBallot N) :=
    replica.quorum.sint_W64 _ (by omega) (by omega)
  have a1 : 0 ≤ sint.Z X := by omega
  have a2 : sint.Z X ≤ sint.Z (replica.maxBallot N) := by omega
  have e : sint.Z (W32 (sint.Z X)) = sint.Z X := replica.quorum.sint_W32 (sint.Z X) (by omega) (by omega)
  rw [e]
  exact ⟨a1, a2⟩

/-- `SameHigherOk`'s ballot `sameAs + (higherThan / m) * m * N` (int64, no overflow) is
`sameAs` mod `N` (D56 N1-c: the same leader). -/
theorem replica.sameHigher_emod (a h : w32) (m N : Nat) (hm : 1 ≤ m ∧ m ≤ 35) (hN : 1 ≤ N ∧ N ≤ 7) :
    sint.Z (W64 (sint.Z a) + BitVec.sdiv (W64 (sint.Z h)) (W64 (m : Int)) * W64 (m : Int) *
      W64 (N : Int)) % (N : Int) = sint.Z a % (N : Int) := by
  have ha1 : -2 ^ 31 ≤ sint.Z a ∧ sint.Z a < 2 ^ 31 := ⟨by word, by word⟩
  have hh1 : -2 ^ 31 ≤ sint.Z h ∧ sint.Z h < 2 ^ 31 := ⟨by word, by word⟩
  have hA : (W64 (sint.Z a)).toInt = sint.Z a := replica.quorum.sint_W64 _ (by omega) (by omega)
  have hH : (W64 (sint.Z h)).toInt = sint.Z h := replica.quorum.sint_W64 _ (by omega) (by omega)
  have hM : (W64 (m : Int)).toInt = m := replica.quorum.sint_W64 _ (by omega) (by omega)
  have hNz : (W64 (N : Int)).toInt = N := replica.quorum.sint_W64 _ (by omega) (by omega)
  have hqb : ((sint.Z h).tdiv m).natAbs ≤ (sint.Z h).natAbs := Int.natAbs_tdiv_le_natAbs _ _
  generalize hq : (sint.Z h).tdiv m = q at hqb
  have hq1 : -2 ^ 31 ≤ q ∧ q ≤ 2 ^ 31 := by omega
  have hD : (BitVec.sdiv (W64 (sint.Z h)) (W64 (m : Int))).toInt = q := by
    rw [BitVec.toInt_sdiv, hH, hM, hq, Int.bmod_eq_of_le] <;> omega
  have hqm : (q * m).natAbs ≤ 2 ^ 31 * 35 := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (by omega) (by simp; omega)
  generalize hqm' : q * (m : Int) = t at hqm
  have hT : (BitVec.sdiv (W64 (sint.Z h)) (W64 (m : Int)) * W64 (m : Int)).toInt = t := by
    rw [BitVec.toInt_mul, hD, hM, hqm', Int.bmod_eq_of_le] <;> omega
  have htn : (t * N).natAbs ≤ 2 ^ 31 * 35 * 7 := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul hqm (by simp; omega)
  generalize htn' : t * (N : Int) = u at htn
  have hU : (BitVec.sdiv (W64 (sint.Z h)) (W64 (m : Int)) * W64 (m : Int) * W64 (N : Int)).toInt
      = u := by
    rw [BitVec.toInt_mul, hT, hNz, htn', Int.bmod_eq_of_le] <;> omega
  show (W64 (sint.Z a) + _).toInt % _ = _
  rw [BitVec.toInt_add, hA, hU, Int.bmod_eq_of_le (by omega) (by omega), ← htn', ← hqm',
    Int.add_mul_emod_self_right]

/-- `SameHigherOk`'s returned ballot (`X` checked in `[0, MaxBallot(N)]`) is `sameAs` mod `N`. -/
theorem replica.sameHigher_leader (a h : w32) (M N : Nat) (X : w64)
    (hX : X = W64 (sint.Z a) + BitVec.sdiv (W64 (sint.Z h)) (W64 (M : Int)) * W64 (M : Int) *
      W64 (N : Int)) (hm : 1 ≤ M ∧ M ≤ 35) (hN : 1 ≤ N ∧ N ≤ 7)
    (hlo : ¬ sint.Z X < sint.Z (W64 0))
    (hhi : ¬ sint.Z (W64 (sint.Z (replica.maxBallot N))) < sint.Z X) :
    sint.Z (W32 (sint.Z X)) % (N : Int) = sint.Z a % (N : Int) := by
  have hr := replica.sameHigher_range X _ N hN.2 hlo hhi rfl
  have hM2 := replica.maxBallot_val N hN.2
  have hz : sint.Z (W64 0) = 0 := rfl
  have hmx : sint.Z (W64 (sint.Z (replica.maxBallot N))) = sint.Z (replica.maxBallot N) :=
    replica.quorum.sint_W64 _ (by omega) (by omega)
  have e : sint.Z (W32 (sint.Z X)) = sint.Z X :=
    replica.quorum.sint_W32 _ (by omega) (by omega)
  rw [e, hX]
  exact replica.sameHigher_emod a h M N hm hN

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF]
variable [sem : go.Semantics] [replica.Assumptions] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]

open replica.quorum

/-- `MaxBallot(N)`. -/
abbrev replica.MaxBallot.spec : Prop :=
  ∀ (N : Nat),
  {{ (⌜1 ≤ N ∧ N ≤ 7⌝ : IProp netDistGF) }}
    (App (Val (@! replica.MaxBallot)) (Val #(W64 (N : Int))))
  {{ RET #(replica.maxBallot N); True }}

/-- `NextBallotOfOk(rid, old, N)` of a replica id `rid < N`: `ok` gives a ballot in
`[0, MaxBallot(N)]`. -/
abbrev replica.NextBallotOfOk.spec : Prop :=
  ∀ (rid old : w32) (N : Nat),
  {{ (⌜1 ≤ N ∧ N ≤ 7 ∧ 0 ≤ sint.Z rid ∧ sint.Z rid < N⌝ : IProp netDistGF) }}
    (App (App (App (Val (@! replica.NextBallotOfOk)) (Val #rid)) (Val #old)) (Val #(W64 (N : Int))))
  {{ (nb : w32) (ok : Bool), RET (PairV #nb #ok);
      ⌜ok = true → 0 ≤ sint.Z nb ∧ sint.Z nb ≤ sint.Z (replica.maxBallot N) ∧
        sint.Z nb % (N : Int) = sint.Z rid⌝ }}

/-- `sys.SameHigherOk(sameAs, higherThan)`: `ok` gives a ballot in `[0, MaxBallot(N)]`. -/
abbrev replica.QuorumSystem.SameHigherOk.spec : Prop :=
  ∀ (sys : Loc) (N : Nat) (sameAs higherThan : w32),
  {{ isQS sys N }}
    (App (App (Val (sys @!! go.GoType.PointerType replica.QuorumSystem.ty @!! go!"SameHigherOk"))
      (Val #sameAs)) (Val #higherThan))
  {{ (b : w32) (ok : Bool), RET (PairV #b #ok);
      ⌜ok = true → 0 ≤ sint.Z b ∧ sint.Z b ≤ sint.Z (replica.maxBallot N) ∧
        sint.Z b % (N : Int) = sint.Z sameAs % (N : Int)⌝ }}

end specs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF]
variable [sem : go.Semantics] [replica.Assumptions] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]

set_option goose.wp.extras true

open replica.quorum

end proofs

end Perennial.github_com.imdea_software.swiftpaxos

end
