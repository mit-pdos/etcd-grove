/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/idutil/lowbit.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.idutil.lowbit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.idutil.Assumptions]

private theorem pow_shift_aux : ∀ k, k < 65 → (2 ^ 64 - 1) >>> (64 - k) = 2 ^ k - 1 := by
  decide

/-- `math.MaxUint64 >> (64 - n)` is `2 ^ n - 1` for `n ≤ 64` (shift counts not truncated: `n = 0`
shifts by 64, giving 0). -/
theorem maxUint64_shiftr (n : w64) (Hn : uint.Z n ≤ 64) :
    (W64 18446744073709551615 >>> (W64 64 - n)) = W64 (2 ^ uint.nat n - 1) := by
  apply BitVec.eq_of_toNat_eq
  have hk : n.toNat ≤ 64 := by have := Hn; simp [uint.Z] at this ⊢; omega
  have h1 : (W64 64 - n).toNat = 64 - n.toNat := by
    rw [BitVec.toNat_sub]; simp; omega
  rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, h1]
  have hu : uint.nat n = n.toNat := rfl
  rw [hu]
  have h2 : (W64 18446744073709551615).toNat = 2 ^ 64 - 1 := rfl
  rw [h2, pow_shift_aux _ (by omega)]
  have h3 : 2 ^ n.toNat - 1 < 2 ^ 64 := by
    have : 2 ^ n.toNat ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) hk
    omega
  have hP1 : 1 ≤ 2 ^ BitVec.toNat n := Nat.one_le_two_pow
  have hP2 : 2 ^ BitVec.toNat n ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) hk
  unfold W64
  simp only [BitVec.toNat_ofInt]
  rw [show ((2:Int) ^ BitVec.toNat n) = ((2 ^ BitVec.toNat n : Nat) : Int) from by norm_cast,
    show (((2:Nat) ^ 64 : Nat) : Int) = 18446744073709551616 from rfl]
  generalize 2 ^ BitVec.toNat n = P at hP1 hP2 h3 ⊢
  have : (2:Nat) ^ 64 = 18446744073709551616 := rfl
  omega

theorem idutil.lowbit.wp_proof : idutil.lowbit.spec (GF := GF) (hG := hG) := by
  intro x n Hn
  wp_start as -
  wp_auto
  rw [maxUint64_shiftr n Hn]
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
