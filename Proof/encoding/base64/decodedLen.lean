/-
Proof of `decodedLen` over its translated body (`encoding/base64`, go1.27.3). Lean-first
(prove-authcrypto, 2026-11-21).
-/
module

public import Spec.encoding.base64.decodedLen
public import Proof.encoding.base64.Lemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.encoding.base64.Assumptions]

theorem base64.decLen_pad_eq (n : w64) (hn0 : 0 ≤ sint.Z n) :
    BitVec.sdiv n (W64 4) * W64 3 = W64 ((sint.nat n / 4 * 3 : Nat) : Int) := by
  word

theorem base64.decLen_nopad_eq (n : w64) (hn0 : 0 ≤ sint.Z n) :
    BitVec.sdiv n (W64 4) * W64 3 + BitVec.sdiv (BitVec.srem n (W64 4) * W64 6) (W64 8) =
      W64 ((sint.nat n / 4 * 3 + sint.nat n % 4 * 6 / 8 : Nat) : Int) := by
  have hn : n.toNat < 2 ^ 63 := by word
  have h4 : sint.nat n = n.toNat := by word
  simp only [show (W64 3 : w64) = 3#64 from rfl, show (W64 4 : w64) = 4#64 from rfl,
    show (W64 6 : w64) = 6#64 from rfl, show (W64 8 : w64) = 8#64 from rfl, h4]
  have q1 : (n / 4#64).toNat = n.toNat / 4 := by simp [BitVec.toNat_udiv]
  have q2 : (n % 4#64).toNat = n.toNat % 4 := by simp [BitVec.toNat_umod]
  have q3 : (n / 4#64 * 3#64).toNat = n.toNat / 4 * 3 := by
    rw [BitVec.toNat_mul, q1]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  have q4 : (n % 4#64 * 6#64).toNat = n.toNat % 4 * 6 := by
    rw [BitVec.toNat_mul, q2]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  have q5 : ((n % 4#64 * 6#64) / 8#64).toNat = (n.toNat % 4 * 6) / 8 := by
    rw [BitVec.toNat_udiv, q4]; simp
  rw [base64.sdiv_nn _ _ (base64.msb_small _ (by omega)) (by decide),
    base64.srem_nn _ _ (base64.msb_small _ (by omega)) (by decide)]
  rw [base64.sdiv_nn _ _ (base64.msb_small _ (by omega)) (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, q3, q5]
  simp only [BitVec.toNat_ofInt, Nat.reducePow]
  omega

theorem base64.decodedLen.wp_proof : base64.decodedLen.spec (GF := GF) (hG := hG) := by
  intro n p hn0
  by_cases hp : p = W32 (-1)
  · have hd : base64.decLen p (sint.nat n) = sint.nat n / 4 * 3 + sint.nat n % 4 * 6 / 8 := by
      simp only [base64.decLen, hp, ite_true]
    rw [hd, ← base64.decLen_nopad_eq n hn0]
    subst hp
    wp_start
    try wp_auto
    iapply HΦ; itrivial
  · have hd : base64.decLen p (sint.nat n) = sint.nat n / 4 * 3 := by
      simp only [base64.decLen, hp, ite_false]
    rw [hd, ← base64.decLen_pad_eq n hn0]
    wp_start
    try wp_auto
    simp only [hp, decide_false]
    try wp_auto
    iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
