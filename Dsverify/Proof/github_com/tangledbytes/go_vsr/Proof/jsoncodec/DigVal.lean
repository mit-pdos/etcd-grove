/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/jsoncodec/DigVal.lean (lab master 915f964;
notes/dsv-vr.md).
-/
/-
The decimal value of a list of digits (`jsoncodec.Digits`), and of `decN n`.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.jsoncodec.ScanLemmas

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VsrJson

open Perennial

/-- The value of decimal digits. -/
def valD (ds : List w8) : Nat := ds.foldl (fun a c => a * 10 + (c.toNat - 48)) 0

theorem valD_foldl (ds : List w8) (a : Nat) :
    ds.foldl (fun a c => a * 10 + (c.toNat - 48)) a = a * 10 ^ ds.length + valD ds := by
  induction ds generalizing a with
  | nil => simp [valD]
  | cons c ds ih =>
    simp only [List.foldl_cons, valD] at *
    rw [ih, ih (0 * 10 + (c.toNat - 48))]
    simp only [Nat.pow_succ, List.length_cons, Nat.zero_mul, Nat.zero_add, Nat.add_mul,
      Nat.mul_assoc, Nat.mul_comm 10 (10 ^ _), Nat.add_assoc]

theorem valD_append (a b : List w8) : valD (a ++ b) = valD a * 10 ^ b.length + valD b := by
  unfold valD; rw [List.foldl_append]; exact valD_foldl b _

theorem valD_single (c : w8) : valD [c] = c.toNat - 48 := by simp [valD]

theorem valD_decN (n : Nat) : valD (decN n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [decN_eq]
    split
    · rw [valD_single]; simp; omega
    · rw [valD_append, ih (n / 10) (by omega), valD_single]; simp; omega

theorem valD_le_append (a b : List w8) : valD a ≤ valD (a ++ b) := by
  rw [valD_append]
  have : 1 ≤ 10 ^ b.length := Nat.one_le_pow _ _ (by omega)
  have := Nat.mul_le_mul_left (valD a) this
  omega

end VsrJson
