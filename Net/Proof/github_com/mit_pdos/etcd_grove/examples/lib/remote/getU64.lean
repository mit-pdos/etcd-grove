/-
The proof of `getU64` (`Net/Spec/.../lib/remote/getU64.lean`): the loop over `i < 8` ors in
`uint64(b[i]) << (8*i)`, which adds byte `i` to the little-endian decoding (`leToU64_take_succ`:
the bits are disjoint, Perennial's `toNat_or_shl`); the invariant: `x` is the decoding of `b`'s
first `i` bytes.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.getU64
public import Perennial.Proof.encoding.binary.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

theorem combine_append_single (l : List w8) (v : w8) :
    LittleEndian.combine (l ++ [v]) = LittleEndian.combine l + v.toNat * 2 ^ (8 * l.length) := by
  induction l with
  | nil => simp [LittleEndian.combine]
  | cons a l ih =>
    simp only [List.cons_append, LittleEndian.combine, ih, List.length_cons]
    rw [show 8 * (l.length + 1) = 8 * l.length + 8 by omega, Nat.pow_add, Nat.mul_add,
      Nat.add_assoc]
    congr 2
    rw [Nat.mul_comm 256, Nat.mul_assoc]

open encoding.binary in
/-- One more byte of the little-endian decoding: `x | uint64(v) << (8*i)`. -/
theorem leToU64_take_succ (bs : List w8) (i : w64) (v : w8) (hi : uint.nat i < 8)
    (hv : bs[uint.nat i]? = some v) :
    leToU64 (bs.take (uint.nat i + 1)) =
      leToU64 (bs.take (uint.nat i)) ||| (W64 (uint.Z v) <<< (W64 8 * i)) := by
  have hl : (bs.take (uint.nat i)).length = uint.nat i := by
    have : uint.nat i < bs.length := by
      rcases Nat.lt_or_ge (uint.nat i) bs.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hv; cases hv
    simp; omega
  have hc := combine_bound (bs.take (uint.nat i))
  rw [hl] at hc
  have hlt : 2 ^ (8 * uint.nat i) ≤ 2 ^ 56 := Nat.pow_le_pow_right (by decide) (by omega)
  have hv8 := v.isLt
  rw [List.take_add_one, hv, Option.toList_some, leToU64, leToU64Def, leToU64, leToU64Def,
    combine_append_single, hl]
  have hsh : (W64 8 * i).toNat = 8 * uint.nat i := by word
  have hw : (W64 (uint.Z v) : w64) = v.setWidth 64 := by
    simp only [W64, uint.Z, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  apply BitVec.eq_of_toNat_eq
  rw [hw, BitVec.shiftLeft_eq', hsh,
    toNat_or_shl _ v (8 * uint.nat i) (by rw [BitVec.toNat_ofNat]; omega) (by omega)]
  simp only [BitVec.toNat_ofNat]
  have : (v.toNat + 1) * 2 ^ (8 * uint.nat i) ≤ 256 * 2 ^ (8 * uint.nat i) :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem getU64.wp_proof : getU64.spec (GF := GF) (hG := hG) := by
  intro b dq bs rem Hbs
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  wp_auto
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗ "x" ∷ x_ptr ↦ leToU64 (bs.take (uint.nat i)) ∗
      "%Hi" ∷ ⌜uint.nat i ≤ 8⌝ : IProp GF) $$ [i x]
  · iexists W64 0
    iframe
    ipureintro; simp
  wp_for HI
  wp_if_destruct
  · have hi8 : uint.nat i < 8 := by word
    have hbl : (bs ++ rem).length = 8 + rem.length := by simp [Hbs]
    have hs : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z b.len := by word
    rw [ite_eq_left hs]
    have hsn : (sint.Z i).toNat = uint.nat i := by word
    obtain ⟨v, hv⟩ : ∃ v, bs[uint.nat i]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    wp_apply wp_load_slice_index b (sint.Z i) _ dq v (by word) $$ [Hb] as Hb
    · iframe Hb; ipureintro; rw [hsn, List.getElem?_append_left (by omega)]; exact hv
    wp_for_post
    iframe
    iexists i + W64 1
    rw [show uint.nat (i + W64 1) = uint.nat i + 1 by word, leToU64_take_succ bs i v hi8 hv]
    iframe
    ipureintro; word
  · have hi8 : uint.nat i = 8 := by word
    rw [hi8, List.take_of_length_le (by omega)]
    wp_end

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
