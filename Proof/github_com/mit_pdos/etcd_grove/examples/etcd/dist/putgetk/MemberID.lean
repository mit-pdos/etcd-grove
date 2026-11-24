/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/putgetk/MemberID.lean`: `crypto/sha1.Sum` of
`"http://" + peer + Token` (Perennial's `crypto.sha1.Sum.spec`: the FIPS 180-4 digest `crypto.sha1.sha1`), then
the loop `id = id<<8 | uint64(h[j])` over the digest's first 8 bytes, which is `memberIdOf peer`'s fold.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.MemberID
public import Perennial.Spec.crypto.sha1.Sum

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putgetk_dist

open Iris Iris.BI Iris.ProofMode

/-- The SHA-1 digest is 20 bytes. -/
theorem sha1_length (m : List w8) : (crypto.sha1.sha1 m).length = 20 := by
  unfold crypto.sha1.sha1
  dsimp only
  simp [crypto.sha1.bytes32]

/-- `memberIdOf`'s fold, one byte at a time. -/
def idStep (acc : Nat) (b : w8) : Nat := acc * 256 + b.toNat

theorem memberIdOf_eq (peer : GoString) :
    memberIdOf peer =
      W64 ((((crypto.sha1.sha1 (go!"http://" ++ peer ++ go!"putgetk")).take 8).foldl idStep 0 : Nat) :
        Int) := by
  unfold memberIdOf idStep; rfl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Assumptions]

/-- One step of the loop: `id<<8 | uint64(b)` is the fold's next value. -/
theorem idStep_w64 (acc : Nat) (b : w8) :
    W64 (acc : Int) <<< W64 8 ||| W64 (uint.Z b) = W64 ((idStep acc b : Nat) : Int) := by
  have hb : b.toNat < 256 := b.isLt
  have h8 : (W64 8).toNat = 8 := rfl
  rw [BitVec.shiftLeft_eq', h8]
  simp only [W64, uint.Z, idStep, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq]
  simp only [Nat.reducePow]
  have key : ∀ m : Nat, m % 256 = 0 → m ||| b.toNat = m + b.toNat := by
    intro m hm
    have e : m = (m / 256) <<< 8 := by rw [Nat.shiftLeft_eq]; omega
    rw [e, ← Nat.shiftLeft_add_eq_or_of_lt (show b.toNat < 2 ^ 8 by omega)]
  rw [Nat.mod_eq_of_lt (show b.toNat < 18446744073709551616 by omega), key _ (by omega)]
  omega

/-- A 20-byte array's `n`-th byte, and the array back. -/
theorem arr20_acc (p : Loc) (a : List w8) (n : Nat) (hl : a.length = 20) (hn : n < 20) :
    (p ↦ (array.mk 20 a : GoArray w8 20) : IProp GF) ⊢
      arrayIndexRef w8 (n : Int) p ↦ a[n]'(by omega) ∗
        (arrayIndexRef w8 (n : Int) p ↦ a[n]'(by omega) -∗ p ↦ (array.mk 20 a : GoArray w8 20)) := by
  have h := array_acc (GF := GF) p (n : Int) (DFrac.own 1) 20 (array.mk 20 a) (a[n]'(by omega)) (by omega)
    (by simp)
  iintro H
  icases h $$ H with ⟨Hel, Hb⟩
  iframe Hel
  iintro Hel
  ihave Hb := Hb $$ Hel
  simp only [Int.toNat_natCast, List.set_getElem_self]
  iexact Hb

theorem MemberID.wp_proof
    (wp_Sum : crypto.sha1.Sum.spec (GF := GF) (hG := hG)) :
    MemberID.spec (GF := GF) (hG := hG) := by
  intro peer Hfips
  wp_start
  ihave #Hsha : isPkgInit (PROP := IProp GF) pkg_id.crypto.sha1 $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
  try wp_auto
  wp_apply (wp_Sum sl (DFrac.own 1) _ Hfips) $$ [Hsl] as -
  · iframe
  try wp_auto
  have hD := sha1_length (go!"http://" ++ peer ++ go!"putgetk")
  ihave IH : iprop(∃ (j idv : w64), "j" ∷ j_ptr ↦ j ∗ "id" ∷ id_ptr ↦ idv ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 8 ∧
        idv = W64 ((((crypto.sha1.sha1 (go!"http://" ++ peer ++ go!"putgetk")).take (sint.nat j)).foldl
          idStep 0 : Nat) : Int)⌝) $$ [j id]
  · iexists W64 0, zero_val w64
    iframe
    ipureintro
    exact ⟨by decide, by decide, rfl⟩
  wp_for IH
  obtain ⟨hj0, hj8, hid⟩ := Hj
  generalize hDd : crypto.sha1.sha1 (go!"http://" ++ peer ++ go!"putgetk") = D at hD hid ⊢
  wp_if_destruct
  · have h8 : sint.Z (W64 8) = 8 := rfl
    have hjn : sint.nat j < 20 := by word
    rw [if_pos (show 0 ≤ sint.Z j ∧ sint.Z j < 20 by omega)]
    have hjz : sint.Z j = ((sint.nat j : Nat) : Int) := by word
    rw [hjz]
    icases arr20_acc h_ptr _ (sint.nat j) hD hjn $$ h with ⟨Hel, Hb⟩
    (try wp_auto)
    ihave h := Hb $$ Hel
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    refine ⟨by word, by word, ?_⟩
    rw [hj1, List.take_add_one, List.getElem?_eq_getElem (show sint.nat j < D.length by omega),
      Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil, hid]
    exact idStep_w64 _ _
  · have h8 : sint.Z (W64 8) = 8 := rfl
    have hj : sint.nat j = 8 := by word
    rw [hj, ← hDd, ← memberIdOf_eq] at hid
    subst hid
    (try wp_auto)
    iapply HΦ; itrivial

end proof

end etcd_putgetk_dist
end EtcdGrove
end Perennial

end
