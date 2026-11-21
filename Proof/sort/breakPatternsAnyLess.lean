/-
The proof of `sort.breakPatterns` for any `Less` (`Spec/sort/breakPatternsAnyLess.lean`): Perennial's proof (`Perennial/Proof/sort/breakPatterns.lean`), without the segment (`Less` is not called; its callees are Perennial's `nextPowerOfTwo` and `xorshift.Next`).
-/
module

public import Spec.sort.breakPatternsAnyLess
public import Proof.sort.AnyLessBasics

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open sortAny

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.sort.Assumptions]

open slices in
theorem sort.breakPatterns.wp_proofAnyLess
    (wp_nextPowerOfTwo : _root_.Perennial.sort.nextPowerOfTwo.spec (GF := GF) (hG := hG))
    (wp_xorshift_Next : _root_.Perennial.sort.xorshift.Next.spec (GF := GF) (hG := hG)) :
    EtcdGrove.sort.breakPatterns.anyLessSpec (GF := GF) (hG := hG) := fun E x R l a b => by
  wp_start as ⟨#Hs, Hl, %Hab_bound⟩
  wp_auto
  wp_if_destruct
  · wp_apply wp_nextPowerOfTwo _ (by word) with %m %Hm
    have hL : sint.Z (b - a) = sint.Z b - sint.Z a := by word
    have hd : sint.Z (BitVec.sdiv (b - a) (W64 4)) = (sint.Z b - sint.Z a) / 4 := by
      rw [sint_sdiv4 _ (by omega), hL]
    ihave HI : (∃ (l1 : List E) (idx_val : w64) (rv : _root_.Perennial.sort.xorshift),
        "Hl" ∷ R l1 ∗
        "idx" ∷ idx_ptr ↦ idx_val ∗
        "random" ∷ random_ptr ↦ rv ∗
        "%idx_bound" ∷ ⌜sint.Z a + (sint.Z b - sint.Z a) / 4 * 2 - 1 ≤ sint.Z idx_val ∧
          sint.Z idx_val ≤ sint.Z a + (sint.Z b - sint.Z a) / 4 * 2 + 2⌝ ∗
        "%HPerm1" ∷ ⌜l.Perm l1⌝ : IProp GF) $$ [Hl idx random]
    · iexists l, _, _
      iframe
      ipureintro
      exact ⟨by word, List.Perm.refl _⟩
    wp_for HI
    wp_if_destruct
    · wp_apply wp_xorshift_Next $$ random with %rv' %n random
      have hand : uint.Z (n &&& (m - W64 1)) ≤ uint.Z (m - W64 1) := by
        have := Nat.and_le_right (n := n.toNat) (m := (m - W64 1).toNat)
        simp only [uint.Z, BitVec.toNat_and]; omega
      have hm1 : uint.Z (m - W64 1) = uint.Z m - 1 := by word
      have ho : sint.Z (n &&& (m - W64 1)) = uint.Z (n &&& (m - W64 1)) := by
        have h63 : uint.Z (n &&& (m - W64 1)) < 2 ^ 63 := by omega
        exact BitVec.toInt_eq_toNat_of_lt (by unfold uint.Z at h63; omega)
      have Hlen := HPerm1.length_eq
      wp_join iprop(∃ o : w64, "other" ∷ other_ptr ↦ o ∗ "length" ∷ length_ptr ↦ (b - a) ∗
          "%Ho" ∷ ⌜0 ≤ sint.Z o ∧ sint.Z o < sint.Z b - sint.Z a⌝) with [other length]
          as ⟨%o, other, length, %Ho⟩
      · (try wp_auto); iexists _; iframe; ipureintro; constructor <;> word
      · (try wp_auto); iexists _; iframe; ipureintro; constructor <;> word
      have hj : sint.Z a ≤ sint.Z (a + o) ∧ sint.Z (a + o) < sint.Z b := by
        constructor <;> word
      generalize hjdef : (a + o) = j at *
      have hi : sint.Z a ≤ sint.Z idx_val ∧ sint.Z idx_val < sint.Z b := by
        have := hd; constructor <;> word
      list_elem l1 (sint.nat j) as xo
      list_elem l1 (sint.nat idx_val) as xi
      wp_apply wp_any_Swap x R l1 idx_val j xi xo (by word) (by word)
        Hxi_lookup Hxo_lookup $$ [$Hs $Hl] as %l2 ⟨Hl, %Hp⟩
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro
      exact ⟨by have := hd; word, HPerm1.trans Hp⟩
    · iapply HΦ
      iframe
      ipureintro
      exact HPerm1
  · iapply HΦ
    iframe
    ipureintro
    exact List.Perm.refl _

end proof

end EtcdGrove
end Perennial
