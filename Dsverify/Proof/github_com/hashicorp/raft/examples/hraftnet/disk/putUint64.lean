/-
(hraft_robust R3) The proof of `disk.putUint64` (as `etcd/wal`'s `putU64`, the same loop).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.putUint64

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.disk

theorem github_com.hashicorp.raft.examples.hraftnet.disk.putUint64.wp_proof :
    github_com.hashicorp.raft.examples.hraftnet.disk.putUint64.spec (GF := GF) (hG := hG) := by
  intro b bs x
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  ihave HI : (∃ (i : w64) (bb : GoSlice),
      "i" ∷ i_ptr ↦ i ∗ "b" ∷ b_ptr ↦ bb ∗ "Hb" ∷ bb ↦* (bs ++ (encU64 x).take (uint.nat i)) ∗
      "Hcap" ∷ ownSliceCap w8 bb (DFrac.own 1) ∗
      "%Hi" ∷ ⌜uint.nat i ≤ 8⌝ : IProp GF) $$ [i b Hb Hcap]
  · iexists W64 0, b
    simp only [show uint.nat (W64 0) = 0 from rfl, List.take_zero, List.append_nil]
    iframe
    ipureintro; word
  wp_for HI
  by_cases hi8 : uint.Z i < uint.Z (W64 8)
  · rw [if_pos (by simp only [decide_eq_true_eq]; exact hi8)]
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %ysl ⟨Hysl, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hysl] as %bb' ⟨Hb, Hcap, -⟩
    wp_for_post
    iframe
    iexists i + W64 1, bb'
    have hi1 : uint.nat (i + W64 1) = uint.nat i + 1 := by word
    rw [hi1, encU64_take_succ x (uint.nat i) (by word), ← List.append_assoc,
      show W64 (8 * ((uint.nat i : Nat) : Int)) = W64 8 * i by word]
    iframe
    ipureintro; word
  · rw [if_neg (by simp only [decide_eq_true_eq]; exact hi8),
      if_neg (by simp only [decide_eq_true_eq]; exact hi8)]
    have h8 : uint.nat i = 8 := by word
    rw [h8, ← encU64_length x, List.take_length]
    wp_auto
    iapply HΦ
    iframe

end proof

end Perennial
