/- Lean-first (no Rocq counterpart). The proof of `putU64`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.putU64
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.RefLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem tU64_take_succ (x : w64) (i : Nat) (hi : i < 8) :
    (tU64 x).take (i + 1) = (tU64 x).take i ++ [W8 (uint.Z (x >>> W64 (8 * (i : Int))))] := by
  unfold tU64
  rw [List.take_add_one, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem putU64.wp_proof : putU64.spec (GF := GF) (hG := hG) := by
  intro b bs x
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  ihave HI : (∃ (i : w64) (bb : GoSlice),
      "i" ∷ i_ptr ↦ i ∗ "b" ∷ b_ptr ↦ bb ∗ "Hb" ∷ bb ↦* (bs ++ (tU64 x).take (uint.nat i)) ∗
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
    rw [hi1, tU64_take_succ x (uint.nat i) (by word), ← List.append_assoc,
      show W64 (8 * ((uint.nat i : Nat) : Int)) = W64 8 * i by word]
    iframe
    ipureintro; word
  · rw [if_neg (by simp only [decide_eq_true_eq]; exact hi8),
      if_neg (by simp only [decide_eq_true_eq]; exact hi8)]
    have h8 : uint.nat i = 8 := by word
    have hl : (tU64 x).length = 8 := by simp [tU64]
    rw [h8, ← hl, List.take_length]
    wp_auto
    iapply HΦ
    iframe

end proof

end etcd_wal
end EtcdGrove
end Perennial
