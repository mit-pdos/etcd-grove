/- Lean-first (no Rocq counterpart). The proof of `entData`: the salt's loop (`tEntSalt`), then the
pattern's (`tEntPat`). -/
module

public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.entData

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

section pure
variable [GooseExts]

/-- The salt's `k`-th byte. -/
def tEntSalt (e : TEnt) (k : Nat) : w8 := W8 (uint.Z (e.salt' >>> W64 (8 * (k : Int))))

/-- The pattern's byte at position `k`. -/
def tEntPat (e : TEnt) (k : Nat) : w8 :=
  W8 (uint.Z ((e.index' + W64 3 * e.term' + W64 (k : Int)) % W64 251))

theorem tEntData_eq (e : TEnt) :
    tEntData e = (List.range (min 8 (uint.nat e.size'))).map (tEntSalt e) ++
      (List.range' 8 (uint.nat e.size' - 8)).map (tEntPat e) := rfl

theorem range_map_succ (f : Nat → w8) (k : Nat) :
    (List.range (k + 1)).map f = (List.range k).map f ++ [f k] := by
  rw [List.range_succ, List.map_append]; rfl

theorem range'_map_succ (f : Nat → w8) (m : Nat) :
    (List.range' 8 (m + 1)).map f = (List.range' 8 m).map f ++ [f (8 + m)] := by
  rw [List.range'_concat, List.map_append]; simp

end pure

set_option hygiene false in
/-- **`entData`'s pattern loop** (from `i := 8`, the salt's bytes in `b`). Unhygienic: it names the
proof's hypotheses. -/
macro "entData_loop2" : tactic => `(tactic| (
  ihave HI : (∃ (k : w64) (bb : GoSlice),
      "i" ∷ i_ptr ↦ k ∗ "b" ∷ b_ptr ↦ bb ∗
      "Hb" ∷ bb ↦* ((List.range (min 8 (uint.nat e.size'))).map (tEntSalt e) ++
        (List.range' 8 (uint.nat k - 8)).map (tEntPat e)) ∗
      "Hcap" ∷ ownSliceCap w8 bb (DFrac.own 1) ∗
      "%Hk" ∷ ⌜8 ≤ uint.nat k ∧ uint.nat k ≤ max 8 (uint.nat e.size')⌝ : IProp GF) $$ [i b Hb Hcap]
  · iexists W64 8, _
    simp only [show uint.nat (W64 8) - 8 = 0 from rfl, List.range'_zero, List.map_nil,
      List.append_nil]
    iframe
    ipureintro; word
  wp_for HI
  by_cases hk : uint.Z k < uint.Z e.size'
  · rw [if_pos (by simp [hk])]
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %ysl ⟨Hysl, -⟩
    wp_apply wp_slice_append $$ [Hb Hcap Hysl] as %bb' ⟨Hb, Hcap, -⟩
    · iframe
    wp_for_post
    iframe
    iexists k + W64 1, bb'
    have hk1 : uint.nat (k + W64 1) - 8 = (uint.nat k - 8) + 1 := by word
    rw [hk1, range'_map_succ, ← List.append_assoc]
    unfold tEntPat
    rw [show W64 (((8 + (uint.nat k - 8) : Nat)) : Int) = k by word]
    iframe
    ipureintro; word
  · first
      | rw [if_neg (by simp [hk]), if_neg (by simp [hk])]
      | rw [if_neg (by simp [hk]), if_pos (by simp [hk])]
    have hk2 : uint.nat k - 8 = uint.nat e.size' - 8 := by word
    rw [hk2, ← tEntData_eq]
    wp_auto
    iapply HΦ
    iframe))

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem entData.wp_proof : entData.spec (GF := GF) (hG := hG) := by
  intro e hsz
  wp_start
  wp_auto
  wp_apply (wp_slice_make3 (V := w8) (W64 0) e.size' (by word)) as %b0 ⟨Hb, Hcap, -⟩
  -- the salt's loop
  ihave HI : (∃ (i : w64) (bb : GoSlice),
      "i" ∷ i_ptr ↦ i ∗ "b" ∷ b_ptr ↦ bb ∗
      "Hb" ∷ bb ↦* (List.range (uint.nat i)).map (tEntSalt e) ∗
      "Hcap" ∷ ownSliceCap w8 bb (DFrac.own 1) ∗
      "%Hi" ∷ ⌜uint.nat i ≤ 8 ∧ uint.nat i ≤ uint.nat e.size'⌝ : IProp GF) $$ [i b Hb Hcap]
  · iexists W64 0, b0
    simp only [show uint.nat (W64 0) = 0 from rfl, List.range_zero, List.map_nil]
    iframe
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · try wp_auto
    by_cases hs : uint.Z i < uint.Z e.size'
    · rw [if_pos (by simp only [decide_eq_true_eq]; exact hs)]
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
      rw [hi1, range_map_succ]
      unfold tEntSalt
      rw [show W64 (8 * ((uint.nat i : Nat) : Int)) = W64 8 * i by word]
      iframe
      ipureintro; word
    · rw [if_neg (by simp only [decide_eq_true_eq]; exact hs),
        if_neg (by simp only [decide_eq_true_eq]; exact hs)]
      have hm : uint.nat i = min 8 (uint.nat e.size') := by word
      rw [hm]
      iclear i
      wp_auto
      entData_loop2
  · have hm : uint.nat i = min 8 (uint.nat e.size') := by word
    rw [hm]
    entData_loop2

end proof

end etcd_wal
end EtcdGrove
end Perennial
