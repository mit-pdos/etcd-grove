/-
The proof of `sort.siftDown` for any `Less` (`Spec/sort/siftDownAnyLess.lean`): the loop of Perennial's proof (`Perennial/Proof/sort/siftDown.lean`), without the heap: `root` stays in `[lo, hi]`, and every index it passes is `first` plus a child below `hi`.
-/
module

public import Spec.sort.siftDownAnyLess
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

omit [GooseExts] [GooseSemantics] [GooseInterp] in
/-- `2 * root + 1` does not overflow (in a small context: `word` in the proof's is lost). -/
theorem siftDown_child_arith (root hi : w64) (h0 : 0 ≤ sint.Z root) (h : sint.Z root < sint.Z hi)
    (h2 : sint.Z hi ≤ 2 ^ 62) :
    sint.Z (W64 2 * root + W64 1) = 2 * sint.Z root + 1 := by
  word

theorem sort.siftDown.wp_proofAnyLess :
    EtcdGrove.sort.siftDown.anyLessSpec (GF := GF) (hG := hG) := fun E x R l lo hi first => by
  wp_start as ⟨#Hs, Hl, %Hb⟩
  wp_auto
  ihave HI : (∃ (root_val : w64) (L : List E),
      "root" ∷ root_ptr ↦ root_val ∗
      "Hl" ∷ R L ∗
      "%Hr" ∷ ⌜sint.Z lo ≤ sint.Z root_val ∧ sint.Z root_val ≤ sint.Z hi ∧
        sint.Z root_val < 2 ^ 62 ∧ l.Perm L⌝ : IProp GF)
      $$ [root Hl]
  · iexists lo, l
    iframe
    ipureintro
    exact ⟨by word, by word, by word, List.Perm.refl _⟩
  wp_for HI
  obtain ⟨Hr1, Hr2, Hr3, HP⟩ := Hr
  have HL := HP.length_eq
  wp_if_destruct
  · -- `child ≥ hi`: break
    wp_for_post
    iapply HΦ
    iframe
    ipureintro
    exact HP
  · have hc : sint.Z (W64 2 * root_val + W64 1) = 2 * sint.Z root_val + 1 :=
      siftDown_child_arith root_val (W64 (2 ^ 62)) (by omega) (by word) (by word)
    have hch : 2 * sint.Z root_val + 1 < sint.Z hi := by omega
    wp_join iprop(∃ (c : w64),
        "child" ∷ child_ptr ↦ c ∗
        "Hl" ∷ R L ∗
        "first" ∷ first_ptr ↦ first ∗
        "data" ∷ data_ptr ↦ (GoInterface.ok x : GoInterface) ∗
        "%Hsel" ∷ ⌜sint.Z root_val < sint.Z c ∧ sint.Z c < sint.Z hi⌝)
      with [child Hl first data] as ⟨%c, child, Hl, first, data, %Hsel⟩
    · list_elem L (sint.nat (first + (W64 2 * root_val + W64 1))) as xl
      list_elem L (sint.nat (first + (W64 2 * root_val + W64 1) + W64 1)) as xr
      wp_apply wp_any_Less x R L _ _ xl xr (by word) (by word) Hxl_lookup Hxr_lookup
        $$ [$Hs $Hl] as %r1 Hl
      cases r1
      · (try bool_if)
        wp_auto
        wp_join_done
        iexists _
        iframe
        ipureintro
        constructor <;> word
      · (try bool_if)
        wp_auto
        wp_join_done
        iexists _
        iframe
        ipureintro
        constructor <;> word
    · iexists _
      iframe
      ipureintro
      constructor <;> word
    list_elem L (sint.nat (first + root_val)) as xrt
    list_elem L (sint.nat (first + c)) as xc
    wp_apply wp_any_Less x R L _ _ xrt xc (by word) (by word) Hxrt_lookup Hxc_lookup
      $$ [$Hs $Hl] as %r2 Hl
    cases r2
    · (try bool_if)
      wp_auto
      wp_for_post
      iapply HΦ
      iframe
      ipureintro
      exact HP
    · (try bool_if)
      wp_auto
      wp_apply wp_any_Swap x R L _ _ xrt xc (by word) (by word) Hxrt_lookup Hxc_lookup
        $$ [$Hs $Hl] as %L2 ⟨Hl, %Hp2⟩
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      exact ⟨by word, by word, by word, HP.trans Hp2⟩

end proof

end EtcdGrove
end Perennial
