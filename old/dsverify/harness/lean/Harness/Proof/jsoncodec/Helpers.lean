/-
Specs of some of `harness/jsoncodec`'s helpers (the JSON syntax a kit's generated codec and the
lab's json model share): `IsSpace` (`spaceB`), `AppendRaw` and
`AppendBool`. Functional specs, so they imply safety (no panic).
-/
module

public import Harness.Proof.jsoncodec.Base

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace dsverify_lab.harness.jsoncodec

/-- JSON whitespace. -/
def spaceB (c : w8) : Bool := [W8 32, W8 9, W8 10, W8 13].contains c

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : dsverify_lab.harness.jsoncodec.Assumptions]

set_option goose.wp.extras true

theorem wp_IsSpace (c : w8) :
    {{ (True : IProp GF) }}
      (App (Val (@! dsverify_lab.harness.jsoncodec.IsSpace)) (Val #c))
    {{ RET #(spaceB c); True }} := by
  wp_start
  wp_auto
  by_cases h1 : c = W8 32
  · have hb : spaceB c = true := by rw [h1]; rfl
    rw [hb]; simp only [h1, _root_.decide_true]
    wp_auto
    iapply HΦ; itrivial
  simp only [h1, _root_.decide_false]
  wp_auto
  by_cases h2 : c = W8 9
  · have hb : spaceB c = true := by rw [h2]; rfl
    rw [hb]; simp only [h2, _root_.decide_true]
    wp_auto
    iapply HΦ; itrivial
  simp only [h2, _root_.decide_false]
  wp_auto
  by_cases h3 : c = W8 10
  · have hb : spaceB c = true := by rw [h3]; rfl
    rw [hb]; simp only [h3, _root_.decide_true]
    wp_auto
    iapply HΦ; itrivial
  simp only [h3, _root_.decide_false]
  wp_auto
  have h1' : ¬ c = 32#8 := h1
  have h2' : ¬ c = 9#8 := h2
  have h3' : ¬ c = 10#8 := h3
  have hb : spaceB c = decide (c = W8 13) := by
    simp [spaceB, h1', h2', h3']
  rw [hb]
  iapply HΦ; itrivial

/-- `AppendRaw(b, s)`: `b` with `s`'s bytes after it. -/
theorem wp_AppendRaw (b : GoSlice) (bs : List w8) (str : GoString) :
    {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
      (App (App (Val (@! dsverify_lab.harness.jsoncodec.AppendRaw)) (Val #b)) (Val #str))
    {{ (b' : GoSlice), RET #b'; b' ↦* (bs ++ str) ∗ ownSliceCap w8 b' (DFrac.own 1) }} := by
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb', Hcap', -⟩
  iapply HΦ
  iframe

/-- `AppendBool(b, x)`: `b` with `true` or `false` after it. -/
theorem wp_AppendBool (b : GoSlice) (bs : List w8) (x : Bool) :
    {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
      (App (App (Val (@! dsverify_lab.harness.jsoncodec.AppendBool)) (Val #b)) (Val #x))
    {{ (b' : GoSlice), RET #b';
        b' ↦* (bs ++ (if x then (go!"true" : List w8) else go!"false")) ∗
        ownSliceCap w8 b' (DFrac.own 1) }} := by
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  cases x
  · wp_auto
    wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb', Hcap', -⟩
    iapply HΦ
    iframe
  · wp_auto
    wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb', Hcap', -⟩
    iapply HΦ
    iframe

end spec

end dsverify_lab.harness.jsoncodec

end Perennial
