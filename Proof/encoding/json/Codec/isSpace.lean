/-
The proof of `isSpace` (`Spec/encoding/json/Codec/isSpace.lean`): the four comparisons (as
`jsoncodec.IsSpace`'s proof).
-/
module

public import Spec.encoding.json.Codec.isSpace

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace encoding.json

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.json.Assumptions]

theorem isSpace.wp_proof : isSpace.spec (GF := GF) (hG := hG) := by
  intro c
  wp_start
  wp_auto
  by_cases h1 : c = W8 32
  · have hb : isSpaceB c = true := by rw [h1]; rfl
    rw [hb]; simp only [h1, _root_.decide_true]
    wp_auto
    iapply HΦ; itrivial
  simp only [h1, _root_.decide_false]
  wp_auto
  by_cases h2 : c = W8 9
  · have hb : isSpaceB c = true := by rw [h2]; rfl
    rw [hb]; simp only [h2, _root_.decide_true]
    wp_auto
    iapply HΦ; itrivial
  simp only [h2, _root_.decide_false]
  wp_auto
  by_cases h3 : c = W8 10
  · have hb : isSpaceB c = true := by rw [h3]; rfl
    rw [hb]; simp only [h3, _root_.decide_true]
    wp_auto
    iapply HΦ; itrivial
  simp only [h3, _root_.decide_false]
  wp_auto
  have h1' : ¬ c = 32#8 := h1
  have h2' : ¬ c = 9#8 := h2
  have h3' : ¬ c = 10#8 := h3
  have hb : isSpaceB c = decide (c = W8 13) := by
    simp [isSpaceB, h1', h2', h3']
  rw [hb]
  iapply HΦ; itrivial

end proof

end encoding.json
end Perennial
