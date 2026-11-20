/-
The proof of `jsoncodec.AppendBool` (`Net/Spec/models_lab/jsoncodec/AppendBool.lean`): one
case per value, the literal's bytes appended.
-/
module

public import Net.Spec.models_lab.jsoncodec.AppendBool

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace models_lab.jsoncodec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.jsoncodec.Assumptions]

set_option goose.wp.extras true

theorem AppendBool.wp_proof : AppendBool.spec (GF := GF) (hG := hG) := by
  intro b bs x
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

end proof

end models_lab.jsoncodec
end Perennial
