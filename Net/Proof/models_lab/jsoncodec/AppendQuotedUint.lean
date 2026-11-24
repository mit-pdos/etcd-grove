/-
The proof of `jsoncodec.AppendQuotedUint` (`Net/Spec/models_lab/jsoncodec/AppendQuotedUint.lean`).
Ported from dsverify-lab's `wp_AppendQuotedUint` (`GoEnc.lean`, lab master 915f964).
-/
module

public import Net.Spec.models_lab.jsoncodec.AppendQuotedUint
public import Net.Spec.models_lab.jsoncodec.AppendUint
public import Net.Proof.models_lab.jsoncodec.ScanString

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace models_lab.jsoncodec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.jsoncodec.Assumptions]

set_option goose.wp.extras true

theorem AppendQuotedUint.wp_proof (wp_AppendUint : AppendUint.spec (GF := GF) (hG := hG)) :
    AppendQuotedUint.spec (GF := GF) (hG := hG) := by
  intro b bs x
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 34]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b1 ⟨Hb1, Hcap1, -⟩
  wp_apply (wp_AppendUint b1 _ x) $$ [$Hb1 $Hcap1] as %b2 ⟨Hb2, Hcap2⟩
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 34]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb2 $Hcap2 $Hlit] as %b3 ⟨Hb3, Hcap3, -⟩
  iapply HΦ
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
  iframe
end proof

end models_lab.jsoncodec
end Perennial
