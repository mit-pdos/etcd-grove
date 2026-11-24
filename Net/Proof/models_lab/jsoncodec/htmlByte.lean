/-
The proof of `jsoncodec.htmlByte` (`Net/Spec/models_lab/jsoncodec/htmlByte.lean`).
-/
module

public import Net.Spec.models_lab.jsoncodec.htmlByte


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

theorem htmlByte.wp_proof : htmlByte.spec (GF := GF) (hG := hG) := by
  intro c
  wp_start
  wp_auto
  repeat' (first | wp_if_destruct | wp_auto)
  all_goals
    iapply (val_leaf Φ _ _ ?_) $$ HΦ
    unfold htmlB; simp_all (decide := true)

end proof

end models_lab.jsoncodec
end Perennial
