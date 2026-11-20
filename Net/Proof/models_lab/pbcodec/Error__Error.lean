/-
The proof of `Net/Spec/models_lab/pbcodec/Error__Error.lean`: the translated
`return "proto: " + e.Msg`.
-/
module

public import Net.Spec.models_lab.pbcodec.Error__Error

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace models_lab.pbcodec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.pbcodec.Assumptions]

theorem Error.Error.wp_proof : Error.Error.spec (GF := GF) (hG := hG) := by
  intro e v
  wp_start as #He
  (try wp_method_call)
  iStructNamed He
  wp_auto
  iapply HΦ
  itrivial

end proof

end models_lab.pbcodec
end Perennial
