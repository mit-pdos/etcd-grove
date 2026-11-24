/-
The proof of `jsoncodec.appendEscapedASCII` (`Net/Spec/models_lab/jsoncodec/appendEscapedASCII.lean`).
-/
module

public import Net.Spec.models_lab.jsoncodec.appendEscapedASCII


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

theorem appendEscapedASCII.wp_proof : appendEscapedASCII.spec (GF := GF) (hG := hG) := by
  intro b bs c
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  trace_state
  sorry

end proof

end models_lab.jsoncodec
end Perennial
