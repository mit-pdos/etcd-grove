/-
The proof of `log.Println` (`Net/Spec/log/Println.lean`): Perennial's model does nothing.
-/
module

public import Net.Spec.log.Println

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : log.Assumptions]

theorem log.Println.wp_proof : log.Println.spec (GF := GF) (hG := hG) := by
  intro arg xs dq Hxs
  wp_start as Hsl
  wp_end

end proof

end Perennial
