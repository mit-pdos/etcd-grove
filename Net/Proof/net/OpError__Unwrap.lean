/-
The proof of `Net/Spec/net/OpError__Unwrap.lean`: the translated `return e.Err`.
-/
module

public import Net.Spec.net.OpError__Unwrap
public import Net.Proof.net.Errors

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions]
variable [go.BasicIntoValInj]

theorem OpError.Unwrap.wp_proof : OpError.Unwrap.spec (GF := GF) (hG := hG) := by
  intro pe v
  wp_start as #Hpe
  (try wp_method_call)
  ihave #H2 := Hpe
  iStructNamed H2
  wp_auto
  iapply HΦ
  itrivial

end proof

end net
end Perennial
