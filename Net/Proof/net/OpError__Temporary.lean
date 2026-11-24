/-
The proof of `Net/Spec/net/OpError__Temporary.lean`: `OpError.Temporary.impl`'s type assertions on
`Err` (`model.errFlag`), else the extension's `AnyBool`.
-/
module

public import Net.Spec.net.OpError__Temporary
public import Net.Proof.net.Errors
public import Net.Proof.net.OpError__Timeout

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

theorem OpError.Temporary.wp_proof : OpError.Temporary.spec (GF := GF) (hG := hG) := by
  intro pe v
  wp_start as #Hpe
  (try wp_method_call)
  (try unfold OpError.Temporary.impl)
  (try wp_auto)
  wp_apply wp_errFlag pe v $$ Hpe as %b %hb
  iapply HΦ
  ipureintro; exact hb

end proof

end net
end Perennial
