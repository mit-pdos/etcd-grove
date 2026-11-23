/-
The proof of `badStringError` (`Net/Spec/net/http/badStringError.lean`): `fmt.Errorf` of two strings.
-/
module

public import Net.Spec.net.http.badStringError
public import Perennial.Spec.fmt.Errorf

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

theorem badStringError.wp_proof (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    badStringError.spec (GF := GF) (hG := hG) := by
  intro what val
  wp_start as #Hfmt
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  wp_apply wp_Errorf _ _ _ _ $$ [$Hsl] as %e -
  · iapply fmt.argsOk_of_argsWf
    rw [show sint.nat (W64 (0 + 1)) = 1 from rfl]
    exact fmt.ArgsWf.cons_string _ _ (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil)
  iapply HΦ; itrivial

end proof

end net.http
end Perennial
