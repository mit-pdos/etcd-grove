/-
The proof of `parseRequestLine` (`Net/Spec/net/http/parseRequestLine.lean`): two `strings.Cut`s at `" "` (`cut_single`).
-/
module

public import Net.Spec.net.http.parseRequestLine
public import Perennial.Spec.strings.Cut

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

theorem parseRequestLine.wp_proof (wp_cut : strings.Cut.spec (GF := GF) (hG := hG)) :
    parseRequestLine.spec (GF := GF) (hG := hG) := by
  intro line
  wp_start
  wp_auto
  wp_apply wp_cut line _ $$ [$Hpkg]
  rw [cut_single]; try rw [show (32#8 : w8) = W8 32 from rfl]
  wp_apply wp_cut _ _ $$ [$Hpkg]
  rw [cut_single]; try rw [show (32#8 : w8) = W8 32 from rfl]
  unfold parseReqLine
  cases h1 : (cutByte line (W8 32)).2.2 <;> cases h2 : (cutByte (cutByte line (W8 32)).2.1 (W8 32)).2.2 <;>
    simp only [h1, h2, Bool.not_false, Bool.not_true, Bool.false_and, Bool.and_false, Bool.and_self,
      Bool.false_eq_true, ↓reduceIte] <;> wp_auto <;> (iapply HΦ; itrivial)

end proof

end net.http
end Perennial
