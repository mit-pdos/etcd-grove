/-
The proof of `Request.ProtoAtLeast` (`Net/Spec/net/http/Request__ProtoAtLeast.lean`).
-/
module

public import Net.Spec.net.http.Request__ProtoAtLeast

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

set_option hygiene false in
/-- The end: the result's `decide`s settled by the case hypotheses, the request's fields put back. -/
local macro "req_fin" : tactic => `(tactic| (
  simp only [*, decide_true, decide_false, Bool.true_or, Bool.false_or, Bool.true_and, Bool.false_and,
    Bool.and_true, Bool.and_false, Bool.or_true, Bool.or_false, and_true, true_and, and_false,
    false_and, and_self]
  iapply HΦ
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe))

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

theorem Request.ProtoAtLeast.wp_proof : Request.ProtoAtLeast.spec (GF := GF) (hG := hG) := by
  intro req dq r major minor
  wp_start as Hr
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hr
  iStructNamed Hr
  wp_auto
  wp_if_destruct
  · req_fin
  · wp_if_destruct
    · req_fin
    · req_fin

end proof

end net.http
end Perennial
