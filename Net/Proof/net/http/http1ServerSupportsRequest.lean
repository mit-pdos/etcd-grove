/-
The proof of `http1ServerSupportsRequest` (`Net/Spec/net/http/http1ServerSupportsRequest.lean`).
-/
module

public import Net.Spec.net.http.http1ServerSupportsRequest

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

set_option hygiene false in
/-- The end: the result `b` settled by the case hypotheses (`hb`), the request's fields put back. -/
local macro "req_fin" v:term : tactic => `(tactic| (
  obtain rfl : b = $v := hb.symm.trans (by simp_all)
  iapply HΦ
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe))

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

theorem http1ServerSupportsRequest.wp_proof : http1ServerSupportsRequest.spec (GF := GF) (hG := hG) := by
  intro req dq r
  generalize hb : (decide (r.ProtoMajor' = W64 1) || decide (r.ProtoMajor' = W64 2 ∧
    r.ProtoMinor' = W64 0 ∧ r.Method' = go!"PRI" ∧ r.RequestURI' = go!"*")) = b
  wp_start as Hr
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hr
  iStructNamed Hr
  wp_auto
  by_cases h1 : r.ProtoMajor' = W64 1
  · simp only [decide_eq_true h1]
    wp_auto
    req_fin true
  simp only [decide_eq_false h1]
  wp_auto
  by_cases h2 : r.ProtoMajor' = W64 2
  · simp only [decide_eq_true h2]
    wp_auto
    by_cases h3 : r.ProtoMinor' = W64 0
    · simp only [decide_eq_true h3]
      wp_auto
      by_cases h4 : r.Method' = go!"PRI"
      · simp only [decide_eq_true h4]
        wp_auto
        by_cases h5 : r.RequestURI' = go!"*"
        · simp only [decide_eq_true h5]
          wp_auto
          req_fin true
        · simp only [decide_eq_false h5]
          wp_auto
          req_fin false
      · simp only [decide_eq_false h4]
        wp_auto
        req_fin false
    · simp only [decide_eq_false h3]
      wp_auto
      req_fin false
  · simp only [decide_eq_false h2]
    wp_auto
    req_fin false

end proof

end net.http
end Perennial
