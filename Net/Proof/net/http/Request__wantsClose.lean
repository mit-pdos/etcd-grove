/-
The proof of `Request.wantsClose` (`Net/Spec/net/http/Request__wantsClose.lean`).
-/
module

public import Net.Spec.net.http.Request__wantsClose
public import Net.Spec.net.http.Header__get
public import Net.Spec.net.http.hasToken

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

set_option hygiene false in
/-- The request's fields put back into `Hr`. -/
local macro "req_combine" : tactic => `(tactic| (
  ihave Hr := typedPointsto_combine req r dq Hnn $$ [Method URL Proto ProtoMajor ProtoMinor Header Body GetBody ContentLength TransferEncoding Close Host Form PostForm MultipartForm Trailer RemoteAddr RequestURI TLS Cancel Response Pattern ctx pat matches' otherValues]
  · simp only [TypedPointsto.typedPointstoDef]; iframe))

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

theorem Request.wantsClose.wp_proof
    (wp_get : Header.get.spec (GF := GF) (hG := hG))
    (wp_hasToken : hasToken.spec (GF := GF) (hG := hG)) :
    Request.wantsClose.spec (GF := GF) (hG := hG) := by
  intro req dq dqm r ms
  wp_start as ⟨Hr, Hm, %Hc⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hr
  iStructNamed Hr
  wp_auto
  req_combine
  cases hC : r.Close'
  · wp_auto
    iStructNamed Hr
    rw [method_unfold (t := go.GoType.PointerType net.http.Header.ty) (m := go!"get")]
    wp_auto
    wp_apply wp_get r.Header' dqm ms go!"Connection" $$ [Hm] as %v ⟨Hm, -, %Hv⟩
    · iframe; simp only [hdrVals, Hc]; ipureintro; trivial
    rw [Hv Hc]
    wp_apply wp_hasToken go!"" go!"close"
    · ipureintro; decide
    req_combine
    iapply HΦ
    iframe
  · wp_auto
    iapply HΦ
    iframe

end proof

end net.http
end Perennial
