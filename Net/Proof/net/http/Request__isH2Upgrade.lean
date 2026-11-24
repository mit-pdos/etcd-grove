/-
The proof of `Request.isH2Upgrade` (`Net/Spec/net/http/Request__isH2Upgrade.lean`).
-/
module

public import Net.Spec.net.http.Request__isH2Upgrade

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

set_option hygiene false in
/-- The end: the result `b` settled by the case hypotheses (`hb`), the request's and the URL's
fields put back. -/
local macro "h2_fin" v:term : tactic => `(tactic| (
  obtain rfl : b = $v := hb.symm.trans (by simp_all)
  iapply HΦ
  iframe Hm
  isplitl [Method URL Proto ProtoMajor ProtoMinor Header Body GetBody ContentLength TransferEncoding
    Close Host Form PostForm MultipartForm Trailer RemoteAddr RequestURI TLS Cancel Response Pattern
    ctx pat matches' otherValues]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  · iapply typedPointsto_combine _ _ _ Hnnu
    simp only [TypedPointsto.typedPointstoDef]
    iframe))

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

theorem Request.isH2Upgrade.wp_proof : Request.isH2Upgrade.spec (GF := GF) (hG := hG) := by
  intro req dq dqm dqu r ms u
  generalize hb : (decide (r.Method' = go!"PRI") && decide (GMap.size ms = 0) &&
    decide (u.Path' = go!"*") && decide (r.Proto' = go!"HTTP/2.0")) = b
  wp_start as ⟨Hr, Hm, Hu⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hr
  ihave %Hnnu := typedPointsto_not_null _ _ _ $$ Hu
  iStructNamed Hr
  iStructNamedPrefix Hu "u_"
  wp_auto
  by_cases h1 : r.Method' = go!"PRI"
  · simp only [decide_eq_true h1]
    wp_auto
    wp_apply wp_map_len_lt $$ Hm as ⟨Hm, %Hsz⟩
    by_cases h2 : GMap.size ms = 0
    · simp only [h2]
      wp_auto
      by_cases h3 : u.Path' = go!"*"
      · simp only [decide_eq_true h3]
        wp_auto
        by_cases h4 : r.Proto' = go!"HTTP/2.0"
        · simp only [decide_eq_true h4]
          try wp_auto
          h2_fin true
        · simp only [decide_eq_false h4]
          try wp_auto
          h2_fin false
      · simp only [decide_eq_false h3]
        try wp_auto
        h2_fin false
    · have h2' : decide (W64 (GMap.size ms) = W64 0) = false := by
        apply decide_eq_false; intro h; apply h2
        have := congrArg BitVec.toNat h
        simp at this; omega
      simp only [h2']
      try wp_auto
      h2_fin false
  · simp only [decide_eq_false h1]
    try wp_auto
    h2_fin false

end proof

end net.http
end Perennial
