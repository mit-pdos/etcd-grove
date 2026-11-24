/-
The proof of `hasToken` (`Net/Spec/net/http/hasToken.lean`).
-/
module

public import Net.Spec.net.http.hasToken
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

open github_com.mit_pdos.perennial.goose.model.strings (wp_string_len)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

theorem hasToken.wp_proof : hasToken.spec (GF := GF) (hG := hG) := by
  intro v token
  wp_start as %Hlt
  wp_auto
  wp_apply wp_string_len as %Ht
  wp_apply wp_string_len as %Hv
  rw [decide_eq_true (show sint.Z (W64 v.length) < sint.Z (W64 token.length) by word)]
  wp_auto
  iapply HΦ
  ipureintro; trivial

end proof

end net.http
end Perennial
