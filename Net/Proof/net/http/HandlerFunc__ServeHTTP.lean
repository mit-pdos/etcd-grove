/-
The proof of `HandlerFunc.ServeHTTP` (`Net/Spec/net/http/HandlerFunc__ServeHTTP.lean`): `f(w, r)`; a
panic of `f`'s unwinds through the method's body unchanged.
-/
module

public import Net.Spec.net.http.HandlerFunc__ServeHTTP

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

theorem HandlerFunc.ServeHTTP.wp_proof : HandlerFunc.ServeHTTP.spec (GF := GF) (hG := hG) := by
  intro f w r Φ
  iintro Hwp
  rw [method_unfold]
  wp_auto
  wp_bind (App (App (Val #f) (Val #w)) (Val #r))
  iapply wp_wand $$ Hwp
  iintro %v ⟨%hv, HΦ⟩
  rcases hv with rfl | hp
  · wp_auto
    iexact HΦ
  · obtain ⟨p, rfl⟩ := val.isPanic_eq_true hp
    wp_auto
    iexact HΦ

end proof

end net.http
end Perennial
