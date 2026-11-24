/-
The proof of `http.Header.Del` (`Net/Spec/net/http/Header__Del.lean`): `textproto.MIMEHeader(h).Del(key)`.
-/
module

public import Net.Spec.net.http.Header__Del
public import Net.Spec.net.textproto.MIMEHeader__Del

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

theorem Header.Del.wp_proof
    (wp_Del : net.textproto.MIMEHeader.Del.spec (GF := GF) (hG := hG)) :
    Header.Del.spec (GF := GF) (hG := hG) := by
  intro h m key
  wp_start as ⟨%Hk, Hm⟩
  wp_auto
  wp_apply wp_Del h m key $$ [Hm] as Hm
  · iframe; ipureintro; exact Hk
  iapply HΦ
  iexact Hm

end proof

end net.http
end Perennial
