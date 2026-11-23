/-
The proof of `textproto.MIMEHeader.Del` (`Net/Spec/net/textproto/MIMEHeader__Del.lean`): the canonical
key (unchanged, `CanonicalMIMEHeaderKey.spec`) deleted from the map.
-/
module

public import Net.Spec.net.textproto.MIMEHeader__Del
public import Net.Spec.net.textproto.CanonicalMIMEHeaderKey

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.textproto

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.textproto.Assumptions]

theorem MIMEHeader.Del.wp_proof
    (wp_Canon : CanonicalMIMEHeaderKey.spec (GF := GF) (hG := hG)) :
    MIMEHeader.Del.spec (GF := GF) (hG := hG) := by
  intro h m key
  wp_start as ⟨%Hk, Hm⟩
  wp_auto
  wp_apply wp_Canon key
  · ipureintro; exact Hk
  wp_apply wp_mapDelete_underlying (V := GoSlice) h m key $$ Hm as Hm
  iapply HΦ
  iexact Hm

end proof

end net.textproto
end Perennial
