/-
The proof of `textproto.MIMEHeader.Set` (`Net/Spec/net/textproto/MIMEHeader__Set.lean`): the slice
literal `[]string{value}`, then the canonical key (unchanged, `CanonicalMIMEHeaderKey.spec`) set to it.
-/
module

public import Net.Spec.net.textproto.MIMEHeader__Set
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

theorem MIMEHeader.Set.wp_proof
    (wp_Canon : CanonicalMIMEHeaderKey.spec (GF := GF) (hG := hG)) :
    MIMEHeader.Set.spec (GF := GF) (hG := hG) := by
  intro h ms key value
  wp_start as ⟨%Hk, Hm⟩
  wp_auto
  wp_apply wp_slice_literal (V := GoString) [value]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  wp_apply wp_Canon key
  · ipureintro; exact Hk
  wp_apply wp_mapInsert $$ Hm as Hm
  iapply HΦ
  iframe

end proof

end net.textproto
end Perennial
