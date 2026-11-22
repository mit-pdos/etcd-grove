/-
The proof of `clientCodec.ReadResponseBody` (`Net/Spec/net/rpc/clientCodec__ReadResponseBody.lean`):
`readFrame`, then for a non-`nil` body the registered codec's `Decode` (`decOk`).
-/
module

public import Net.Spec.net.rpc.clientCodec__ReadResponseBody
public import Net.Spec.net.rpc.getCodec

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]

theorem clientCodec.ReadResponseBody.wp_proof (wp_readFrame : readFrame.spec (GF := GF) (hG := hG))
    (wp_getCodec : getCodec.spec (GF := GF) (hG := hG)) :
    clientCodec.ReadResponseBody.spec (GF := GF) (hG := hG) := by
  intro c t cn s a la ra body C Θ P eof ueof ed ef
  wp_start as ⟨#Hrwc, #Hc, #Hio, #Heof, #Hueof, #Hed, #Hef, #HefV, Hdec, HP, #Hacc⟩
  wp_auto
  wp_apply wp_readFrame t cn s a la ra P eof ueof ed ef
      $$ [$Hc $Hio $Heof $Hueof $Hed $Hef $HefV $HP $Hacc]
    as %p %err ⟨%got, HP, Hres⟩
  icases Hres with (⟨%pl, ⟨%Hnil, %Hgot, %Hpl⟩, Hp, Hpcap⟩ | ⟨%Hne, #HE⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl Hne
    | ok e =>
      wp_auto
      iapply HΦ
      iexists got
      iframe HP
      iright
      iframe Hdec
      isplitr
      · ipureintro; exact Hne
      iexact HE
  subst Hnil
  wp_auto
  cases body with
  | nil =>
    wp_auto
    iapply HΦ
    iexists got
    iframe HP
    ileft
    iexists pl
    isplitr
    · ipureintro; exact ⟨Hgot, Hpl⟩
    unfold bodyRes
    ipureintro; rfl
  | ok b =>
    unfold bodyDec
    icases Hdec with ⟨#Hset, Hd⟩
    wp_auto
    wp_apply wp_getCodec C $$ Hset as %cd #Hcd
    unfold codecIs
    icases Hcd with ⟨%v, #Hv, #Henc, #Hdecok⟩
    iStructNamed Hv
    wp_auto
    unfold decOk
    wp_bind (App (App (Val #v.Decode') _) _)
    iapply Hdecok $$ Hp [Hd]
    · iapply Hd
    inext
    iintro %err %ok Hp %Hiff HΘ Herr
    wp_auto
    iapply HΦ
    iexists got
    iframe HP
    ileft
    iexists pl
    isplitr
    · ipureintro; exact ⟨Hgot, Hpl⟩
    unfold bodyRes
    iexists ok
    iframe HΘ Herr
    ipureintro; exact Hiff

end proof

end net.rpc
end Perennial
