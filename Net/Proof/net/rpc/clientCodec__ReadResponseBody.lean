/-
The proof of `clientCodec.ReadResponseBody` (`Net/Spec/net/rpc/clientCodec__ReadResponseBody.lean`):
`readFrame`, then for a non-`nil` body the registered codec's `Decode` (`decOk`).
-/
module

public import Net.Proof.net.rpc.ReadAcc
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
variable [package_sem' : net.rpc.Assumptions]

theorem clientCodec.ReadResponseBody.wp_proof (wp_readFrame : readFrame.spec (GF := GF) (hG := hG))
    (wp_getCodec : getCodec.spec (GF := GF) (hG := hG)) :
    clientCodec.ReadResponseBody.spec (GF := GF) (hG := hG) := by
  intro c t cn s a la ra body C D G Θ P eof ueof ed ef
  wp_start as ⟨#Hrwc, #Hc, #Hio, #Heof, #Hueof, #Hed, #Hef, #HefV, #Hdec, HD, HP, #Hguard, #Hacc⟩
  wp_auto
  ihave #Hacc' := readAcc_true cn s P $$ Hacc
  wp_apply wp_readFrame t cn s a la ra P iprop(True) eof ueof ed ef
      $$ [$Hc $Hio $Heof $Hueof $Hed $Hef $HefV $HP $Hacc']
    as %p %err ⟨%got, HP, Hres⟩
  icases Hres with (⟨%pl, ⟨%Hnil, %Hgot, %Hpl⟩, Hp, Hpcap⟩ | ⟨%Hne, HE⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl Hne
    | ok e =>
      wp_auto
      iapply HΦ
      iexists got
      iframe HP
      iright
      iframe HD
      isplitr
      · ipureintro; exact Hne
      icases HE with (%HE | ⟨#HE, -⟩)
      · ileft; ipureintro; exact HE.1
      · iright; iexact HE
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
    simp only [bodyRes]
    iframe HD
    ipureintro; exact ⟨Hgot, Hpl⟩
  | ok b =>
    unfold bodyDecG
    icases Hdec with ⟨#Hset, #Hd⟩
    subst Hgot
    ihave HPG := Hguard $$ %pl %Hpl HP
    wp_auto
    icases HPG with ⟨HP, HG⟩
    wp_apply wp_getCodec C $$ Hset as %cd #Hcd
    unfold codecIs
    icases Hcd with ⟨%v, #Hv, #Henc, #Hdecok, -⟩
    iStructNamed Hv
    wp_auto
    unfold decOk
    wp_bind (App (App (Val #v.Decode') _) _)
    iapply Hdecok $$ Hp [HD HG]
    · iapply Hd $$ HD HG
    inext
    iintro %err %ok Hp %Hiff HΘ Herr
    wp_auto
    iapply HΦ
    iexists (frameOf pl)
    iframe HP
    ileft
    iexists pl
    isplitr
    · ipureintro; exact ⟨rfl, Hpl⟩
    unfold bodyRes
    iexists ok
    iframe HΘ
    isplitr
    · ipureintro; exact Hiff
    cases ok
    · simp only [Bool.false_eq_true, ite_false]
      iexact Herr
    · simp only [ite_true]
      itrivial

end proof

end net.rpc
end Perennial
