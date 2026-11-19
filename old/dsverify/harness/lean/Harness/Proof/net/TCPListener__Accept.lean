/-
The proof of `Spec/net/TCPListener__Accept.lean`: the model over `NetConn.wp_Accept`.
-/
module

public import Harness.Spec.net.TCPListener__Accept

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions]

theorem net.TCPListener.Accept.wp_proof : net.TCPListener.Accept.spec (GF := GF) (hG := hG) := by
  intro l lid a P Q
  unfold net.ownListener
  wp_start as ⟨⟨%fd, #Hfd, #HFD, #Hl, -⟩, #Hpr⟩
  ihave #HFD2 := HFD
  unfold net.ownFD
  icases HFD2 with ⟨#Hid, #Hside, %la, %ra, #Hla, #Hra⟩
  rw [net.netFD_ty_eq, net.TCPListener_ty_eq, net.Addr_ty_eq]
  wp_auto
  wp_apply NetConn.wp_Accept lid a P Q $$ [$Hl $Hpr] as %cid %code Hres
  wp_if_destruct
  · wp_apply net.wp_arbitraryAddr as %ra' %Hra'
    wp_apply net.wp_arbitraryAddr as %la' %Hla'
    wp_apply net.wp_newFD as %fd' ⟨#Hfd', #Hlp, #Hrp⟩
    wp_apply net.wp_newConn as %c #Hc
    icases Hres with ⟨Hres, Hf⟩
    ihave ⟨Hres, #Hcp⟩ := net.connEnd_isConnP $$ Hres
    iapply HΦ
    unfold net.newConnResult
    ileft
    iexists c, cid
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · unfold net.ownTCPConn net.connAddrs
      iexists fd'
      iframe Hc Hfd' Hcp
      iexists la', ra'
      iframe Hlp Hrp
      ipureintro; exact ⟨Hla', Hra'⟩
    · iframe Hres Hf
  · wp_apply net.wp_codeErr as %inner Hinner
    wp_apply net.wp_opError as %e ⟨#HOp, #HErr⟩
    iapply HΦ
    unfold net.newConnResult
    iright
    iexists _
    isplitr
    · ipureintro; exact ⟨by trivial, rfl⟩
    iexists code
    isplitr
    · ipureintro; exact Hif
    unfold net.opErr
    iexists e, inner
    iframe HOp HErr Hinner
    ipureintro; rfl

end proof

end Perennial
