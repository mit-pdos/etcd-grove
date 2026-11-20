/-
The proof of `Spec/net/TCPListener__Close.lean`: the model over `NetConn.wp_CloseListener`.
-/
module

public import Harness.Spec.net.TCPListener__Close

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

theorem net.TCPListener.Close.wp_proof : net.TCPListener.Close.spec (GF := GF) (hG := hG) := by
  intro l lid a
  unfold net.ownListener
  wp_start as ⟨%fd, #Hfd, #HFD, #Hl, -⟩
  ihave #HFD2 := HFD
  unfold net.ownFD
  icases HFD2 with ⟨#Hid, #Hside, %la, %ra, #Hla, #Hra⟩
  rw [net.netFD_ty_eq, net.TCPListener_ty_eq, net.Addr_ty_eq]
  wp_auto
  wp_apply NetConn.wp_CloseListener lid a $$ Hl as %code -
  wp_if_destruct
  · iapply HΦ
    iexists errNone
    unfold net.opResult
    simp only [↓reduceIte]
    ipureintro; trivial
  · wp_apply net.wp_codeErr as %inner Hinner
    wp_apply net.wp_opError as %e ⟨#HOp, #HErr⟩
    iapply HΦ
    iexists code
    unfold net.opResult net.opErr
    simp only [Hif, ↓reduceIte]
    iexists e, inner
    iframe HOp HErr Hinner
    ipureintro; rfl

end proof

end Perennial
