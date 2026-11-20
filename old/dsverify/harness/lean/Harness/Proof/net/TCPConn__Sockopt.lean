/-
The proofs of `Spec/net/TCPConn__Sockopt.lean`: the (promoted) method, then the model's
`setSockopt` (`net.wp_setSockopt`, below).
-/
module

public import Harness.Spec.net.TCPConn__Sockopt

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

/-- The model's `setSockopt src addr`: `nil`, or an `*OpError` of `"set"` (the closed-end error or
another failure). -/
theorem net.wp_setSockopt (src addr : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.net }}
      (App (App (Val net.model.setSockopt) (Val #src)) (Val #addr))
    {{ (err : GoInterface), RET #err; ∃ code : w64,
        ⌜err = interface.nil ↔ code = errNone⌝ ∗ net.connErr go!"set" code err }} := by
  wp_start
  wp_apply net.wp_arbitraryBool as %b -
  wp_if_destruct
  · wp_apply net.wp_arbitraryBool as %b2 -
    wp_if_destruct
    · wp_apply net.wp_codeErr as %inner Hinner
      wp_apply net.wp_opError as %e ⟨#HOp, #HErr⟩
      iapply HΦ
      iexists NetConn.errFail
      unfold net.connErr net.opErr
      rw [ite_cond_eq_false _ _ (by decide), ite_cond_eq_false _ _ (by decide)]
      isplitr
      · ipureintro; simp [interface.mkOk]
      · iexists e, inner
        rw [ite_cond_eq_false _ _ (by decide)]
        iframe HOp HErr
        ipureintro; rfl
    · wp_apply net.wp_codeErr as %inner Hinner
      wp_apply net.wp_opError as %e ⟨#HOp, #HErr⟩
      iapply HΦ
      iexists NetConn.errClosed
      unfold net.connErr net.opErr
      rw [ite_cond_eq_false _ _ (by decide), ite_cond_eq_false _ _ (by decide)]
      isplitr
      · ipureintro; simp [interface.mkOk]
      · iexists e, inner
        rw [ite_cond_eq_true _ _ (by decide)]
        iframe HOp HErr Hinner
        ipureintro; rfl
  · iapply HΦ
    iexists errNone
    unfold net.connErr
    simp only [↓reduceIte]
    ipureintro; simp

theorem net.TCPConn.SetReadBuffer.wp_proof :
    net.TCPConn.SetReadBuffer.spec (GF := GF) (hG := hG) := by
  intro c cid side n
  unfold net.ownTCPConn net.connAddrs
  wp_start as ⟨%fd, #Hfd, #HFD, #Hc, %la, %ra, #Hla, #Hra, %Hok⟩
  rw [method_unfold]
  wp_auto
  wp_apply net.wp_fdOf $$ Hfd
  rw [net.netFD_ty_eq, net.Addr_ty_eq]
  wp_auto
  wp_apply net.wp_setSockopt as %err Herr
  iapply HΦ $$ Herr

theorem net.TCPConn.SetWriteBuffer.wp_proof :
    net.TCPConn.SetWriteBuffer.spec (GF := GF) (hG := hG) := by
  intro c cid side n
  unfold net.ownTCPConn net.connAddrs
  wp_start as ⟨%fd, #Hfd, #HFD, #Hc, %la, %ra, #Hla, #Hra, %Hok⟩
  rw [method_unfold]
  wp_auto
  wp_apply net.wp_fdOf $$ Hfd
  rw [net.netFD_ty_eq, net.Addr_ty_eq]
  wp_auto
  wp_apply net.wp_setSockopt as %err Herr
  iapply HΦ $$ Herr

theorem net.TCPConn.SetKeepAlive.wp_proof :
    net.TCPConn.SetKeepAlive.spec (GF := GF) (hG := hG) := by
  intro c cid side b
  unfold net.ownTCPConn net.connAddrs
  wp_start as ⟨%fd, #Hfd, #HFD, #Hc, %la, %ra, #Hla, #Hra, %Hok⟩
  rw [net.TCPConn_ty_eq]
  wp_auto
  wp_apply net.wp_fdOf $$ Hfd
  rw [net.netFD_ty_eq, net.Addr_ty_eq]
  wp_auto
  wp_apply net.wp_setSockopt as %err Herr
  iapply HΦ $$ Herr

theorem net.TCPConn.SetKeepAlivePeriod.wp_proof :
    net.TCPConn.SetKeepAlivePeriod.spec (GF := GF) (hG := hG) := by
  intro c cid side d
  unfold net.ownTCPConn net.connAddrs
  wp_start as ⟨%fd, #Hfd, #HFD, #Hc, %la, %ra, #Hla, #Hra, %Hok⟩
  rw [net.TCPConn_ty_eq]
  wp_auto
  wp_apply net.wp_fdOf $$ Hfd
  rw [net.netFD_ty_eq, net.Addr_ty_eq]
  wp_auto
  wp_apply net.wp_setSockopt as %err Herr
  iapply HΦ $$ Herr

end proof

end Perennial
