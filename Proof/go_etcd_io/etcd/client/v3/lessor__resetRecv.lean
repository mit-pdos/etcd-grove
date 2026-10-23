/-
Proof of `Spec/go_etcd_io/etcd/client/v3/lessor__resetRecv.lean` (item 1, the client lease).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.lessor__resetRecv
public import Spec.go_etcd_io.etcd.client.v3.lessor__sendKeepAliveLoop
public import Spec.go_etcd_io.etcd.client.v3.retryLeaseClient__LeaseKeepAlive
public import Spec.go_etcd_io.etcd.client.v3.withMax

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option maxHeartbeats 0 in
theorem lessor.resetRecv.wp_proof
    (wp_withMax : withMax.spec (GF := GF) (hG := hG))
    (wp_retry : retryLeaseClient.LeaseKeepAlive.spec (GF := GF) (hG := hG))
    (wp_send : lessor.sendKeepAliveLoop.spec (GF := GF) (hG := hG)) :
    lessor.resetRecv.spec (GF := GF) (hG := hG) := by
  intro l addr
  wp_start as ⟨#Hl, #Hstr⟩
  ihave #Hl' := Hl
  iunfold lessorAt at Hl'
  icases Hl' with ⟨%dc, %γd, %sc, %scd, %lg, %d, %γr, #Hdc, #Hdcu, #Hsc, #Hscc, #Hlg, %Hlgnn, #Hd,
    #Hrem, #Hmu, #Honce⟩
  iunfold lessorRemoteAt at Hrem
  icases Hrem with ⟨%rlc, %conn, %sl, #Hremote, #Hrlc, #Hconn, #Hcopts, #Hco⟩
  iunfold callOptsAt at Hco
  icases Hco with ⟨%vs, #Hsl, %Hcap, #Hok, -⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hctxp : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply context.wp_WithCancel_any sc scd $$ [] as %sctx %γs %cancel ⟨#Hcancel, #Hsctx⟩
  · iframe #
  (try wp_auto)
  wp_apply wp_withMax as %ro #Hro
  ihave #Hro := optApplyKeep_ok _ _ $$ Hro
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoInterface)
    [interface.mkOk go_etcd_io.etcd.client.v3.retryOption.ty #ro]
  isplitr
  · ipureintro; rfl
  iintro %sl1 ⟨Hsl1, -⟩
  (try wp_auto)
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave Hocap := ownSliceCap_empty (GF := GF) (V := GoInterface) sl Hcap Hlen.2
  wp_apply wp_slice_append_persistent sl vs _ _ (DFrac.own 1) $$ [$Hsl $Hocap $Hsl1]
    as %copts ⟨#Hco, Hcocap, -⟩
  ihave #Hro1 : streamCallOptOk (GF := GF) (interface.mkOk go_etcd_io.etcd.client.v3.retryOption.ty #ro) $$ []
  · unfold streamCallOptOk
    iright
    iexists ro
    iframe #
    ipureintro; rfl
  ihave #Hs1 := streamCallOptsOk_singleton _ $$ Hro1
  ihave #Hok' := streamCallOptsOk_of vs $$ Hok
  ihave #Hok2 := streamCallOptsOk_app vs [interface.mkOk go_etcd_io.etcd.client.v3.retryOption.ty #ro] $$ [Hok' Hs1]
  · iframe #
  (try wp_auto)
  ihave #Hctxok := ctxOk_of_isContext sctx _ $$ Hsctx
  wp_apply wp_retry rlc conn addr sctx _ copts (vs ++ [interface.mkOk go_etcd_io.etcd.client.v3.retryOption.ty #ro]) $$ [Hcocap] as %st %err Hres
  · iframe #
    iframe
  (try wp_auto)
  icases Hres with (⟨%Herr, %γ, %Dn, %cd', #Hcs, HSt, HRt⟩ | ⟨%Hst, #Herr⟩)
  · subst Herr
    (try wp_auto)
    wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
    iunfold lessorInv at Hinv
    icases Hinv with ⟨%mref, %mm, %stv, %scf, %e, Hkas, Hm, HM, Hstf, Hscf, #Hscok, Herr, Hreg⟩
    (try wp_auto)
    cases stv with
    | nil =>
      (try wp_auto)
      wp_apply wp_fork $$ [HSt]
      · wp_apply wp_send l addr st γ Dn cd' [] $$ [HSt]
        · iframe #; iframe
        itrivial
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm HM Hstf Hscf Herr Hreg]
      · inext; unfold lessorInv; iexists mref, mm, st, cancel, e; iframe; iframe #
        iright; unfold cancelAny; iexists γs; iexact Hcancel
      (try wp_auto)
      iapply HΦ
      ileft
      isplitr
      · ipureintro; rfl
      iexists γ, Dn, cd'
      iframe #
      iframe
    | ok si =>
      (try wp_auto)
      by_cases hsc : scf = func.nil
      · subst hsc
        (try wp_auto)
        wp_apply wp_fork $$ [HSt]
        · wp_apply wp_send l addr st γ Dn cd' [] $$ [HSt]
          · iframe #; iframe
          itrivial
        (try wp_auto)
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm HM Hstf Hscf Herr Hreg]
        · inext; unfold lessorInv; iexists mref, mm, st, cancel, e; iframe; iframe #
          iright; unfold cancelAny; iexists γs; iexact Hcancel
        (try wp_auto)
        iapply HΦ
        ileft
        isplitr
        · ipureintro; rfl
        iexists γ, Dn, cd'
        iframe #
        iframe
      · icases Hscok with (%Hn | #Hcany)
        · exact absurd Hn hsc
        rw [decide_eq_false hsc]
        (try wp_auto)
        iunfold cancelAny at Hcany
        icases Hcany with ⟨%γc0, #Hc0⟩
        iunfold context.cancelSpec at Hc0
        wp_apply Hc0 $$ [] as -
        · itrivial
        (try wp_auto)
        wp_apply wp_fork $$ [HSt]
        · wp_apply wp_send l addr st γ Dn cd' [] $$ [HSt]
          · iframe #; iframe
          itrivial
        (try wp_auto)
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm HM Hstf Hscf Herr Hreg]
        · inext; unfold lessorInv; iexists mref, mm, st, cancel, e; iframe; iframe #
          iright; unfold cancelAny; iexists γs; iexact Hcancel
        (try wp_auto)
        iapply HΦ
        ileft
        isplitr
        · ipureintro; rfl
        iexists γ, Dn, cd'
        iframe #
        iframe
  · ihave #Herr' := Herr
    iunfold cliStreamErr at Herr'
    icases Herr' with ⟨%Hne, -, -⟩
    subst Hst
    cases err with
    | nil => exact absurd rfl Hne.1
    | ok ei =>
      (try wp_auto)
      iunfold context.cancelSpec at Hcancel
      wp_apply Hcancel $$ [] as -
      · itrivial
      (try wp_auto)
      iapply HΦ
      iright
      iframe #
      ipureintro; rfl

end proof

end EtcdGrove
end Perennial
