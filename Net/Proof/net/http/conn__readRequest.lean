/-
The proof of `conn.readRequest` (`Net/Spec/net/http/conn__readRequest.lean`).
-/
module

public import Net.Spec.net.http.conn__readRequest
public import Net.Spec.net.http.conn__hijacked
public import Net.Spec.net.http.connReader__setReadLimit
public import Net.Spec.net.http.connReader__setInfiniteReadLimit
public import Net.Spec.net.http.connReader__hitReadLimit
public import Net.Spec.net.http.connReader__Read
public import Net.Spec.net.http.readRequestLimit
public import Net.Spec.net.http.http1ServerSupportsRequest
public import Net.Spec.net.http.Request__ProtoAtLeast
public import Net.Spec.net.http.Request__isH2Upgrade
public import Net.Spec.net.http.Request__wantsClose
public import Net.Spec.net.http.Request__wantsHttp10KeepAlive
public import Net.Spec.net.http.Server__maxHeaderValueCount
public import Net.Spec.net.Conn__SetReadDeadline
public import Net.Proof.net.http.ConnReaderStream
public import Net.Proof.net.http.ServerConnLemmas
public import Perennial.Spec.time.Now
public import Perennial.Spec.context.WithCancel

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.http

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS] [net.Assumptions] [field_sem : net.FieldAssumptions]
variable [bufio.Assumptions]

theorem conn.readRequest.wp_proof
    (wp_hijacked : conn.hijacked.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_setReadLimit : connReader.setReadLimit.spec (GF := GF) (hG := hG))
    (wp_setInf : connReader.setInfiniteReadLimit.spec (GF := GF) (hG := hG))
    (wp_hit : connReader.hitReadLimit.spec (GF := GF) (hG := hG))
    (wp_crRead : connReader.Read.spec (GF := GF) (hG := hG))
    (wp_rrl : readRequestLimit.spec (GF := GF) (hG := hG))
    (wp_h1 : http1ServerSupportsRequest.spec (GF := GF) (hG := hG))
    (wp_Proto : Request.ProtoAtLeast.spec (GF := GF) (hG := hG))
    (wp_isH2 : Request.isH2Upgrade.spec (GF := GF) (hG := hG))
    (wp_wantsClose : Request.wantsClose.spec (GF := GF) (hG := hG))
    (wp_wantsKA : Request.wantsHttp10KeepAlive.spec (GF := GF) (hG := hG))
    (wp_mhvc : Server.maxHeaderValueCount.spec (GF := GF) (hG := hG))
    (wp_WithCancel : context.WithCancel.spec (GF := GF) (hG := hG))
    (wp_SetRD : net.Conn.SetReadDeadline.spec (GF := GF) (hG := hG))
    (wp_WReset : EtcdGrove.bufio.Writer.Reset.spec (GF := GF) (hG := hG))
    (wp_NewWriterSize : EtcdGrove.bufio.NewWriterSize.specRep (GF := GF) (hG := hG)) :
    conn.readRequest.spec (GF := GF) (hG := hG) := by
  intro c s cr br γ γh t cn a la ra P Q Z path rmt lm v ctx cd hc hp hlen hlm
  wp_start as ⟨#Henv, #Hrenv, #Hctxi, #Hsc, #Hsd, #Hctx, #Hcctx, #Hsrv, #Hr, #Hbufr, #Hrwc, #Hrmt,
    #Htls, #Hmu, Hγh, Hlm, #Hcr, #Hhl, #Hzl, #Hcok, #Hcrwc, #Hca, Hmain, Hfr⟩
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  ihave #Hsd' := Hsd
  iunfold srvDflt at Hsd'
  icases Hsd' with ⟨#HRT, #HWT, #HMHB, #HMHVC⟩
  ihave #Hsc' := Hsc
  iunfold srvConst at Hsc'
  icases Hsc' with ⟨#Htime, #Hsync, #Hatomic, -, -⟩
  wp_apply wp_hijacked c γh false $$ [$Hsync $Hmu $Hγh] as Hγh
  try wp_auto
  wp_apply wp_Now $$ [$Htime] as %t0 -
  try wp_auto
  rw [method_unfold (t := go.GoType.PointerType net.http.Server.ty) (m := go!"initialReadLimitSize")]
  try wp_auto
  rw [method_unfold (t := go.GoType.PointerType net.http.Server.ty) (m := go!"maxHeaderBytes")]
  try wp_auto
  iunfold crMain at Hmain
  icases Hmain with ⟨Hph, %ab, Hcf, Hhb, Hir, Hab, Hrm, Hbuf, Hsend, Hrecv, Hrdl⟩
  wp_apply wp_setReadLimit cr v _ $$ [$Hrm] as Hrm
  try wp_auto
  rw [decide_eq_false hlm]
  try wp_auto
  wp_apply wp_mhvc s (W64 0) DFrac.discard $$ [$HMHVC] as -
  try wp_auto
  rw [show (W64 1048576 + W64 4096 : w64) = W64 srvL from rfl]
  ihave Hmain : crMain cr γ cn P Q c [] (W64 srvL) $$ [Hph Hcf Hhb Hir Hab Hrm Hbuf Hsend Hrecv Hrdl]
  · iunfold crMain; iframe Hph; iexists ab; iframe
  imod crMain_head cr γ cn P Q srvL c $$ Hmain with ⟨%γe, Hhead⟩
  ihave #Henv' := Henv
  iunfold httpEnv at Henv'
  icases Henv' with ⟨#Hbufio, #Hio, -⟩
  ihave #Hstream := crHead_stream wp_crRead cr γ t cn a la ra P Q (net.rpc.connectReq path) Z srvL c γe
    hc (by unfold srvL; decide) $$ [$Hcr $Hrenv $Hio $Hcok $Hcrwc $Hca]
  ihave #Hbound := crHead_bound cr γ γe cn P Q srvL c (by unfold srvL; decide)
  ihave Hb : (EtcdGrove.bufio.ownReader br ⟨go.GoType.PointerType net.http.connReader.ty, #cr⟩
      (crHead cr γ γe cn P Q srvL c) (crHeadErr γe) [] : IProp GF) $$ [Hfr Hhead]
  · iapply EtcdGrove.bufio.freshReader_own
    iframe Hbufio Hhead
    iexact Hfr
  ihave #Hpre : (□ ∀ r', crHead cr γ γe cn P Q srvL c r' -∗ ⌜r' <+: net.rpc.connectReq path⌝ : IProp GF)
      $$ []
  · imodintro
    iintro %r' HS
    iapply crHead_prefix cr γ γe cn P Q (net.rpc.connectReq path) Z srvL c r'
    iframe Hhl Hzl HS
  ihave #Hfin : (□ ∀ (r1 r2 : List w8) (e : GoInterface), crHeadErr γe r1 e -∗
      crHead cr γ γe cn P Q srvL c r2 -∗ ⌜r1 <+: r2 → r2 = r1⌝ : IProp GF) $$ []
  · imodintro
    iintro %r1 %r2 %e #He HS
    iapply crHeadErr_final cr γ γe cn P Q srvL c r1 r2 e
    iframe He HS
  ihave #Hmsg := crHeadErr_msg (GF := GF) γe
  wp_apply wp_rrl br ⟨go.GoType.PointerType net.http.connReader.ty, #cr⟩ (crHead cr γ γe cn P Q srvL c)
      (crHeadErr γe) path (W64 500) hp (by decide) $$ Henv Hstream Hbound Hpre Hfin Hmsg [Hb]
    as %req %err Hres
  · iexact Hb
  icases Hres with (⟨%Hne, #Hre, %rr, Hb⟩ | ⟨%Hnil, Hreq, Hb⟩)
  · -- an error: the read limit not reached (the request is shorter), so `err` itself
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
    icases EtcdGrove.bufio.ownReader_raw br _ _ _ _ $$ Hb with ⟨Hraw, %q, HS⟩
    ihave %Hpq := Hpre $$ HS
    icases crHead_remain cr γ γe cn P Q srvL c _ $$ HS with ⟨Hrm, HS⟩
    try wp_auto
    wp_apply wp_hit cr (DFrac.own 1) _ $$ [$Hrm] as Hrm
    have hlt : (rr ++ q).length < srvL := by
      have := Hpq.length_le
      simp only [net.rpc.connectReq, List.length_append] at this
      unfold srvL; simp at this ⊢; omega
    rw [show decide (sint.Z (W64 (srvL - (rr ++ q).length : Nat)) ≤ 0) = false by
      rw [decide_eq_false_iff_not]
      have : srvL - (rr ++ q).length < 2 ^ 63 := by unfold srvL at hlt ⊢; omega
      have h0 : 0 < srvL - (rr ++ q).length := by omega
      word]
    try wp_auto
    iapply HΦ
    iframe Hγh Hraw
    ileft
    isplitr
    · ipureintro; exact Hne
    iframe Hlm
    iexists γe, (rr ++ q)
    isplitl [Hrm HS]
    · iapply HS; iexact Hrm
    iexact Hre
  subst Hnil
  iunfold connectReqv at Hreq
  icases Hreq with ⟨%u, %m, %cl, %nb, Hrq, Hu, Hm⟩
  generalize hrv : connectReqVal path u m cl nb = rv
  have hPM : rv.ProtoMajor' = W64 1 := by rw [← hrv]; rfl
  have hPm : rv.ProtoMinor' = W64 0 := by rw [← hrv]; rfl
  have hMeth : rv.Method' = go!"CONNECT" := by rw [← hrv]; rfl
  have hHdr : rv.Header' = m := by rw [← hrv]; rfl
  have hURL : rv.URL' = u := by rw [← hrv]; rfl
  have hProto : rv.Proto' = go!"HTTP/1.0" := by rw [← hrv]; rfl
  try wp_auto
  wp_apply wp_h1 req (DFrac.own 1) _ $$ [$Hrq] as Hrq
  simp only [hPM, decide_true, Bool.true_or, Bool.not_true]
  try wp_auto
  icases EtcdGrove.bufio.ownReader_raw br _ _ _ _ $$ Hb with ⟨Hraw, %q, HS⟩
  ihave %Hpq := Hpre $$ HS
  have hq : q = [] := by
    have := Hpq.length_le
    simp only [List.length_append] at this
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst hq
  rw [List.append_nil] at *
  ihave Hmain := crHead_main cr γ γe cn P Q srvL c _ $$ HS
  iunfold crMain at Hmain
  icases Hmain with ⟨Hph, %ab', Hcf, Hhb, Hir, Hab, Hrm, Hbuf, Hsend, Hrecv, Hrdl⟩
  wp_apply wp_setInf cr _ $$ [$Hrm] as Hrm
  try wp_auto
  rw [hHdr]
  wp_apply (wp_map_lookup2 (V := GoSlice) go.string (go.SliceType go.string) m _ go!"Host" _) $$ Hm
    as Hm
  try wp_auto
  wp_apply wp_isH2 req (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) rv ∅ _ $$ [Hrq Hm Hu] as ⟨Hrq, Hm, Hu⟩
  · rw [hHdr, hURL]; iframe Hrq Hm Hu
  rw [hMeth, hProto]
  simp only [show decide ((go!"CONNECT" : List w8) = go!"PRI") = false by decide, Bool.false_and]
  try wp_auto
  wp_apply wp_Proto req (DFrac.own 1) _ (W64 1) (W64 1) $$ [$Hrq] as Hrq
  rw [hPM, hPm]
  have e1 : decide (sint.Z (W64 1) < sint.Z (W64 1)) = false := by decide
  have e2 : decide (sint.Z (W64 1) ≤ sint.Z (W64 0)) = false := by decide
  simp only [e1, e2, decide_true, Bool.false_or, Bool.and_false]
  try wp_auto
  -- the header map is empty: the loop over it runs no iteration
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (K := GoString) (V := GoSlice) (fun _ _ => iprop(True)) $$ Hm
  iintro %keys %Hkeys
  obtain ⟨-, hlen, -⟩ := Hkeys
  have hk : keys = [] := List.eq_nil_of_length_eq_zero (by rw [hlen]; exact GMap.map_size_empty)
  subst hk
  isplitr
  · ipureintro; trivial
  isplitr
  · imodintro
    iintro %i %key %v %h
    obtain ⟨h1, -⟩ := h
    simp at h1
  iintro - Hm
  try wp_auto
  rw [hHdr]
  wp_apply (wp_mapDelete_underlying (t := net.http.Header.ty) (K := GoString) (V := GoSlice) m ∅
    go!"Host") $$ Hm as Hm
  try wp_auto
  wp_apply wp_WithCancel iprop(True) ctx cd $$ [$Hctxi $Hctx $Hcctx] as %ctx' %γc %cancel ⟨#Hcancel, -, -, -⟩
  try wp_auto
  sorry

end proof

end net.http
end Perennial
