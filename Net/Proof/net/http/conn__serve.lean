/-
Proof of `Net/Spec/net/http/conn__serve.lean`. WIP (S5 session 9): the plan, step by step, over the
callees' specs taken as hypotheses (linked in `Net/Proof/net/http/Results.lean`). NOT LANDED.
-/
module

public import Net.Spec.net.http.conn__serve
public import Net.Spec.net.http.conn__readRequest
public import Net.Spec.net.http.conn__hijacked
public import Net.Spec.net.http.Header__get
public import Net.Spec.net.http.hasToken
public import Net.Spec.net.http.connReader__startBackgroundRead
public import Net.Spec.net.http.connReader__releaseConn
public import Net.Spec.net.http.response__Hijack
public import Net.Spec.net.Conn__RemoteAddr
public import Net.Spec.net.Conn__LocalAddr
public import Net.Spec.net.Conn__Close
public import Net.Spec.net.Conn__Write
public import Net.Spec.context.WithValuePtr
public import Net.Spec.context.WithCancelValBg
public import Net.Proof.net.http.ServerConnLemmas
public import Net.Proof.net.http.ServeDefs
public import Net.Proof.net.http.ServeLemmas
public import Net.Proof.net.ConnIo
public import Perennial.Spec.fmt.Fprintf

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.http

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [package_sem : context.Assumptions] [bufio.Assumptions]
variable [π : NetProtoGS] [net.Assumptions] [field_sem : net.FieldAssumptions]

set_option maxHeartbeats 2000000 in
theorem conn.serve.wp_proof
    (wp_readRequest : conn.readRequest.spec (GF := GF) (hG := hG))
    (wp_hijacked : conn.hijacked.spec (GF := GF) (hG := hG))
    (wp_sbr : connReader.startBackgroundRead.spec (GF := GF) (hG := hG))
    (wp_release : connReader.releaseConn.spec (GF := GF) (hG := hG))
    (wp_Hijack : response.Hijack.spec (GF := GF) (hG := hG))
    (wp_RemoteAddr : net.Conn.RemoteAddr.spec (GF := GF) (hG := hG))
    (wp_LocalAddr : net.Conn.LocalAddr.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_WithValue : context.WithValue.specPtr (GF := GF) (hG := hG))
    (wp_WithCancelBg : context.WithCancel.specValBg (GF := GF) (hG := hG))
    (wp_Timeout : net.OpError.Timeout.spec (GF := GF) (hG := hG))
    (wp_get : Header.get.spec (GF := GF) (hG := hG))
    (wp_hasToken : hasToken.spec (GF := GF) (hG := hG))
    (wp_RReset : EtcdGrove.bufio.Reader.Reset.spec (GF := GF) (hG := hG))
    (wp_NewReader : EtcdGrove.bufio.NewReader.specFresh (GF := GF) (hG := hG))
    (wp_WReset : EtcdGrove.bufio.Writer.Reset.spec (GF := GF) (hG := hG))
    (wp_NewWriterSize : EtcdGrove.bufio.NewWriterSize.specRep (GF := GF) (hG := hG)) :
    conn.serve.spec (GF := GF) (hG := hG) := by
  intro c s t cn a la ra P Q Z path ctx hc hp hlen hQ
  wp_start as ⟨#Henv, #Hrenv, #Hctxi, #Hsc, #Hsd, #Hss, #Hkeys, #Hpools, #Hrpool, ⟨%tm, #Htm⟩, #Hbg, Hc,
    #Hca, Hsend, Hrecv, Hfresh, Hrdl, #Hhl, #Hzl, #HQ400, #Hh, Htok⟩
  wp_apply wp_with_defer_recover as %defer %pnc defer pnc
  iunfold ctxKeys at Hkeys
  icases Hkeys with ⟨%sk, %lk, #Hsk, #Hlk⟩
  iunfold connNew at Hc
  icases Hc with ⟨#Hsrv, #Hrwc, Hcc, Hrma, Htls, Hwerr, Hr, Hbufr, Hbufw, Hlm, Hcur, Hst, Hmu, Hhj⟩
  ihave #Hca' := Hca
  iunfold connAt at Hca'
  icases Hca' with ⟨%nw, %Hnw, #Ht, #Hla, #Hra, #Hcat⟩
  iunfold netAddr at Hra
  icases Hra with ⟨%rp, %rv, %Hraeq, #Hrp⟩
  iunfold netAddr at Hla
  icases Hla with ⟨%lp, %lv, %Hlaeq, #Hlp⟩
  wp_load
  wp_apply wp_RemoteAddr $$ [$Hca]
  subst Hraeq
  wp_auto
  rw [method_unfold (t := go.GoType.PointerType net.TCPAddr.ty) (m := go!"String")]
  unfold net.TCPAddr.String.impl
  wp_auto
  wp_bind (ExternalOp _ _ _)
  iapply wp_net_AnyString
  iintro %rmt
  wp_auto
  ipersist Hrma
  wp_apply wp_LocalAddr $$ [$Hca]
  subst Hlaeq
  try wp_auto
  wp_apply wp_WithValue ctx contextKey.ty lk _ $$ [$Hctxi] as %q ⟨#Hq1, #Hq2, #Hq3⟩
  try wp_auto
  have hcs : go.typeSetContains (go.GoType.PointerType net.TCPConn.ty) connectionStater.ty = false := by
    go_type_set
  simp only [hcs]
  try wp_auto
  simp only [hcs]
  try wp_auto
  ihave #Hbg1 : context.ctxBg (GF := GF) (interface.mk (go.GoType.PointerType context.valueCtx.ty) #q) $$ []
  · iunfold context.ctxBg at Hbg
    icases Hbg with ⟨%n, #Hn⟩
    iunfold context.ctxBg
    iexists n + 1
    simp only [context.ctxBgN]
    iright
    iexists q, ctx, (interface.mk (go.GoType.PointerType contextKey.ty) #lk), _
    iframe #
    ipureintro; rfl
  wp_apply wp_WithCancelBg $$ [$Hctxi $Hbg1] as %ctx2 %γc %cancel ⟨#Hcancel, #Hctx2, #Hcctx2⟩
  try wp_auto
  -- the connection's reader
  icases typedPointsto_split _ _ _ $$ «$r0» with «$r0»
  simp only [TypedPointsto.typedPointstoDef, named]
  icases «$r0» with ⟨rwc, mu, conn, hasByte, byteBuf, cond, inRead, aborted, remain, -⟩
  ipersist rwc
  ipersist Hr
  ipersist Hcc
  ihave #Hsc' := Hsc
  iunfold srvConst at Hsc'
  icases Hsc' with ⟨#Htime, #Hsync, #Hatomic, -, -⟩
  imod inv_alloc curReqN ⊤ (curReqInv c) $$ [Hcur] with #Hcurinv
  · inext; iunfold curReqInv; iexists null; iframe Hcur; ileft; ipureintro; rfl
  ihave #Hcok : crConnOk (GF := GF) c $$ []
  · iunfold crConnOk; iright; iexists cancel, γc
    iframe Hsync Hatomic Hcc Hcancel Hcurinv
    ipureintro; exact hc
  imod ghostVar_alloc (GF := GF) false with ⟨%γph, Hph⟩
  icases (ghostVar_split_half γph 1 false).1 $$ Hph with ⟨Hph1, Hph2⟩
  imod token_alloc (GF := GF) with ⟨%γbg, Hbg⟩
  imod ghostVar_alloc (GF := GF) (net.rpc.connectReq path) with ⟨%γr, Hγr⟩
  let γ : CrNames := ⟨γph, γbg, γr⟩
  imod sync.init_Mutex (crInv «$r0_ptr» γ cn P (net.rpc.connectReq path) Z) ⊤
      (structFieldRef net.http.connReader go!"mu" «$r0_ptr») $$ mu [cond Hph1 Hbg] with #Hcrmu
  · inext
    iunfold crInv
    isplitl [cond]
    · ileft; iexact cond
    iunfold crPh
    iexists false
    iframe Hph1
    simp only [Bool.false_eq_true, ↓reduceIte]
    iexact Hbg
  ihave #Hcris : crIs (GF := GF) «$r0_ptr» γ cn P (net.rpc.connectReq path) Z $$ []
  · iunfold crIs; iframe Hsync Hcrmu
  ihave #Henv' := Henv
  iunfold httpEnv at Henv'
  icases Henv' with ⟨#Hbufio, #Hio, #Hfmt, -⟩
  wp_apply wp_newBufioReader_fresh wp_RReset wp_NewReader
      ⟨go.GoType.PointerType net.http.connReader.ty, #«$r0_ptr»⟩
      (by unfold net.http.connReader.ty bufio.Reader.ty; intro h; cases h)
      $$ [$Hsync $Hbufio $Hrpool] as %br Hfr
  try wp_auto
  wp_apply wp_newBufioWriterSize wp_WReset wp_NewWriterSize
      ⟨net.http.checkConnErrorWriter.ty, #(net.http.checkConnErrorWriter.mk c)⟩ 4096 (.inr rfl)
      (by unfold net.http.checkConnErrorWriter.ty bufio.Writer.ty; intro h; cases h)
      $$ [$Hsync $Hbufio $Hpools] as %bw Hbw
  try wp_auto
  wp_apply wp_readHeaderTimeout s $$ [$Hss $Hsd]
  try wp_auto
  wp_apply wp_protocols s $$ [$Hss]
  try wp_auto
  rw [method_unfold (t := go.GoType.PointerType net.http.Protocols.ty) (m := go!"UnencryptedHTTP2")]
  try wp_auto
  rw [method_unfold (t := net.http.Protocols.ty) (m := go!"UnencryptedHTTP2")]
  try wp_auto
  iclear «$res0»
  rw [method_unfold (t := go.GoType.PointerType net.http.Protocols.ty) (m := go!"HTTP1")]
  try wp_auto
  rw [method_unfold (t := net.http.Protocols.ty) (m := go!"HTTP1")]
  try wp_auto
  iclear «$res0»
  -- the connection's mutex
  imod ghostVar_alloc (GF := GF) false with ⟨%γh, Hγh⟩
  icases (ghostVar_split_half γh 1 false).1 $$ Hγh with ⟨Hγh1, Hγh2⟩
  imod sync.init_Mutex (connMuInv c γh) ⊤ (structFieldRef net.http.conn go!"mu" c) $$ Hmu
      [Hhj Hγh1] with #Hcmu
  · inext; iunfold connMuInv; iexists false; iframe Hhj Hγh1
  ipersist Htls
  wp_for
  ihave Hmain : crMain (GF := GF) «$r0_ptr» γ cn P Q c [] (0 : w64) $$
      [Hph2 conn hasByte inRead aborted remain byteBuf Hsend Hrecv Hrdl]
  · iunfold crMain; iframe Hph2; iexists false; iframe conn hasByte inRead aborted remain Hsend Hrecv Hrdl
    iexists _; iexact byteBuf
  wp_apply wp_readRequest c s «$r0_ptr» br γ γh t cn a _ _ P Q Z path rmt [] (0 : w64) ctx2 _ (DFrac.own 1)
      hc hp hlen (by decide) $$ [$Henv $Hrenv $Hctxi $Hsc $Hsd $Hpools $Hctx2 $Hcctx2 $Hsrv $Hr $Hbufr
        $Hrwc $Hrma $Htls $Hcmu $Hγh2 $Hlm $Hcris $Hhl $Hzl $Hcok $rwc $Hca $Hmain $Hfr]
    as %w %err ⟨Hγh2, Hbr, Hbufr, Hres⟩
  try wp_auto
  icases Hres with (⟨%Herr, Hlm, %γe, %r, Hhead, #Hrerr⟩ |
    ⟨%Herr, Hlm, %req, %u, %m, %cl, %nb, %ctx', Hreq, Hu, Hm, Hresp, Hph, Hfields, Hremain, Hbb,
      Hsend, Hrecv, %b, Hrdl, Hdis⟩)
  · -- an error: Go's 400, or nothing; then the connection closed
    iunfold crHead at Hhead
    icases Hhead with ⟨Hph, %Hrl, %ab, Hcconn, Hhb, Hir, Hab, Hrem, Hbb, Hsend, Hrecv, Hrdl, Hmono⟩
    ihave #Hci := sendTok_connIs $$ Hsend
    ihave #Hrenv' := Hrenv
    iunfold readEnv at Hrenv'
    icases Hrenv' with ⟨-, ⟨%ed, #Hed⟩, -⟩
    ihave #Hsw := net.conn_streamWriterOk wp_Write t cn true a _ _ ed Q hQ $$ [$Hca $Hed]
    iunfold EtcdGrove.io.streamWriterOk at Hsw
    icases Hsw with ⟨-, #Hw⟩
    try wp_auto
    rw [method_unfold (t := go.GoType.PointerType net.http.Server.ty) (m := go!"initialReadLimitSize")]
    try wp_auto
    rw [method_unfold (t := go.GoType.PointerType net.http.Server.ty) (m := go!"maxHeaderBytes")]
    try wp_auto
    ihave #Hsd' := Hsd
    iunfold srvDflt at Hsd'
    icases Hsd' with ⟨-, -, #HMHB, -⟩
    try wp_auto
    iclear «$res0»
    wp_if_destruct
    all_goals try (wp_apply wp_setState c s _ (W64 1) (by decide) $$ [$Hsrv $Hsc $Hst] as Hst)
    all_goals try wp_auto
    all_goals wp_apply wp_shuttingDown s $$ [$Hss $Hatomic]
    all_goals try wp_auto
    all_goals ihave ⟨%xt, #Hvtl, %Hne⟩ := reqErr_not_tooLarge γe err $$ [$Henv $Hrenv $Hrerr]
    all_goals ihave %Hsh := reqErr_shape γe err $$ Hrerr
    all_goals rcases Hsh with ⟨x, hx⟩ | ⟨msg, hx⟩ | ⟨pe, hx⟩ <;> subst hx <;> try wp_auto
    all_goals simp only [interface.mkOk, opError_ty_ne_errorString, protocolError_ty_ne_errorString,
      ↓reduceIte]
    all_goals try wp_auto
    all_goals try (
      have hxt : x ≠ xt := fun h => Hne (by rw [h])
      simp only [decide_eq_false hxt, decide_false, Bool.true_eq_false]
      try wp_auto)
    all_goals wp_apply wp_isUnsupportedTEError γe _ $$ [$Hrerr]
    all_goals try wp_auto
    all_goals wp_apply wp_isCommonNetReadError wp_Timeout γe _ $$ [$Hrerr $Hrenv] as %bnr -
    all_goals try wp_auto
    all_goals cases bnr
    all_goals try simp only [decide_true, decide_false, Bool.true_eq_false]
    all_goals wp_auto
    all_goals try (
      wp_apply wp_Fprintf_noVerb ⟨go.GoType.PointerType net.TCPConn.ty, #t⟩ _ rfl (sendTok (Gg := hG.goose_globalGS) cn true Q [])
          (fun _ _ => iprop(True)) $$ [$Hsend] as %n0 %e0 -
      · iintro %sl %Ψ Hs Hsl HΨ
        simp only [net.connIface]
        iapply Hw $$ %([] : List w8) %sl %(DFrac.own 1) %_ %Ψ [Hs Hsl]
        · iframe Hs Hsl
          simp only [List.nil_append, net.rpc.badReqAns]
          imodintro
          iexact HQ400
        inext
        iintro %n %err ⟨%k, -, Hsl, -, -⟩
        iapply HΨ $$ Hsl
        itrivial
      try wp_auto)
    all_goals wp_for_post
    all_goals (
      iunfold context.cancelSpec at Hcancel
      wp_bind (App (Val #cancel) (Val #()))
      iapply Hcancel
      · imodintro; itrivial
      inext
      iintro -
      try wp_auto
      wp_apply wp_recoverPanic $$ [$pnc] as pnc
      try wp_auto
      wp_apply wp_hijacked c γh false $$ [$Hsync $Hcmu $Hγh2] as Hγh2
      try wp_auto
      wp_apply wp_conn_close wp_Close wp_RReset wp_WReset c br bw t cn a _ _
        $$ [$Hsync $Hrpool $Hpools $Hbufr $Hbr $Hbufw $Hbw $Hrwc $Hca $Hci] as ⟨Hbufr, Hbufw⟩
      try wp_auto
      wp_apply wp_setState c s _ (W64 4) (by decide) $$ [$Hsrv $Hsc $Hst] as Hst
      try wp_auto
      iapply HΦ
      iexact Htok)
  · -- the request: the handler, which hijacks the connection
    subst Herr
    ihave #Hsd' := Hsd
    iunfold srvDflt at Hsd'
    icases Hsd' with ⟨-, -, #HMHB, -⟩
    try wp_auto
    rw [method_unfold (t := go.GoType.PointerType net.http.Server.ty) (m := go!"initialReadLimitSize")]
    try wp_auto
    rw [method_unfold (t := go.GoType.PointerType net.http.Server.ty) (m := go!"maxHeaderBytes")]
    try wp_auto
    iclear «$res0»
    try wp_if_destruct
    all_goals try (wp_apply wp_setState c s _ (W64 1) (by decide) $$ [$Hsrv $Hsc $Hst] as Hst)
    all_goals try wp_auto
    wp_apply wp_shuttingDown s $$ [$Hss $Hatomic]
    try wp_auto
    iunfold respNew at Hresp
    icases Hresp with ⟨#Hwc, #Hwreq, #Hwrb, ⟨%fw, %γw, #Hwcf, #Hwcancel⟩, Hhd, Hec, Hwh, ⟨%ww, Hww, Hwraw⟩,
      ⟨%hh, Hhh, Hhhm⟩, #Hnotify⟩
    iStructNamedPrefix Hreq "R"
    try wp_auto
    rw [method_unfold (t := go.GoType.PointerType net.http.Request.ty) (m := go!"expectsContinue")]
    try wp_auto
    rw [method_unfold (t := go.GoType.PointerType net.http.Header.ty) (m := go!"get")]
    try wp_auto
    wp_apply wp_get m _ ∅ go!"Expect" $$ [$Hm] as %v1 ⟨Hm, -, %Hv1⟩
    · unfold hdrVals; simp only [GMap.lookup_empty]; itrivial
    rw [Hv1 (GMap.lookup_empty _)]
    try wp_auto
    wp_apply wp_hasToken $$ []
    · ipureintro; decide
    try wp_auto
    rw [method_unfold (t := go.GoType.PointerType net.http.Header.ty) (m := go!"get")]
    try wp_auto
    wp_apply wp_get m _ ∅ go!"Expect" $$ [$Hm] as %v2 ⟨Hm, -, %Hv2⟩
    · unfold hdrVals; simp only [GMap.lookup_empty]; itrivial
    rw [Hv2 (GMap.lookup_empty _)]
    try wp_auto
    -- `c.curReq.Store(w)`
    wp_bind (App (Val #(methods _ _ _)) (Val #w))
    iapply (sync.atomic.Pointer.wp_Store (T' := net.http.response) net.http.response.ty
      (structFieldRef net.http.conn go!"curReq" c) w)
    · iPkgInit
    unfold curReqInv
    iinv Hcurinv with ⟨%v0, >Hv, -⟩ Hclose
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists v0
    iframe Hv
    iintro Hv
    imod Hmask
    imod Hclose $$ [Hv] with -
    · inext; iexists w; iframe Hv
      by_cases hw : w = null
      · ileft; ipureintro; exact hw
      · iright; iframe Hnotify; ipureintro; exact hw
    imodintro
    try wp_auto
    rw [method_unfold (t := go.GoType.PointerType net.http.body.ty) (m := go!"bodyRemains")]
    try wp_auto
    wp_apply wp_with_defer as %defer2 Hdefer2
    try wp_auto
    iclear «$res0»
    -- the background read
    icases Hfields with ⟨%ab, Hcconn, Hhb, Hir, Hab⟩
    icases Hbb with ⟨%arr, Hbb⟩
    wp_apply wp_sbr «$r0_ptr» γ t cn a _ _ P (net.rpc.connectReq path) Z c ab b arr
      $$ [$Hcris $Hhl $Hrenv $rwc $Hca $Hrdl $Hph $Hγr $Hcconn $Hhb $Hir $Hab $Hcok $Hbb $Hrecv]
      as ⟨Hph, Hγr, %b', Hrdl⟩
    try wp_auto
    -- the handler, with the right to hijack
    ipersist Hbufr
    ipersist Hbufw
    let N : HjNames := ⟨γ, γh, w, c, «$r0_ptr», s, t, cn, a,
      interface.mkOk (go.GoType.PointerType net.TCPAddr.ty) #lp,
      interface.mkOk (go.GoType.PointerType net.TCPAddr.ty) #rp, tm, br, bw, ww⟩
    ihave Hhj : hijackOk (GF := GF) w cn a P Q (net.rpc.connectReq path) (hjDone N (net.rpc.connectReq path)) $$
        [Hhd Hec Hwh Hww Hwraw Hγh2 Hbw Hst Hph Hγr Hsend Hfresh Hrdl]
    · iapply (wp_Hijack N P Q (net.rpc.connectReq path) Z)
      iunfold hjPre
      iframe Hhd Hec Hwh Hwc Hww Hwraw Hcmu Hγh2 Hr Hrwc Hbufr Hbufw Hbw Hsrv Hsc Hst Hcris Htm rwc Hph Hγr
        Hca Hsend Hfresh Hzl Hpools
      iexists b'; iexact Hrdl
    ipersist RMethod
    ipersist RRemoteAddr
    iunfold srvHandler at Hh
    wp_bind (App (App (Val #(methods _ _ _)) _) _)
    iapply Hh $$ %w %req %_ %u %m %cl %nb %ctx' %rmt %(hjDone N (net.rpc.connectReq path)) %_
      [RURL RProto RProtoMajor RProtoMinor RHeader RBody RGetBody RContentLength RTransferEncoding RClose
        RHost RForm RPostForm RMultipartForm RTrailer RRequestURI RTLS RCancel RResponse RPattern Rctx Rpat
        «Rmatches'» RotherValues Hu Hm Hhj Htok]
    · iframe Hu Hm Hhj Htok
      isplitr
      · ipureintro; rfl
      isplitr
      · have hM : (rrReqVal path u m cl nb ctx' rmt).Method' = go!"CONNECT" := rfl
        simp only [hM]
        iunfold reqHead; iframe RMethod; iexists _; iexact RRemoteAddr
      iunfold reqRest
      iframe
    inext
    iintro ⟨Htok, Hdone⟩
    try wp_auto
    sorry
/-PLAN
  -- 1. `with_defer_recover`; RemoteAddr (+ `TCPAddr.String`: `wp_net_AnyString`), store remoteAddr;
  --    `WithValue(ctx, LocalAddrContextKey, LocalAddr())` (wp_WithValue; ctxBg grows by one).
  -- 2. the two `connectionStater` assertions on a `*TCPConn` fail (TypeAssert2 to an interface).
  -- 3. `WithCancel` (wp_WithCancelBg); store `c.cancelCtx`, persist it; `defer cancelCtx()`.
  -- 4. `&connReader{conn: c, rwc: c.rwc}`: iStructNamed; ghost names (ph halves, bg token, r := hs);
  --    `sync.init_Mutex` with `crInv` (cond nil, phase false: token); `crIs`; `crMain cr γ cn P Q c [] 0`.
  --    curReq invariant (`inv curReqN (curReqInv c)`) from connNew's ownPointer; `crConnOk c`.
  -- 5. `newBufioReader(c.r)`: a freshReader variant of `wp_newBufioReader` (pool: Reset gives it;
  --    NewReader: unfold NewReaderSize/reset); `newBufioWriterSize(checkConnErrorWriter{c}, 4096)`.
  -- 6. readHeaderTimeout (srvServe: 0; srvDflt ReadTimeout 0): no deadline; protocols(): Protocols nil,
  --    TLSNextProto nil (lookup on a nil map), HTTP1 set, UnencryptedHTTP2 unset; `sync.init_Mutex` for
  --    `c.mu` with `connMuInv c γh` (hijackedv false).
  -- 7. `c.readRequest(ctx)` (wp_readRequest; c.bufr at 1); `c.r.remain != initialReadLimitSize()`
  --    -> setState(StateActive) (`wp_setState`); shuttingDown: `Bool.Load` on srvServe's discarded false.
  -- 8. error: `err == errTooLarge` false (`httpEnv_errTooLarge`: messages differ from io.EOF's,
  --    ErrUnexpectedEOF's, "malformed HTTP "...; other types differ); isUnsupportedTEError false;
  --    isCommonNetReadError: either way; statusError assertion false; `fmt.Fprintf(c.rwc, 400)`:
  --    SprintfOut of a verb-free format is the format; the write through `sendTok` with `HQ400`
  --    (`conn_streamWriterOk`/`write_acc`). Return: defers: cancel (cancelSpec), recover nil,
  --    inFlightResponse nil, hijacked false -> c.close(): finalFlush (putBufioReader on rawReader,
  --    `bufw.Flush()` on a raw writer: nothing to write, putBufioWriter), Conn.Close (`close_au`),
  --    setState(StateClosed).
  -- 9. success: persist c.bufr/c.bufw; split `req ↦ rrReqVal ...` (iStructNamed), persist Method and
  --    RemoteAddr (`reqHead`), the rest `reqRest`; expectsContinue false and `Header.get("Expect")`
  --    "" (empty map); `c.curReq.Store(w)` through the invariant (respNotify w from respNew);
  --    bodyRemains(nil) false; startBackgroundRead; `hjPre` from respNew + fields; `hijackOk` by
  --    wp_Hijack; the handler (`srvHandler`) returns threadTok and `hjDone`; `w.cancelCtx()`;
  --    hijacked() true; releaseConn (crLeft); return: defers: cancel, recover nil, hijacked true.
PLAN-/

end proof

end net.http
end Perennial
