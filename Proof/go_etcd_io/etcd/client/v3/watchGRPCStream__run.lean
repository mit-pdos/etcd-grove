/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__run.lean` (the watch slice's unit W-C).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.ReceiptTactics
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__run
public import Proof.go_etcd_io.etcd.client.v3.WatchRun
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__newWatchClient
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__nextResume
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__dispatchEvent
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__addSubstream
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__closeSubstream
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__joinSubstreams
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__serveSubstream
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__newWatcherStreamBufLogger
public import Spec.go_etcd_io.etcd.client.v3.watchRequest__toPB
public import Spec.go_etcd_io.etcd.client.v3.progressRequest__toPB
public import Proof.go_etcd_io.etcd.client.v3.MapSplit
public import Spec.go_etcd_io.etcd.client.v3.watcher__closeStream
public import Spec.go_etcd_io.etcd.client.v3.isHaltErr
public import Spec.go_etcd_io.etcd.client.v3.ContextError
public import Spec.errors.IsStatusErr
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__backoffIfUnavailable
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Int64
public import Perennial.Proof.time
public import Proof.go_etcd_io.etcd.client.v3.WatchClientModel
public import Proof.go_etcd_io.etcd.client.v3.WatchContent
public import Proof.go_etcd_io.etcd.client.v3.WatchCompl
public import Proof.go_etcd_io.etcd.client.v3.WatchApiLemmas
public import Proof.go_etcd_io.etcd.client.v3.WatchResumeSrv
public import Proof.go_etcd_io.etcd.client.v3.WatchEpoch
public import Proof.go_etcd_io.etcd.client.v3.InvLessor

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client



section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem watchGRPCStream.run.wp_proof
    (wp_newWC : watchGRPCStream.newWatchClient.spec (GF := GF) (hG := hG))
    (wp_nextResume : watchGRPCStream.nextResume.spec (GF := GF) (hG := hG))
    (wp_dispatch : watchGRPCStream.dispatchEvent.spec (GF := GF) (hG := hG))
    (wp_addSub : watchGRPCStream.addSubstream.spec (GF := GF) (hG := hG))
    (wp_closeSub : watchGRPCStream.closeSubstream.spec (GF := GF) (hG := hG))
    (wp_join : watchGRPCStream.joinSubstreams.spec (GF := GF) (hG := hG))
    (wp_serveSub : watchGRPCStream.serveSubstream.spec (GF := GF) (hG := hG))
    (wp_bufLogger : watchGRPCStream.newWatcherStreamBufLogger.spec (GF := GF) (hG := hG))
    (wp_toPB : watchRequest.toPB.spec (GF := GF) (hG := hG))
    (wp_ptoPB : progressRequest.toPB.spec (GF := GF) (hG := hG))
    (wp_closeStream : watcher.closeStream.spec (GF := GF) (hG := hG))
    (wp_isHaltErr : isHaltErr.spec (GF := GF) (hG := hG))
    (wp_Debug : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (wp_zapError : zap.Error.spec (GF := GF) (hG := hG))
    (wp_zapInt64 : zap.Int64.spec (GF := GF) (hG := hG))
    (wp_ctxErr : ContextError.spec (GF := GF) (hG := hG))
    (wp_isStatus : errors.IsStatusErr.spec (GF := GF) (hG := hG))
    (wp_backoff : watchGRPCStream.backoffIfUnavailable.spec (GF := GF) (hG := hG)) :
    watchGRPCStream.run.spec (GF := GF) (hG := hG) := by
  intro V G callSl m0 s0 rc γrc
  wp_start as ⟨#HW, #HG, #Hco, Hsub, Hm0, Hres, Hs0, HcE, Hrc, Hrcb, Hgen, Hrcons, Hprod0, Hep0, Hdn,
    Had, Htt, Hwsa⟩
  ihave #HG' := HG
  iunfold isWGS at HG'
  icases HG' with ⟨%Hwgs, -, #Hsf, %Hlg, #Fowner, #Fremote, #FcallOpts, #Fctx, #FctxKey, #Fcancel,
    #Freqc, #Frespc, #Fdonec, #Ferrc, #Fclosingc, #Flg, #HGctx, #HGcancel, #Hreqb, #Herrb, #Hclb,
    #HGdone, #Hrspsc⟩
  ihave #Hsf' := Hsf
  iunfold watchSrvFacts at Hsf'
  icases Hsf' with ⟨#Hstub, #Hconn⟩
  iunfold watchConnFacts at Hconn
  icases Hconn with ⟨#Hgc, #Hgs, #Hdesc, #Htoks, #HnoRetry, #Hsmall, #HnoDup,
    #Heof, #HerrNew, #Hcea, #Hvars, %Hpre⟩
  -- S2 and S3, facts of the verified server (unit W-M2)
  ihave #HS2 := srvProgressAllAnswers_holds V.R
  ihave #HS3 := srvEventIdsAssigned_holds V.R
  wp_apply wp_with_defer
  iintro %defer Hdefer
  wp_auto
  wp_apply (wp_map_make1 (K := Loc) (V := Unit) (go.GoType.PointerType go_etcd_io.etcd.client.v3.watcherStream.ty)
    (go.GoType.StructType [])) as %clm Hclm
  ipersist w
  ipersist closing
  wp_bind (exceptionDo _)
  iapply (wp_wand_r (Φ := fun v => iprop(⌜v = #()⌝ ∗ client.runExit V G closeErr_ptr clm)))
  isplitl [Hsub Hm0 Hres Hs0 HcE Hrc Hrcb Hgen Hrcons Hprod0 Hep0 Hdn Had Htt Hwsa wc closeErr Hclm]
  · wp_apply wp_newWC V G callSl m0 s0 rc γrc 0 [] [] (StreamNames.mk G.γws G.γws G.γws G.γws G.γws G.γws G.γws)
      client.RunSt.init ∅ $$ [Hsub Hm0 Hres Hs0 Hrc Hrcb Hgen Hprod0 Hep0 Hwsa Had Htt]
      as %wcv %err ⟨%m1, %s1, %rc1, %γrc1, %l1, Hsub, Hm1, Hres, Hs1, Hrc, Hrcb, Hgen, %HgOk0, Hwsa,
        Hels0, Had, Htt, Hcase⟩
    · iframe #; iframe
      isplitr
      · ipureintro; exact client.gOk_init
      iapply BigSepM.bigSepM_empty.2; itrivial
    icases Hcase with (⟨%Herr, %γs, %Dn, %cd', %γc0, #Hcws, Hstok, #Hspec, Hep⟩ |
      ⟨⟨%Hwcn, %Herr⟩, #Hse, -, -⟩)
    rotate_left
    · cases err with
      | nil => exact absurd rfl Herr
      | ok ei =>
      wp_auto
      isplitr
      · ipureintro; rfl
      unfold client.runExit
      iexists (StreamNames.mk G.γws G.γws G.γws G.γws G.γws G.γws G.γws), client.RunSt.init.reconnect l1, ∅,
        GoInterface.ok ei, GoInterface.nil, m1, s1, 1
      simp only [client.RunSt.init, client.RunSt.reconnect]
      iframe
      iframe Hse
      ihave #Hnil := statusErrOk_nil (GF := GF)
      iframe Hnil
      isplitr
      · ipureintro; exact HgOk0
      iapply Hels0
    subst Herr
    wp_auto
    wp_apply (wp_map_make1 (K := w64) (V := Unit) go.int64 (go.GoType.StructType [])) as %csm Hcsm
    simp only [_root_.Perennial.time.Millisecond]
    wp_auto
    imod monoListLbOwn_nil (GF := GF) (A := v3rpc.WatchRespM) γs.down with #Hlb0
    ihave Hepst := client.epochSt_first G γs γc0 $$ Hep
    ihave IH : iprop(∃ (bo : w64) (γs : StreamNames) (b n : Nat) (wcv : GoInterface)
        (Dn : Nat → v3rpc.WatchRespM → IProp GF) (cd' : context.ContextDesc (IProp GF)) (rc : Loc)
        (γrc : ChanNames) (csm : Loc),
        "Hcore" ∷ client.runCore V G γs b n clm csm ∗
        "closeErr" ∷ closeErr_ptr ↦ GoInterface.nil ∗ "cur" ∷ cur_ptr ↦ (null : Loc) ∗
        "backoff" ∷ backoff_ptr ↦ bo ∗ "wc" ∷ wc_ptr ↦ wcv ∗ "cancelSet" ∷ cancelSet_ptr ↦ csm ∗
        "Hrc" ∷ wgsF G.wgs go!"resumec" ↦ rc ∗
        "Hrcb" ∷ ownBroadcastChan rc γrc (monoNatLbOwn G.γend (n + 1)) .Pending ∗
        "#Hcws" ∷ v3rpc.cliWatchStreamIs wcv γs (v3rpc.watchUp V.R.γ) Dn cd' ∗
        "#Hspec" ∷ v3rpc.watchSpec V.R γs Dn) $$ [Hclm Hcsm Hsub Hm1 Hres Hs1 HcE Hstok Hrcons
        Hepst Hwsa Had Htt Hdn Hgen closeErr cur backoff Hels0 wc cancelSet Hrc Hrcb]
    · iexists _, γs, 0, 1, _, Dn, cd', rc1, γrc1, csm
      simp only [named]
      iframe
      iframe #
      unfold client.runCore
      iexists client.RunSt.init.reconnect l1, ∅, [], m1, s1, GoInterface.nil
      simp only [client.RunSt.init, client.RunSt.reconnect]
      iframe
      ihave #Hnil := statusErrOk_nil (GF := GF)
      iframe Hnil
      isplitr
      · ipureintro; rfl
      isplitr
      · unfold v3rpc.downLbW; iexact Hlb0
      isplitr
      · ipureintro; exact HgOk0
      isplitr
      · iapply BigSepL.bigSepL_nil.2; itrivial
      isplitr
      · iapply BigSepL.bigSepL_nil.2; itrivial
      isplitr
      · imodintro; iapply BigSepL.bigSepL_nil.2; itrivial
      iapply Hels0
    ihave #HGc := HGctx
    iNamedPrefix HGc "W"
    wp_for IH
    ihave #Hcws' := Hcws
    iunfold v3rpc.cliWatchStreamIs at Hcws'
    iunfold cliBidiStreamIs at Hcws'
    icases Hcws' with ⟨%ci, %Hci, #HSend, #HRecv, -, -⟩
    subst Hci
    ihave #Hrcu := ownBroadcastChan_Unknown $$ Hrcb
    wp_apply +noauto WHDone as %dch %dγ #Hdone
    wp_auto_lc 6
    wp_apply_core chan.wp_select_blocking
    -- reqc
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists go_etcd_io.etcd.client.v3.watchStreamRequest, inferInstance, inferInstance, inferInstance,
        inferInstance, G.reqc, G.γreq
      isplit
      · ipureintro; rfl
      isplit
      · iapply is_bag_is_chan $$ Hreqb
      iapply bag_recv_au G.γreq G.reqc (reqP V) _ $$ [$Hlc1 $Hlc2] Hreqb
      inext
      iintro %rv #Hrq
      iunfold reqP at Hrq
      icases Hrq with (⟨%wr, %P0, ⟨%Hrv, %Hwrn⟩, #Hro, #Hrrev, #Hrretc, #Hctx, #Hretb, %Hok, #Hsrd0⟩ |
        ⟨%pr, %Hrv⟩)
      rotate_left
      · -- a progress request (unit W-K): sent up the stream
        subst Hrv
        iunfold client.runCore at Hcore
        icases Hcore with ⟨%S, %U, %rcv, %mref, %s, %e, Hclm, Hcsm, Hsub, Hm, Hres, Hs, HcF, #He,
          Hstok, Hrcons, %Hrcv, Hepst, #HDlb, %HgOk, Hans, Hids, #Hinfo, Hwsa, Hels, Had, Htt, Hdn, Hgen⟩
        wp_auto
        wp_apply wp_ptoPB pr as %preq Hpsend
        wp_apply HSend $$ %S.L %preq %(.progress) [Hstok Hpsend] as %err ⟨-, Hres'⟩
        · iframe
          unfold v3rpc.watchUp v3rpc.watchReqOk
          isplitr <;> itrivial
        ihave ⟨%L', %HL', Hstok⟩ : iprop(∃ L' : List v3rpc.WatchReqM,
            ⌜L' = S.L ∨ L' = S.L ++ [.progress]⌝ ∗ cliSendTok (Req := v3rpc.pbWatchRequest) γs L')
            $$ [Hres']
        · icases Hres' with (⟨-, Htok⟩ | ⟨-, %L', %HL', Htok⟩)
          · iexists _; iframe; ipureintro; right; rfl
          · iexists L'; iframe; ipureintro; exact HL'
        obtain ⟨Hg2, Hph2⟩ := client.progress_ok (S := S) (U := U) HgOk HL'
        ihave Hels := BigSepM.bigSepM_impl
            (Ψ := fun ws (_ : Unit) => client.wsElem V G n γs (S.sentProgress L') ws) $$ Hels []
        · iintro !> %ws' %u %Hws' Hw'
          iapply (client.wsElem_mono V G n γs (S := S) (S' := S.sentProgress L') ws' rfl
            (fun ph' h => Hph2 ws' ph' h)
            (fun X _ => client.cancels_of_snoc .progress X (by intro e; cases e) HL')) $$ Hw'
        ihave Hfin : iprop(▷ client.runCore V G γs b n clm csm) $$
            [Hclm Hcsm Hsub Hm Hres Hs HcF Hstok Hrcons Hepst Hans Hids Hwsa Hels Had Htt Hdn Hgen]
        · inext
          unfold client.runCore
          iexists S.sentProgress L', U, rcv, mref, s, e
          have r0 : (S.sentProgress L').Dm = S.Dm := rfl
          have r1 : (S.sentProgress L').ansd = S.ansd := rfl
          have r2 : (S.sentProgress L').regs = S.regs := rfl
          have r3 : (S.sentProgress L').M = S.M := rfl
          have r4 : (S.sentProgress L').CL = S.CL := rfl
          have r5 : (S.sentProgress L').l = S.l := rfl
          have r6 : (S.sentProgress L').L = L' := rfl
          have r7 : (S.sentProgress L').CS = S.CS := rfl
          rw [r0, r1, r2, r3, r4, r5, r6, r7]
          iframe
          iframe #
          ipureintro; exact ⟨Hrcv, Hg2⟩
        cases err with
        | nil =>
          wp_auto
          wp_for_post
          iexists bo, γs, b, n, _, Dn, cd', rc, γrc, csm
          simp only [named]
          iframe closeErr cur backoff wc cancelSet Hrc Hrcb Hcws Hspec
          iexact Hfin
        | ok ei =>
          wp_auto
          wp_apply wp_zapError as %f1 -
          wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
          isplitr
          · ipureintro; rfl
          iintro %fsl ⟨-, -⟩
          wp_auto
          wp_apply wp_Debug V.lg _ _ $$ []
          · iframe #; ipureintro; exact Hlg
          wp_for_post
          iexists bo, γs, b, n, _, Dn, cd', rc, γrc, csm
          simp only [named]
          iframe closeErr cur backoff wc cancelSet Hrc Hrcb Hcws Hspec
          iexact Hfin
      subst Hrv
      iunfold client.runCore at Hcore
      icases Hcore with ⟨%S, %U, %rcv, %mref, %s, %e, Hclm, Hcsm, Hsub, Hm, Hres, Hs, HcF, #He,
        Hstok, Hrcons, %Hrcv, Hepst, #HDlb, %HgOk, Hans, Hids, #Hinfo, Hwsa, Hels, Had, Htt, Hdn, Hgen⟩
      wp_auto
      wp_apply (chan.wp_make2 (V := go_etcd_io.etcd.client.v3.WatchResponse) (W64 1)) as
        %outc %γo ⟨#Houtc, %Hγo, Houto⟩
      · ipureintro; word
      ihave #Hwrv : iprop(wr ↦□ (go_etcd_io.etcd.client.v3.watchRequest.mk (interface.ok P0.ctx)
          P0.key P0.ed P0.rev P0.cn P0.pn false P0.wbl P0.flt false P0.retc)) $$ []
      · iunfold wrRO at Hro
        icases Hro with ⟨#Rctx, #Rkey, #Rend, #Rcn, #Rpn, #Rfrag, #Rwbl, #Rflt, -, #RprevKV⟩
        iapply typedPointsto_combine _ _ _ Hwrn
        simp only [TypedPointsto.typedPointstoDef]
        iframe #
      wp_auto
      wp_apply (chan.wp_make1 (V := Loc)) as %recvc %γrc2 ⟨#Hrecvc, %Hγrc2, Hrecvo⟩
      ihave %Hwsn := typedPointsto_not_null _ _ _ $$ «$r0»
      iStructNamed «$r0»
      iStructNamed initReq
      ipersist ctx; ipersist key; ipersist end'; ipersist createdNotify; ipersist progressNotify
      ipersist fragment; ipersist watchBufLogEnabled; ipersist filters; ipersist prevKV
      ipersist recvc
      icases client.ptsto_split_half _ _ $$ rev with ⟨Hrev1, Hrev2⟩
      wp_bind (If _ _ _)
      iapply (wp_wand_r (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ws_ptr ↦ «$r0_ptr» ∗ ∃ bl : Loc,
          wsF «$r0_ptr» go!"bufLogger" ↦ bl ∗ bufLogOk «$r0_ptr» bl)))
      isplitl [bufLogger ws]
      · cases hw : P0.wbl
        · wp_auto
          isplitr
          · ipureintro; rfl
          iframe
          unfold bufLogOk; ileft; ipureintro; rfl
        · wp_auto
          ihave #Hnf : (□ ∀ Φ : val → IProp GF, ▷ (∀ t : _root_.Perennial.time.Time, Φ #t) -∗
              WP (App (Val #(functions _root_.Perennial.time.Now [])) (Val #())) {{ Φ }}) $$ []
          · imodintro; iintro %Φ' HΦ'
            wp_apply time.wp_Now as %t1 -
            iapply HΦ'
          wp_apply wp_bufLogger G.wgs «$r0_ptr» V.lg P0.key P0.ed _ $$ [] as %bl #Hbl
          · iframe #; ipureintro; exact Hlg
          isplitr
          · ipureintro; rfl
          iframe
          unfold bufLogOk; iright; iexact Hbl
      iintro %v ⟨%Hv, ws, %bl, HbL, #HbLok⟩
      subst Hv
      wp_auto
      wp_apply (chan.wp_make1 (V := Unit)) as %dnc %γdn ⟨#Hdnc, %-, Hdno⟩
      icases client.ptsto_split_half_loc _ _ $$ donec with ⟨Hdnf1, Hdnf2⟩
      imod dghostVar_alloc false with ⟨%γx, Hx⟩
      -- (D24) the goroutine's first lifetime: its deposit's flag, `run`'s token
      imod dghostVar_alloc false with ⟨%γt, Hγt⟩
      icases dghostVar_halves _ _ $$ Hγt with ⟨Hγt1, Hγt2⟩
      imod dghostVar_alloc () with ⟨%γk, Htk⟩
      let L : LifePrm := ⟨dnc, γdn, γt, γk, n⟩
      imod mono_list_own_alloc (GF := GF) [P0.rev - W64 1] with ⟨%γhi, Hhia, #Hhilb⟩
      imod mono_list_own_alloc (GF := GF) [P0.rev - W64 1] with ⟨%γcur, Hcura, #Hcurlb⟩
      ihave #Hhi0 := monoListIdxOwn_get (GF := GF) 0 (P0.rev - W64 1) rfl $$ Hhilb
      ihave #Hcur0 := monoListIdxOwn_get (GF := GF) 0 (P0.rev - W64 1) rfl $$ Hcurlb
      -- (K2e-7d) the second cursors: the dispatch's and the contract's
      imod mono_list_own_alloc (GF := GF) [P0.rev - W64 1] with ⟨%γh2, Hh2a, #Hh2lb⟩
      imod mono_list_own_alloc (GF := GF) [P0.rev - W64 1] with ⟨%γcur2, Hcur2a, #Hcur2lb⟩
      ihave #Hh20 := monoListIdxOwn_get (GF := GF) 0 (P0.rev - W64 1) rfl $$ Hh2lb
      ihave #Hcur20 := monoListIdxOwn_get (GF := GF) 0 (P0.rev - W64 1) rfl $$ Hcur2lb
      -- (D24) the positions' statuses: the goroutine starts at `0`
      imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Bool) with ⟨%γps, Hpsa⟩
      imod ghost_map_insert_persist (γ := γps) 0 true (GMap.lookup_empty 0) $$ Hpsa with
        ⟨Hpsa, #Hps0⟩
      let Ppre : WsPrm GF := WsPrm.mk P0.o P0.rev P0.ctx P0.cs P0.key P0.ed P0.cn P0.pn P0.wbl
        P0.flt P0.retc P0.γret «$r0_ptr» (EtcdWatchNames.mk G.γr γcur γcur2 (cplOf P0)) outc recvc G.γr γhi γh2 γx
        P0.sr γps
      imod start_spsc (V := go_etcd_io.etcd.client.v3.WatchResponse) outc
        (rangeWatchElem (EM := V.EM) Ppre.γ V.pfx P0.o P0.rev) (fun _ => iprop(True)) γo
        $$ Houtc [Houto] with ⟨%γsp, #Hosp, Hoprod, Hocons⟩
      · iright; iexact Houto
      imod start_sspsc (V := Loc) recvc (client.recvElem V Ppre) (fun _ => iprop(True)) γrc2
        $$ Hrecvc Hrecvo with ⟨%γrr, #Hrsp, Hrprod, Hrcons2⟩
      let P : WsPrm GF := WsPrm.mk P0.o P0.rev P0.ctx P0.cs P0.key P0.ed P0.cn P0.pn P0.wbl
        P0.flt P0.retc P0.γret «$r0_ptr» (EtcdWatchNames.mk γsp γcur γcur2 (cplOf P0)) outc recvc γrr γhi γh2 γx
        P0.sr γps
      have eq1 : (isSpsc γsp outc (rangeWatchElem (EM := V.EM) Ppre.γ V.pfx P0.o P0.rev)
          (fun _ => iprop(True)) : IProp GF) =
          isSpsc P.γ.spsc P.outc (rangeWatchElem (EM := V.EM) P.γ V.pfx P.o P.rev)
            (fun _ => iprop(True)) := rfl
      have eq2 : (isSspsc γrr recvc (client.recvElem V Ppre) (fun _ => iprop(True)) : IProp GF) =
          isSspsc P.γr P.recvc (client.recvElem V P) (fun _ => iprop(True)) := rfl
      irevert Hosp Hrsp
      rw [eq1, eq2]
      iintro #Hosp #Hrsp
      -- (D24) the lifetime's `donec`
      imod alloc_broadcast_chan (E := ⊤) (lifeQ V G P L) γdn dnc $$ Hdnc Hdno with Hdnb
      icases ownBroadcastChan_dup_unknown _ _ _ _ $$ Hdnb with ⟨Hdnb, #Hdnu⟩
      ihave #HP : iprop(wsIs V P) $$ []
      · iunfold wrRO at Hro
        icases Hro with ⟨-, -, -, -, -, -, -, -, #Rflts, -⟩
        unfold wsIs
        isplitr
        · unfold wrRO
          iframe #
        isplitr
        · iexact recvc
        isplitr
        · iexact Hosp
        isplitr
        · iexact Hrsp
        isplitr
        · iexact Hctx
        isplitr
        · iexact Hretb
        isplitr
        · ipureintro; exact ⟨Hwsn, Hok, rfl⟩
        iexact Hsrd0
      ihave #Hls0 : iprop(lifeStart P 0) $$ []
      · unfold lifeStart; iexact Hps0
      ihave Hpsq : iprop(client.psQ P) $$ [Hpsa]
      · unfold client.psQ
        iexists _
        iframe Hpsa
        ipureintro
        refine ⟨GMap.lookup_insert _ _ _, fun j hj => ?_⟩
        rw [GMap.lookup_insert_ne _ _ (by omega)]
        exact GMap.lookup_empty j
      ihave #Hh20d : iprop(⌜P.γ.cpl = false⌝ ∨ monoListIdxOwn P.γh2 0 (P.rev - W64 1)) $$ []
      · iright; iexact Hh20
      ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
      · iPkgInit
      iunfold wgAdder at Had
      wp_apply wp_wgsWg_Add $$ [Had Htt] as ⟨Had, Hwd⟩
      · iframe
      icases client.wsElems_fresh V G n γs S U «$r0_ptr» _ $$ [Hels id] with ⟨%HUf, Hels, id⟩
      · iframe
      imod ghost_map_insert «$r0_ptr» () HUf $$ Hwsa with ⟨Hwsa, Hwsel⟩
      icases (ghostMapElem_halves G.γws «$r0_ptr» ()).1 $$ Hwsel with ⟨Hwsel1, Hwsel2⟩
      -- (D24) the lifetime's invariant, running
      imod inv_alloc lifeN ⊤ (lifeSt V G P L) $$ [Hγt2 Hwsel2] with #Hli
      · inext
        iunfold lifeSt
        ileft
        iframe
      ihave HlifeN : iprop(client.wsLife V G n P false) $$ [Hdnf2 Htk]
      · iapply client.wsLife_fresh V G n P L _ rfl
        unfold donecAt
        iframe Hdnf2 Hdnu Hli
        unfold ownTok; iexact Htk
      ihave Hc2p : cur2Pos P 0 0 $$ [Hcur2a]
      · unfold cur2Pos
        cases hc : cplOf P0
        · ileft; ipureintro; exact hc
        · iright
          iexists [P0.rev - W64 1], P0.rev - W64 1
          iframe Hcur2a Hh20
          ipureintro; simp
      ihave Hst0 : iprop(wsRun V P 0 P.rev [] P.rev) $$ [buf bufWaitStartTime retc Hrev1 Hocons
          Hoprod Hcura Hrcons2 Hc2p]
      · iapply client.wsRun_init V P slice.nil _
        iframe HP Hhi0 Hh20d
        (try rw [show P.γ.spsc = γsp from rfl])
        (try rw [show P.γ.cur = γcur from rfl])
        (try rw [show P.γr = γrr from rfl])
        (try rw [show P.rev = P0.rev from rfl])
        (try rw [show P.ws = «$r0_ptr» from rfl])
        (try rw [show P.retc = P0.retc from rfl])
        iframe
        isplitr
        · unfold sliceOwn
          isplitr
          · iapply ownSlice_nil
          iapply (ownSliceCap_nil (V := Loc))
        unfold retcRes
        (try rw [show P.γ.cur2 = γcur2 from rfl])
        iframe
        iframe #
      wp_apply wp_fork_tok_self $$ [closing HbL outc Hdnf1 Hdnb Hγt1 Hst0 Hx Hwd Hwsel1] as Htt
      · wp_apply wp_serveSub V G callSl P L 0 P.rev [] bl rc γrc
          $$ [closing HbL outc Hdnf1 Hdnb Hγt1 Hst0 Hx Hwd Hwsel1]
          as Htok
        · unfold wgDone
          iframe #
          iframe
          ipureintro; rfl
        first | iexact Htok | (iframe Htok; ipureintro; simp) | (iframe Htok; ipureintro; decide)
      wp_apply wp_slice_literal (V := Loc) [«$r0_ptr»]
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      iunfold sliceOwn at Hs
      icases Hs with ⟨Hs, Hscap⟩
      wp_apply wp_slice_append $$ [Hs Hscap Hsl1] as %s' ⟨Hs, Hscap, -⟩
      · iframe
      ihave %Hslen := ownSlice_len $$ Hs
      by_cases hl : S.l = []
      · have hlen1 : s'.len = W64 1 := by
          have h1 : (S.l ++ [«$r0_ptr»]).length = 1 := by rw [hl]; rfl
          have := Hslen.1; rw [h1] at this; word
        simp only [hlen1, _root_.decide_true]
        iunfold wrRO at Hro
        icases Hro with ⟨-, -, -, -, -, -, -, -, #Rflts, -⟩
        wp_take_receipt as Hrc
        wp_apply wp_toPB (wsF «$r0_ptr» go!"initReq") P0.key P0.ed P0.rev P0.pn P0.flt
          (DFrac.own (1 : Qp).half) P0.sr $$ [Hrev2] as %preq ⟨Hrev2, Hpsend⟩
        · iframe #; iframe
        imod mvcc.watchTokPool_take V.R.γ $$ Htoks Hrc with Hwt
        wp_apply HSend $$ %S.L %preq %(.create (createOf P0.key P0.ed P0.rev P0.pn P0.sr)) [Hstok Hpsend Hwt]
          as %err ⟨-, Hres⟩
        · iframe
          unfold v3rpc.watchUp
          iframe
          isplitr
          · ipureintro; simp [v3rpc.watchReqOk, createOf]
          dsimp only; iframe; simp only [createOf]; iapply client.startOk_read $$ Hsrd0
        ihave ⟨%L', %si, Hstok, %Hcase, Hupi⟩ : iprop(∃ (L' : List v3rpc.WatchReqM) (si : Option Nat),
            cliSendTok (Req := v3rpc.pbWatchRequest) γs L' ∗ ⌜client.addCase S L' si si⌝ ∗
            client.upAtOpt γs si (client.createOfP P)) $$ [Hres]
        · have hpend : S.pend = none := by
            cases h : S.pend with
            | none => rfl
            | some i => exact absurd hl (HgOk.2.2.2.2.2.2.2.2.2.1 i h).2.2
          ihave Hmk : iprop(∀ L2 : List v3rpc.WatchReqM,
              ⌜L2 = S.L ∨ L2 = S.L ++ [.create (createOf P0.key P0.ed P0.rev P0.pn P0.sr)]⌝ -∗
              cliSendTok (Req := v3rpc.pbWatchRequest) γs L2 -∗
              ∃ (L' : List v3rpc.WatchReqM) (si : Option Nat),
              cliSendTok (Req := v3rpc.pbWatchRequest) γs L' ∗ ⌜client.addCase S L' si si⌝ ∗
              client.upAtOpt γs si (client.createOfP P)) $$ []
          · iintro %L2 %HL2 Hst
            rcases HL2 with rfl | rfl
            · iexists S.L, none
              iframe
              isplitr
              · ipureintro
                exact Or.inr (Or.inl ⟨hl, rfl, rfl, rfl⟩)
              unfold client.upAtOpt; itrivial
            · ihave ⟨Hst, #Hlb⟩ := cliSendTok_lb $$ Hst
              iexists _, some S.L.length
              iframe
              isplitr
              · ipureintro
                exact Or.inr (Or.inr ⟨hl, ⟨_, rfl⟩, rfl, rfl⟩)
              ihave Hu := upLb_at (Req := v3rpc.pbWatchRequest) γs _ S.L.length
                (.create (createOf P0.key P0.ed P0.rev P0.pn P0.sr)) (by simp) $$ Hlb
              unfold client.upAtOpt v3rpc.upAtW
              iunfold upAt at Hu
              iexact Hu
          icases Hres with (⟨-, Htok⟩ | ⟨-, %L2, %HL2, Htok⟩)
          · iapply Hmk $$ %_ %(Or.inr rfl) Htok
          · iapply Hmk $$ %L2 %HL2 Htok
        cases err with
        | nil =>
          wp_auto
          wp_for_post
          iexists bo, γs, b, n, _, Dn, cd', rc, γrc, csm
          simp only [named]
          iframe closeErr cur backoff wc cancelSet Hrc Hrcb Hcws Hspec
          obtain ⟨Hg2, Hold2, Hnew2⟩ := client.addWs_ok (S := S) (U := U) (ws := «$r0_ptr»)
            (L' := L') (pend' := si) (si := si) HgOk Hwsn HUf Hcase
          ihave Hels := BigSepM.bigSepM_impl
              (Ψ := fun ws (_ : Unit) => client.wsElem V G n γs (S.addWs «$r0_ptr» L' si) ws) $$ Hels []
          · iintro !> %ws' %u %Hws' Hw'
            have Hws'' : U !! ws' = some u := Hws'
            have hne : ws' ≠ «$r0_ptr» := by
              intro e; subst e; rw [HUf] at Hws''; cases Hws''
            iapply (client.wsElem_mono V G n γs (S := S) (S' := S.addWs «$r0_ptr» L' si) ws' rfl
              (fun ph' h => Hold2 ws' ph' hne h)
              (fun X _ => client.create_or (by
                rcases Hcase with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
                · exact Or.inl h
                · exact Or.inl h
                · exact Or.inr h) X)) $$ Hw'
          ihave Hels := (BigSepM.bigSepM_insert (Φ := fun ws (_ : Unit) =>
              client.wsElem V G n γs (S.addWs «$r0_ptr» L' si) ws) (m := U) (i := «$r0_ptr») (x := ()) HUf).2 $$ [Hels id Hrprod Hhia Hh2a Hrev2 Hpsq Hupi HlifeN]
          · iframe Hels
            unfold client.wsElem
            iexists P, .queued si
            isplitr
            · ipureintro; exact ⟨rfl, Hnew2⟩
            iframe HP
            simp only [WPh.id]
            iframe id
            isplitl [Hrprod Hhia Hh2a Hrev2 Hpsq Hupi]
            · iapply client.queued_fresh V γs _ P si (regB0_ok V.pfx P Hok rfl)
              (try rw [show P.γr = γrr from rfl])
              (try rw [show P.γhi = γhi from rfl])
              (try rw [show P.rev = P0.rev from rfl])
              (try rw [show P.ws = «$r0_ptr» from rfl])
              iframe
              iframe #
              try itrivial
            simp only [client.noCancelOk]
            iframe
            
          unfold client.runCore wgAdder
          iexists S.addWs «$r0_ptr» L' si, GMap.insert «$r0_ptr» () U, rcv, mref, s', e
          have e1 : (S.addWs «$r0_ptr» L' si).Dm = S.Dm := rfl
          have e2 : (S.addWs «$r0_ptr» L' si).L = L' := rfl
          have e3 : (S.addWs «$r0_ptr» L' si).ansd = S.ansd := rfl
          have e4 : (S.addWs «$r0_ptr» L' si).regs = S.regs := rfl
          have e5 : (S.addWs «$r0_ptr» L' si).CS = S.CS := rfl
          have e6 : (S.addWs «$r0_ptr» L' si).M = S.M := rfl
          have e7 : (S.addWs «$r0_ptr» L' si).CL = S.CL := rfl
          have e8 : (S.addWs «$r0_ptr» L' si).l = S.l ++ [«$r0_ptr»] := rfl
          rw [e1, e2, e3, e4, e5, e6, e7, e8]
          iframe
          iframe #
          isplitl [Hs Hscap]
          · unfold sliceOwn; iframe
          ipureintro; exact ⟨Hrcv, Hg2⟩
        | ok ei =>
          wp_auto
          wp_apply wp_zapError as %f1 -
          wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
          isplitr
          · ipureintro; rfl
          iintro %fsl ⟨-, -⟩
          wp_auto
          wp_apply wp_Debug V.lg _ _ $$ []
          · iframe #; ipureintro; exact Hlg
          wp_for_post
          iexists bo, γs, b, n, _, Dn, cd', rc, γrc, csm
          simp only [named]
          iframe closeErr cur backoff wc cancelSet Hrc Hrcb Hcws Hspec
          obtain ⟨Hg2, Hold2, Hnew2⟩ := client.addWs_ok (S := S) (U := U) (ws := «$r0_ptr»)
            (L' := L') (pend' := si) (si := si) HgOk Hwsn HUf Hcase
          ihave Hels := BigSepM.bigSepM_impl
              (Ψ := fun ws (_ : Unit) => client.wsElem V G n γs (S.addWs «$r0_ptr» L' si) ws) $$ Hels []
          · iintro !> %ws' %u %Hws' Hw'
            have Hws'' : U !! ws' = some u := Hws'
            have hne : ws' ≠ «$r0_ptr» := by
              intro e; subst e; rw [HUf] at Hws''; cases Hws''
            iapply (client.wsElem_mono V G n γs (S := S) (S' := S.addWs «$r0_ptr» L' si) ws' rfl
              (fun ph' h => Hold2 ws' ph' hne h)
              (fun X _ => client.create_or (by
                rcases Hcase with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
                · exact Or.inl h
                · exact Or.inl h
                · exact Or.inr h) X)) $$ Hw'
          ihave Hels := (BigSepM.bigSepM_insert (Φ := fun ws (_ : Unit) =>
              client.wsElem V G n γs (S.addWs «$r0_ptr» L' si) ws) (m := U) (i := «$r0_ptr») (x := ()) HUf).2 $$ [Hels id Hrprod Hhia Hh2a Hrev2 Hpsq Hupi HlifeN]
          · iframe Hels
            unfold client.wsElem
            iexists P, .queued si
            isplitr
            · ipureintro; exact ⟨rfl, Hnew2⟩
            iframe HP
            simp only [WPh.id]
            iframe id
            isplitl [Hrprod Hhia Hh2a Hrev2 Hpsq Hupi]
            · iapply client.queued_fresh V γs _ P si (regB0_ok V.pfx P Hok rfl)
              (try rw [show P.γr = γrr from rfl])
              (try rw [show P.γhi = γhi from rfl])
              (try rw [show P.rev = P0.rev from rfl])
              (try rw [show P.ws = «$r0_ptr» from rfl])
              iframe
              iframe #
              try itrivial
            simp only [client.noCancelOk]
            iframe
            
          unfold client.runCore wgAdder
          iexists S.addWs «$r0_ptr» L' si, GMap.insert «$r0_ptr» () U, rcv, mref, s', e
          have e1 : (S.addWs «$r0_ptr» L' si).Dm = S.Dm := rfl
          have e2 : (S.addWs «$r0_ptr» L' si).L = L' := rfl
          have e3 : (S.addWs «$r0_ptr» L' si).ansd = S.ansd := rfl
          have e4 : (S.addWs «$r0_ptr» L' si).regs = S.regs := rfl
          have e5 : (S.addWs «$r0_ptr» L' si).CS = S.CS := rfl
          have e6 : (S.addWs «$r0_ptr» L' si).M = S.M := rfl
          have e7 : (S.addWs «$r0_ptr» L' si).CL = S.CL := rfl
          have e8 : (S.addWs «$r0_ptr» L' si).l = S.l ++ [«$r0_ptr»] := rfl
          rw [e1, e2, e3, e4, e5, e6, e7, e8]
          iframe
          iframe #
          isplitl [Hs Hscap]
          · unfold sliceOwn; iframe
          ipureintro; exact ⟨Hrcv, Hg2⟩
      · have hlen1 : ¬ (s'.len = W64 1) := by
          intro h
          have : (S.l ++ [«$r0_ptr»]).length = 1 := by
            rw [Hslen.1, h]; rfl
          simp at this; exact hl this
        simp only [hlen1, decide_false]
        wp_auto
        wp_for_post
        iexists bo, γs, b, n, _, Dn, cd', rc, γrc, csm
        simp only [named]
        iframe closeErr cur backoff wc cancelSet Hrc Hrcb Hcws Hspec
        obtain ⟨Hg2, Hold2, Hnew2⟩ := client.addWs_ok (S := S) (U := U) (ws := «$r0_ptr»)
          (L' := S.L) (pend' := S.pend) (si := none) HgOk Hwsn HUf (Or.inl ⟨hl, rfl, rfl, rfl⟩)
        ihave Hels := BigSepM.bigSepM_impl
            (Ψ := fun ws (_ : Unit) => client.wsElem V G n γs (S.addWs «$r0_ptr» S.L S.pend) ws) $$ Hels []
        · iintro !> %ws' %u %Hws' Hw'
          have Hws'' : U !! ws' = some u := Hws'
          have hne : ws' ≠ «$r0_ptr» := by
            intro e; subst e; rw [HUf] at Hws''; cases Hws''
          iapply (client.wsElem_mono V G n γs (S := S) (S' := S.addWs «$r0_ptr» S.L S.pend) ws' rfl
            (fun ph' h => Hold2 ws' ph' hne h) (fun _ _ _ hi => hi)) $$ Hw'
        ihave Hels := (BigSepM.bigSepM_insert (Φ := fun ws (_ : Unit) =>
            client.wsElem V G n γs (S.addWs «$r0_ptr» S.L S.pend) ws) (m := U) (i := «$r0_ptr») (x := ()) HUf).2 $$ [Hels id Hrprod Hhia Hh2a Hrev2 Hpsq HlifeN]
        · iframe Hels
          unfold client.wsElem
          iexists P, .queued none
          isplitr
          · ipureintro; exact ⟨rfl, Hnew2⟩
          iframe HP
          simp only [WPh.id]
          iframe id
          isplitl [Hrprod Hhia Hh2a Hrev2 Hpsq]
          · iapply client.queued_fresh V γs _ P none (regB0_ok V.pfx P Hok rfl)
            (try rw [show P.γr = γrr from rfl])
            (try rw [show P.γhi = γhi from rfl])
            (try rw [show P.rev = P0.rev from rfl])
            (try rw [show P.ws = «$r0_ptr» from rfl])
            iframe
            iframe #
            unfold client.upAtOpt; itrivial
          simp only [client.noCancelOk]
          iframe
          
        unfold client.runCore wgAdder
        iexists S.addWs «$r0_ptr» S.L S.pend, GMap.insert «$r0_ptr» () U, rcv, mref, s', e
        have e1 : (S.addWs «$r0_ptr» S.L S.pend).Dm = S.Dm := rfl
        have e2 : (S.addWs «$r0_ptr» S.L S.pend).L = S.L := rfl
        have e3 : (S.addWs «$r0_ptr» S.L S.pend).ansd = S.ansd := rfl
        have e4 : (S.addWs «$r0_ptr» S.L S.pend).regs = S.regs := rfl
        have e5 : (S.addWs «$r0_ptr» S.L S.pend).CS = S.CS := rfl
        have e6 : (S.addWs «$r0_ptr» S.L S.pend).M = S.M := rfl
        have e7 : (S.addWs «$r0_ptr» S.L S.pend).CL = S.CL := rfl
        have e8 : (S.addWs «$r0_ptr» S.L S.pend).l = S.l ++ [«$r0_ptr»] := rfl
        rw [e1, e2, e3, e4, e5, e6, e7, e8]
        iframe
        iframe #
        isplitl [Hs Hscap]
        · unfold sliceOwn; iframe
        ipureintro; exact ⟨Hrcv, Hg2⟩
    -- respc
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, G.respc, G.γr.chanName
      isplit
      · ipureintro; rfl
      isplit
      · ihave #H := Hrspsc
        unfold isSspsc
        icases H with ⟨$, -⟩
      iunfold client.runCore at Hcore
      icases Hcore with ⟨%S, %U, %rcv, %mref, %s, %e, Hclm, Hcsm, Hsub, Hm, Hres, Hs, HcF, #He,
        Hstok, Hrcons, %Hrcv, Hepst, #HDlb, %HgOk, Hans, Hids, #Hinfo, Hwsa, Hels, Had, Htt, Hdn, Hgen⟩
      iapply sspsc_rcv_au G.γr G.respc _ _ rcv _ $$ Hrspsc [$Hlc1 $Hlc2] Hrcons
      inext
      iintro %p %ok Hrecv
      cases ok
      · simp only [Bool.false_eq_true, ↓reduceIte]
        icases Hrecv with ⟨HF, -⟩
        iexfalso; iexact HF
      simp only [↓reduceIte]
      icases Hrecv with ⟨Hel, Hrcons⟩
      -- (D24) a response of the current epoch's stream
      icases client.respcE_at V G γs b rcv.length p (by omega) $$ [Hepst Hel] with ⟨Hepst, Hel⟩
      · iframe
      have hj : rcv.length - b = S.Dm.length := by omega
      rw [hj]
      clear hj
      iunfold respcElem at Hel
      icases Hel with ⟨%m, %Lm, Hm1, HDn, #HLlb, %HLlen⟩
      iunfold v3rpc.downLbW at HDlb HLlb
      ihave %Hcmp := mono_list_lb_valid _ _ _ $$ HDlb HLlb
      have HLm : Lm = S.Dm := client.prefix_snoc_eq Hcmp (by simp at HLlen; omega)
      subst HLm
      clear HLlen Hcmp
      irevert HDn
      rw [show ((S.Dm.length : Int)).toNat = S.Dm.length by simp]
      iintro HDn
      ihave Hwd := HDn
      iunfold v3rpc.watchDn at Hwd
      icases Hwd with ⟨%Hcm, Hcase⟩
      iunfold v3rpc.watchRespRecv at Hm1
      icases Hm1 with ⟨%Hpn, %h, %sl, %ps, Hhdr, Hho, Hwid, Hcr, Hca, Hcomp, Hcrs, Hfr, Hev, #Hps,
        %Hpslen, #Hevs⟩
      wp_auto
      icases Hcase with (⟨%Hsrc, Hctrl, #Hcaf⟩ | #Hmvcc)
      · iunfold v3rpc.ctrlOk at Hctrl
        icases Hctrl with ⟨%i, %req, %γo, %γa, #Haux, #Hup, %Hcans, Hcw, Hat⟩
        cases req with
        | create c =>
          obtain ⟨hs0, hev0, hcomp0, hfr0, hcr0, hcase⟩ : m.src = none ∧ m.evs = [] ∧
              m.compactRev = W64 0 ∧ m.fragment = false ∧ m.created = true ∧
              ((m.canceled = true ∧ m.watchId = W64 (-1)) ∨
               (m.canceled = false ∧ 0 ≤ sint.Z c.startRev ∧
                 (c.watchId ≠ W64 0 → m.watchId = c.watchId))) := by
            simp only [v3rpc.ctrlAnswers] at Hcans; exact Hcans
          icases client.sendTok_lookup γs S.L i (.create c) $$ [Hstok Hup] with ⟨Hstok, %HLi⟩
          · iframe; iframe #
          ihave Hfr' : iprop(⌜i ∉ S.ansd⌝ ∗ ([∗list] j ∈ S.ansd, client.ansH γs j) ∗ v3rpc.ansTok γa i)
            $$ [Hans Hat]
          · iapply client.ans_fresh
            iframe
            iframe #
          icases Hfr' with ⟨%Hia, Hans, Hat⟩
          have hpend : S.pend = some i := (HgOk.2.2.2.2.2.2.2.1 i c HLi).resolve_left Hia
          have hlne : S.l ≠ [] := (HgOk.2.2.2.2.2.2.2.2.2.1 i hpend).2.2
          obtain ⟨h0, hh0⟩ : ∃ h0, S.l.head? = some h0 := by
            cases hl : S.l with
            | nil => exact absurd hl hlne
            | cons x xs => exact ⟨x, rfl⟩
          -- the response's header and events
          iunfold v3rpc.hdrOwn at Hho
          icases Hho with ⟨%Hhn, Hh1, Hh2, Hhrev, Hh4, Hh5⟩
          ipersist Hhrev
          ihave #Hha : iprop(hdrAt h m.hdr.revision) $$ []
          · unfold hdrAt; iright; iframe Hhrev; ipureintro; exact Hhn
          ihave ⟨%kvs, %Hkvl, #Hea, -⟩ := client.evs_eventsAt sl ps m.evs Hpslen $$ [Hps Hevs]
          · iframe #
          ihave #Hea0 : iprop(eventsAt sl ([] : List EvModel)) $$ []
          · have : List.zipWith client.evModelOf m.evs kvs = [] := by rw [hev0]; simp
            rw [← this]; iexact Hea
          -- the new id's token and watcher (unless the create was refused)
          ihave Hidp : iprop(⌜m.canceled = false → m.watchId ∉ S.regs⌝ ∗
              ([∗list] X ∈ S.regs, client.idH γs X) ∗
              ([∗list] X ∈ (if m.canceled then [] else [m.watchId]), client.idH γs X) ∗
              □ (⌜m.canceled = false⌝ -∗ ∃ (w : Loc) (rg : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat),
                ⌜v3rpc.createRangeOk c m.watchId rg⌝ ∗ mvcc.watcherIs V.R.γ w rg fcs lo ∗
                fcs ↦*□ ([] : List GoFunc) ∗
                (∃ γw : mvcc.WatcherNames, mvcc.watcherMeta V.R.γ w γw ∗ ⌜γw.sr = c.sr⌝) ∗
                ∃ (γo : mvcc.WsStreamNames) (γa : GName), streamAuxIs γs (v3rpc.auxOf γo γa) ∗
                  mvcc.idAssigned γo m.watchId w)) $$ [Hcw Hids]
          · cases hcan : m.canceled
            · irevert Hcw
              simp only [v3rpc.ctrlWatcher, hcan, Bool.false_eq_true, ↓reduceIte]
              iintro ⟨%w, %rg, %fcs, %lo, %Hcrg, #Hwi, #Hfcs, #Hws, #Hias, Hidt, -⟩
              ihave ⟨%HXr, Hids, Hidt⟩ := client.id_fresh γs S.regs m.watchId γo γa $$ [Hids Hidt]
              · iframe; iframe #
              isplitr
              · ipureintro; intro _; exact HXr
              iframe Hids
              isplitl [Hidt]
              · iapply BigSepL.bigSepL_singleton.2
                unfold client.idH
                iexists γo, γa
                iframe; iframe #
              imodintro
              iintro %-
              iexists w, rg, fcs, lo
              iframe #
              ipureintro; exact Hcrg
            · iframe Hids
              isplitr
              · ipureintro; intro h'; cases h'
              isplitr
              · simp only [↓reduceIte]; iapply BigSepL.bigSepL_nil.2; itrivial
              imodintro
              iintro %h'; cases h'
          icases Hidp with ⟨%HXf, Hids, Hidn, #Hwf⟩
          ihave #Hsf2 := Hsf
          iunfold watchSrvFacts at Hsf2
          icases Hsf2 with ⟨-, #Hcf⟩
          ihave ⟨%hMf, Hels⟩ : iprop(⌜S.M !! m.watchId = none ∨
              (m.watchId ∈ S.regs ∧ m.watchId ≠ W64 (-1))⌝ ∗
              [∗map] ws ↦ _u ∈ U, client.wsElem V G n γs S ws) $$ [Hels]
          · cases hMX : S.M !! m.watchId with
            | none => iframe; ipureintro; left; rfl
            | some ws1 =>
              icases client.M_entry_facts V G n γs HgOk hMX $$ Hels with ⟨%Hf, Hels⟩
              iframe; ipureintro; right; exact Hf
          rw [hcr0]
          wp_auto
          iunfold sliceOwn at Hs
          icases Hs with ⟨Hs, Hscap⟩
          ihave %Hsll := ownSlice_len $$ Hs
          have hlen0 : S.l.length ≠ 0 := fun h => hlne (List.length_eq_zero_iff.1 h)
          have hl0 : S.l[0]? = some h0 := by
            cases hl : S.l with
            | nil => exact absurd hl hlne
            | cons x xs => rw [hl] at hh0; simpa using hh0
          wp_bind (If _ _ _)
          iapply (wp_wand_r (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
              ∃ (S1 : client.RunSt) (e' : GoInterface),
              ⌜client.gOk S1 U ∧ S1.pend = none ∧ S1.L = S.L ∧ S1.Dm = S.Dm ++ [m] ∧
                S1.CL = S.CL ∧ S1.CS = S.CS⌝ ∗
              wgsF G.wgs go!"substreams" ↦ mref ∗ ownMap mref (DFrac.own 1) S1.M ∗
              wgsF G.wgs go!"resuming" ↦ s ∗ s ↦* S1.l ∗ ownSliceCap Loc s (DFrac.own 1) ∗
              wgsF G.wgs go!"closeErr" ↦ e' ∗ statusErrOk e' ∗
              ([∗list] j ∈ S1.ansd, client.ansH γs j) ∗ ([∗list] X ∈ S1.regs, client.idH γs X) ∗
              ([∗map] ws ↦ _u ∈ U, client.wsElem V G n γs S1 ws) ∗ monoNatAuthOwn G.γend 1 n)))
          isplitl [pbresp Hsub Hm Hres Hs Hscap HcF Hans Hids Hidn Hels Hat Hwid Hca Hcrs Hhdr Hcr Hcomp Hfr Hev
            Hgen]
          · have hpos : 0 < sint.Z s.len := by
              have h1 := Hsll.1; have h2 : 0 < S.l.length := Nat.pos_of_ne_zero hlen0; word
            have hlen : s.len ≠ W64 0 := by intro e0; rw [e0] at hpos; simp at hpos
            have Hbnd : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z s.len := ⟨by simp, by simpa using hpos⟩
            simp only [hlen, decide_false, Bool.not_false]
            wp_auto
            rw [ite_eq_left Hbnd]
            wp_apply wp_load_slice_index s (sint.Z (W64 0)) S.l (DFrac.own 1) h0 (by simp) $$ [Hs] as Hs
            · iframe; ipureintro; simpa using hl0
            by_cases hn0 : h0 = null
            · subst hn0
              simp only [_root_.decide_true, Bool.not_true]
              wp_auto
              obtain ⟨Hg1, Hold1, -⟩ := client.answer_ok (U := U) (reg := false) HgOk hpend hh0 hs0
                hcr0 rfl HXf (fun hc => by rcases hcase with ⟨-, h⟩ | ⟨h, -⟩ <;> simp_all) (fun h => by cases h) (fun h => by cases h) (fun h => absurd rfl h)
              isplitr
              · first | itrivial | (ipureintro; rfl)
              iexists S.answer m i m.watchId null false, e
              have e1 : (S.answer m i m.watchId null false).M = S.M := by simp [client.RunSt.answer]
              have e2 : (S.answer m i m.watchId null false).l = S.l := by simp [client.RunSt.answer]
              have e3 : (S.answer m i m.watchId null false).ansd = S.ansd ++ [i] := rfl
              have e4 : (S.answer m i m.watchId null false).regs =
                  (if m.canceled then S.regs else S.regs ++ [m.watchId]) := rfl
              rw [e1, e2, e3, e4]
              isplitr
              · ipureintro; exact ⟨Hg1, rfl, rfl, rfl, rfl, rfl⟩
              iframe
              iframe #
              isplitl [Hat]
              · iapply BigSepL.bigSepL_singleton.2
                unfold client.ansH
                iexists γo, γa
                iframe; iframe #
              isplitl [Hids Hidn]
              · iapply client.regs_join; iframe
              ihave Hels := BigSepM.bigSepM_impl (Ψ := fun ws (_ : Unit) =>
                  client.wsElem V G n γs (S.answer m i m.watchId null false) ws) $$ Hels []
              · iintro !> %ws' %u %Hws' Hw'
                have Hws'' : U !! ws' = some u := Hws'
                cases u
                have hne : ws' ≠ null := fun e => by
                  subst e; rw [HgOk.2.2.2.2.2.1] at Hws''; cases Hws''
                iapply (client.wsElem_mono' V G n γs (S := S) (S' := S.answer m i m.watchId null false) ws'
                  (fun P ph _ => client.wsRest_snoc_ctrl V γs S.Dm m P ph hs0)
                  (fun ph h => Hold1 ws' ph hne Hws'' h) rfl) $$ Hw'
              iexact Hels
            simp only [hn0, decide_false, Bool.not_false]
            wp_auto
            have hmem0 : h0 ∈ S.l := List.mem_of_getElem? hl0
            have hU0 : U !! h0 = some () := HgOk.2.2.1 h0 hmem0 hn0
            icases (BigSepM.bigSepM_delete hU0).1 $$ Hels with ⟨Hw, Hels⟩
            iunfold client.wsElem at Hw
            icases Hw with ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest, #Hnc, Hlife⟩
            ihave %HPq : ⌜wsReqOk V.pfx P ∧ P.γ.cpl = cplOf P⌝ $$ []
            · ihave #HP' := HP
              iunfold wsIs at HP'
              icases HP' with ⟨-, -, -, -, -, -, %Hq, -⟩
              ipureintro; exact ⟨Hq.2.1, Hq.2.2⟩
            subst HPws
            obtain ⟨si, rfl, hsi⟩ : ∃ si, ph = .queued si ∧ si = some i := by
              cases ph with
              | queued si =>
                refine ⟨si, rfl, ?_⟩
                cases si with
                | none => have := Hph.2.2.2.2 rfl hh0; rw [hpend] at this; cases this
                | some i' => have := (Hph.2.2.2.1 i' rfl).1; rw [hpend] at this; cases this; rfl
              | reg X => exact absurd hmem0 Hph.2.1
              | closedRun X => exact absurd hmem0 Hph.2.1
              | orphan => exact absurd hmem0 Hph.2.1
              | closed => exact absurd hmem0 Hph.2.1
            subst hsi
            iunfold client.wsRest at Hrest
            icases Hrest with (⟨%B, %sent, %C, %C2, %HB, #HsoB, Hprod, Hauth, Hauth2, %HCs, Hrv, Hpsq, #Hupi⟩ |
              ⟨#HxD, %B, %sent, %C, %C2, %q, %HB, #HsoB, Hprod, Hauth, Hauth2, Hrv, #Hupi⟩)
            rotate_left
            · -- (D24) a substream stopped for good, re-created after a reconnection: its dispatch fails
              ihave #Hu1 := Hup
              iunfold client.upAtOpt at Hupi
              iunfold v3rpc.upAtW at Hu1 Hupi
              ihave %Hceq := mono_list_idx_agree _ _ _ _ $$ Hu1 Hupi
              have hc : c = client.createOfB P B := by injection Hceq
              subst hc
              by_cases hfail : addFails m.watchId m.canceled m.cancelReason
              · wp_apply wp_addSub V G.wgs p P.ws m.watchId m.canceled m.cancelReason (DFrac.own 1)
                  (DFrac.own 1) (W64 (-1)) mref S.M e $$ [Hwid Hca Hcrs Hid Hsub Hm HcF Hprod]
                  as ⟨Hwid, Hca, Hcrs, Hsub, Hpost⟩
                · iframe; iframe #
                  iintro %-
                  unfold recvcCloser
                  iexists P, sent
                  iframe; iframe #
                  ipureintro; rfl
                irevert Hpost
                rw [show decide (addFails m.watchId m.canceled m.cancelReason) = true from
                  decide_eq_true hfail]
                simp only [↓reduceIte]
                iintro ⟨Hid, Hm, %e', HcF, #He'⟩
                have hXm : m.watchId = W64 (-1) := by
                  rcases hfail with h | ⟨hca, -⟩
                  · exact h
                  · rcases hcase with ⟨-, h⟩ | ⟨h, -⟩
                    · exact h
                    · rw [hca] at h; cases h
                have hMn : S.M !! m.watchId = none := hMf.resolve_right (fun h => h.2 hXm)
                ihave Hrf : iprop(respFields p (DFrac.own 1) m h sl) $$ [Hhdr Hwid Hcr Hca Hcomp Hcrs Hfr Hev]
                · unfold respFields
                  rw [hcr0]
                  iframe
                  ipureintro; exact Hhn
                have hnb : ¬ client.isBroadcast m := fun h => by
                  obtain ⟨-, -, h3, -⟩ := h; rw [hcr0] at h3; cases h3
                wp_apply wp_dispatch V G.wgs p (DFrac.own 1) m h sl [] mref S.M (DFrac.own 1)
                  (DFrac.own 1) (fun _ => client.dummyWsPrm G G.γr) (fun _ => [])
                  (fun _ => client.dummyDn G) G.γend n
                  $$ [Hrf Hsub Hm Hgen] as %b ⟨Hrf, Hsub, Hm, Hgen, Hpost⟩
                · iframe
                  iframe #
                  isplitr
                  · ipureintro; simp [hev0]
                  isplitr
                  · iintro %-; itrivial
                  rw [if_neg (by simpa using hnb), hMn]
                  itrivial
                rw [ite_eq_left Hbnd]
                wp_apply wp_store_slice_index s (sint.Z (W64 0)) S.l null $$ [Hs] as Hs
                · iframe; ipureintro; exact ⟨by simp, by have := Hsll.1; word⟩
                obtain ⟨Hg1, Hold1, Hnew1⟩ := client.answer_ok (U := U) (reg := false) HgOk hpend hh0 hs0
                  hcr0 rfl HXf (fun hc => by rcases hcase with ⟨-, h⟩ | ⟨h, -⟩ <;> simp_all) (fun h => by cases h) (fun h => by cases h) (fun _ => Hph)
                isplitr
                · first | itrivial | (ipureintro; rfl)
                iexists S.answer m i m.watchId P.ws false, e'
                have e1 : (S.answer m i m.watchId P.ws false).M = S.M := by simp [client.RunSt.answer]
                have e2 : (S.answer m i m.watchId P.ws false).l = S.l.set (sint.Z (W64 0)).toNat null := by
                  simp [client.RunSt.answer, hn0]
                have e3 : (S.answer m i m.watchId P.ws false).ansd = S.ansd ++ [i] := rfl
                have e4 : (S.answer m i m.watchId P.ws false).regs =
                    (if m.canceled then S.regs else S.regs ++ [m.watchId]) := rfl
                rw [e1, e2, e3, e4]
                isplitr
                · ipureintro; exact ⟨Hg1, rfl, rfl, rfl, rfl, rfl⟩
                iframe
                iframe #
                isplitl [Hat]
                · iapply BigSepL.bigSepL_singleton.2
                  unfold client.ansH
                  iexists γo, γa
                  iframe; iframe #
                isplitl [Hids Hidn]
                · iapply client.regs_join; iframe
                ihave Hels := BigSepM.bigSepM_impl (Ψ := fun ws (_ : Unit) =>
                    client.wsElem V G n γs (S.answer m i m.watchId P.ws false) ws) $$ Hels []
                · iintro !> %ws' %u %Hws' Hw'
                  have Hws'' : (GMap.delete P.ws U) !! ws' = some u := Hws'
                  have hne : ws' ≠ P.ws := by
                    intro e; subst e; rw [GMap.lookup_delete] at Hws''; cases Hws''
                  rw [GMap.lookup_delete_ne _ (Ne.symm hne)] at Hws''
                  cases u
                  iapply (client.wsElem_mono' V G n γs (S := S) (S' := S.answer m i m.watchId P.ws false) ws'
                    (fun P ph _ => client.wsRest_snoc_ctrl V γs S.Dm m P ph hs0)
                    (fun ph h => Hold1 ws' ph hne Hws'' h) rfl) $$ Hw'
                iapply (BigSepM.bigSepM_delete (Φ := fun ws (_ : Unit) =>
                  client.wsElem V G n γs (S.answer m i m.watchId P.ws false) ws) (m := U) (i := P.ws) (x := ()) hU0).2
                iframe Hels
                unfold client.wsElem
                iexists P, .orphan
                isplitr
                · ipureintro; exact ⟨rfl, by simpa using Hnew1 hn0⟩
                iframe HP
                simp only [WPh.id, client.wsRest, client.noCancelOk, WPh.isOrphan]
                iframe Hid
                isplitr
                · itrivial
                isplitr
                · itrivial
                iapply client.wsLife_orphan $$ Hlife
              · have hca : m.canceled = false := by
                  cases hcan : m.canceled
                  · rfl
                  · exfalso; apply hfail
                    rcases hcase with ⟨-, h⟩ | ⟨h, -⟩
                    · left; exact h
                    · rw [hcan] at h; cases h
                have hXn : m.watchId ≠ W64 (-1) := fun h => hfail (Or.inl h)
                have hXr : m.watchId ∉ S.regs := HXf hca
                have hMn : S.M !! m.watchId = none := hMf.resolve_right (fun h => hXr h.1)
                wp_apply wp_addSub V G.wgs p P.ws m.watchId m.canceled m.cancelReason (DFrac.own 1)
                  (DFrac.own 1) (W64 (-1)) mref S.M e $$ [Hwid Hca Hcrs Hid Hsub Hm HcF]
                  as ⟨Hwid, Hca, Hcrs, Hsub, Hpost⟩
                · iframe; iframe #
                  iintro %h'; exact absurd h' hfail
                irevert Hpost
                rw [show decide (addFails m.watchId m.canceled m.cancelReason) = false from
                  decide_eq_false hfail]
                simp only [Bool.false_eq_true, ↓reduceIte]
                iintro ⟨Hid, Hm, HcF⟩
                -- the watcher the server registered
                ihave ⟨%w, %rg, %fcs, %lo, %Hcrg, #Hwi, #Hfcs, #Hws, %γo', %γa', #Hax', #Hias⟩ := Hwf $$ %hca
                ihave #Hwi' := Hwi
                iunfold mvcc.watcherIs at Hwi'
                icases Hwi' with ⟨%γw0, %C0, -, #Hwfix, -⟩
                ihave %Hfresh := client.evsSoFar_fresh m.watchId w rg fcs HgOk hXr hXn Hcrg.2.2.1
                  $$ [Hinfo Hwfix]
                · iframe #
                ihave Hrf : iprop(respFields p (DFrac.own 1) m h sl) $$ [Hhdr Hwid Hcr Hca Hcomp Hcrs Hfr Hev]
                · unfold respFields
                  rw [hcr0]
                  iframe
                  ipureintro; exact Hhn
                have hnb : ¬ client.isBroadcast m := fun h => by
                  obtain ⟨-, -, h3, -⟩ := h; rw [hcr0] at h3; cases h3
                simp only [WPh.isOrphan]
                icases client.wsLife_cap V G n P $$ Hlife with ⟨%d, Hdc, Hback⟩
                wp_apply wp_dispatch V G.wgs p (DFrac.own 1) m h sl [] mref (GMap.insert m.watchId P.ws S.M)
                  (DFrac.own 1) (DFrac.own 1) (fun _ => P) (fun _ => sent) (fun _ => d) G.γend n
                  $$ [Hrf Hsub Hm Hgen Hprod Hdc] as %b ⟨Hrf, Hsub, Hm, Hgen, Hpost⟩
                · iframe
                  iframe #
                  isplitr
                  · ipureintro; simp [hev0]
                  isplitr
                  · iintro %-; itrivial
                  rw [if_neg (by simpa using hnb), GMap.lookup_insert]
                  isplitr
                  · ipureintro; rfl
                  unfold sendCap
                  iframe
                  iframe #
                  iintro %wr -
                  unfold client.recvElem
                  iright; iexact HxD
                irevert Hpost
                rw [if_neg (show ¬ (decide (client.isBroadcast m) = true) by
                  simp only [decide_eq_true_eq]; exact hnb)]
                iintro ⟨%wr, Hpost⟩
                ihave #Hsnap : iprop(client.regSnap γs S.Dm w) $$ []
                · irevert Hcaf
                  unfold v3rpc.createdAfter
                  rw [hcr0, hca]
                  simp only [Bool.not_false, Bool.and_self, ↓reduceIte]
                  iintro #Hcaf
                  icases Hcaf with ⟨%γo2, %γa2, %w2, %l0, %l, %L, %n, #Hax2, #Hia2, #Hl0, #Hl, #HL,
                    #Hrn, %Hn, %Hpp⟩
                  ihave %He : iprop(⌜v3rpc.auxOf γo' γa' = v3rpc.auxOf γo2 γa2⌝) $$ []
                  · iapply streamAuxIs_agree
                    isplit
                    · iexact Hax'
                    · iexact Hax2
                  obtain ⟨rfl, rfl⟩ := v3rpc.auxOf_inj He
                  ihave %Hw := mvcc.idAssigned_agree γo' m.watchId w w2 $$ [Hias Hia2]
                  · isplit
                    · iexact Hias
                    · iexact Hia2
                  subst Hw
                  ihave #HL' := HL
                  iunfold v3rpc.downLbW at HL'
                  ihave %HcL := mono_list_lb_valid _ _ _ $$ HDlb HL'
                  have hLD : L = S.Dm := by
                    have hl : L.length = S.Dm.length := by rw [Hpp.2.1]
                    rcases HcL with h' | h'
                    · exact (h'.eq_of_length hl.symm).symm
                    · exact h'.eq_of_length hl
                  unfold client.regSnap
                  iexists γo', γa', l, L, n
                  iframe Hax' Hl Hrn
                  ipureintro
                  exact ⟨Nat.le_trans Hn Hpp.1.length_le, by rw [hLD]; exact List.prefix_refl _, Hpp.2.2⟩
                ihave #Hrg : iprop(client.regFacts V γs S.Dm P B m.watchId w rg fcs lo) $$ []
                · unfold client.regFacts
                  iframe Hwi Hfcs Hsnap
                  isplitr
                  · ipureintro; exact Hcrg
                  isplitr
                  · icases Hws with ⟨%γw', #Hm', %Hsr'⟩
                    iexists γw'; iframe Hm'; ipureintro; exact Hsr'
                  iexists γo', γa'
                  iframe Hax' Hias
                icases client.reg_post_dead V γs P B HB S.Dm m m.watchId w rg fcs lo sent C C2 b wr
                  d G.γend n $$ [HxD Hrg HsoB Hauth Hauth2 Hpost] with ⟨Hrest, Hdc⟩
                · iframe; iframe #
                rw [ite_eq_left Hbnd]
                wp_apply wp_store_slice_index s (sint.Z (W64 0)) S.l null $$ [Hs] as Hs
                · iframe; ipureintro; exact ⟨by simp, by have := Hsll.1; word⟩
                obtain ⟨Hg1, Hold1, Hnew1⟩ := client.answer_ok (U := U) (reg := true) HgOk hpend hh0 hs0
                  hcr0 rfl HXf (fun hc => by rcases hcase with ⟨-, h⟩ | ⟨h, -⟩ <;> simp_all) (fun _ => hMn) (fun _ => ⟨hn0, hXn, hca⟩) (fun _ => Hph)
                isplitr
                · first | itrivial | (ipureintro; rfl)
                iexists S.answer m i m.watchId P.ws true, e
                have e1 : (S.answer m i m.watchId P.ws true).M = GMap.insert m.watchId P.ws S.M := by simp [client.RunSt.answer]
                have e2 : (S.answer m i m.watchId P.ws true).l = S.l.set (sint.Z (W64 0)).toNat null := by
                  simp [client.RunSt.answer, hn0]
                have e3 : (S.answer m i m.watchId P.ws true).ansd = S.ansd ++ [i] := rfl
                have e4 : (S.answer m i m.watchId P.ws true).regs =
                    (if m.canceled then S.regs else S.regs ++ [m.watchId]) := rfl
                rw [e1, e2, e3, e4]
                isplitr
                · ipureintro; exact ⟨Hg1, rfl, rfl, rfl, rfl, rfl⟩
                iframe
                iframe #
                isplitl [Hat]
                · iapply BigSepL.bigSepL_singleton.2
                  unfold client.ansH
                  iexists γo, γa
                  iframe; iframe #
                isplitl [Hids Hidn]
                · iapply client.regs_join; iframe
                ihave Hels := BigSepM.bigSepM_impl (Ψ := fun ws (_ : Unit) =>
                    client.wsElem V G n γs (S.answer m i m.watchId P.ws true) ws) $$ Hels []
                · iintro !> %ws' %u %Hws' Hw'
                  have Hws'' : (GMap.delete P.ws U) !! ws' = some u := Hws'
                  have hne : ws' ≠ P.ws := by
                    intro e; subst e; rw [GMap.lookup_delete] at Hws''; cases Hws''
                  rw [GMap.lookup_delete_ne _ (Ne.symm hne)] at Hws''
                  cases u
                  iapply (client.wsElem_mono' V G n γs (S := S) (S' := S.answer m i m.watchId P.ws true) ws'
                    (fun P ph _ => client.wsRest_snoc_ctrl V γs S.Dm m P ph hs0)
                    (fun ph h => Hold1 ws' ph hne Hws'' h) rfl) $$ Hw'
                iapply (BigSepM.bigSepM_delete (Φ := fun ws (_ : Unit) =>
                  client.wsElem V G n γs (S.answer m i m.watchId P.ws true) ws) (m := U) (i := P.ws) (x := ()) hU0).2
                iframe Hels
                unfold client.wsElem
                iexists P, .reg m.watchId
                isplitr
                · ipureintro; exact ⟨rfl, by simpa using Hnew1 hn0⟩
                iframe HP
                simp only [WPh.id]
                iframe Hid
                rw [show (S.answer m i m.watchId P.ws true).Dm = S.Dm ++ [m] from rfl]
                iframe Hrest
                -- a fresh id: no cancel request for it was sent (a cancel's id is registered)
                isplitr
                · unfold client.noCancelOk
                  ileft; ipureintro
                  intro j hj
                  exact hXr (HgOk.2.2.2.2.2.2.2.2.1 j m.watchId hj)
                iunfold dnCap at Hdc
                icases Hdc with ⟨Hdc, -⟩
                simp only [WPh.isOrphan]
                iapply Hback $$ Hdc

            ihave #Hu1 := Hup
            iunfold client.upAtOpt at Hupi
            iunfold v3rpc.upAtW at Hu1 Hupi
            ihave %Hceq := mono_list_idx_agree _ _ _ _ $$ Hu1 Hupi
            have hc : c = client.createOfB P B := by injection Hceq
            subst hc
            by_cases hfail : addFails m.watchId m.canceled m.cancelReason
            · wp_apply wp_addSub V G.wgs p P.ws m.watchId m.canceled m.cancelReason (DFrac.own 1)
                (DFrac.own 1) (W64 (-1)) mref S.M e $$ [Hwid Hca Hcrs Hid Hsub Hm HcF Hprod]
                as ⟨Hwid, Hca, Hcrs, Hsub, Hpost⟩
              · iframe; iframe #
                iintro %-
                unfold recvcCloser
                iexists P, sent
                iframe; iframe #
                ipureintro; rfl
              irevert Hpost
              rw [show decide (addFails m.watchId m.canceled m.cancelReason) = true from
                decide_eq_true hfail]
              simp only [↓reduceIte]
              iintro ⟨Hid, Hm, %e', HcF, #He'⟩
              have hXm : m.watchId = W64 (-1) := by
                rcases hfail with h | ⟨hca, -⟩
                · exact h
                · rcases hcase with ⟨-, h⟩ | ⟨h, -⟩
                  · exact h
                  · rw [hca] at h; cases h
              have hMn : S.M !! m.watchId = none := hMf.resolve_right (fun h => h.2 hXm)
              ihave Hrf : iprop(respFields p (DFrac.own 1) m h sl) $$ [Hhdr Hwid Hcr Hca Hcomp Hcrs Hfr Hev]
              · unfold respFields
                rw [hcr0]
                iframe
                ipureintro; exact Hhn
              have hnb : ¬ client.isBroadcast m := fun h => by
                obtain ⟨-, -, h3, -⟩ := h; rw [hcr0] at h3; cases h3
              wp_apply wp_dispatch V G.wgs p (DFrac.own 1) m h sl [] mref S.M (DFrac.own 1)
                (DFrac.own 1) (fun _ => client.dummyWsPrm G G.γr) (fun _ => [])
                (fun _ => client.dummyDn G) G.γend n
                $$ [Hrf Hsub Hm Hgen] as %b ⟨Hrf, Hsub, Hm, Hgen, Hpost⟩
              · iframe
                iframe #
                isplitr
                · ipureintro; simp [hev0]
                isplitr
                · iintro %-; itrivial
                rw [if_neg (by simpa using hnb), hMn]
                itrivial
              rw [ite_eq_left Hbnd]
              wp_apply wp_store_slice_index s (sint.Z (W64 0)) S.l null $$ [Hs] as Hs
              · iframe; ipureintro; exact ⟨by simp, by have := Hsll.1; word⟩
              obtain ⟨Hg1, Hold1, Hnew1⟩ := client.answer_ok (U := U) (reg := false) HgOk hpend hh0 hs0
                hcr0 rfl HXf (fun hc => by rcases hcase with ⟨-, h⟩ | ⟨h, -⟩ <;> simp_all) (fun h => by cases h) (fun h => by cases h) (fun _ => Hph)
              isplitr
              · first | itrivial | (ipureintro; rfl)
              iexists S.answer m i m.watchId P.ws false, e'
              have e1 : (S.answer m i m.watchId P.ws false).M = S.M := by simp [client.RunSt.answer]
              have e2 : (S.answer m i m.watchId P.ws false).l = S.l.set (sint.Z (W64 0)).toNat null := by
                simp [client.RunSt.answer, hn0]
              have e3 : (S.answer m i m.watchId P.ws false).ansd = S.ansd ++ [i] := rfl
              have e4 : (S.answer m i m.watchId P.ws false).regs =
                  (if m.canceled then S.regs else S.regs ++ [m.watchId]) := rfl
              rw [e1, e2, e3, e4]
              isplitr
              · ipureintro; exact ⟨Hg1, rfl, rfl, rfl, rfl, rfl⟩
              iframe
              iframe #
              isplitl [Hat]
              · iapply BigSepL.bigSepL_singleton.2
                unfold client.ansH
                iexists γo, γa
                iframe; iframe #
              isplitl [Hids Hidn]
              · iapply client.regs_join; iframe
              ihave Hels := BigSepM.bigSepM_impl (Ψ := fun ws (_ : Unit) =>
                  client.wsElem V G n γs (S.answer m i m.watchId P.ws false) ws) $$ Hels []
              · iintro !> %ws' %u %Hws' Hw'
                have Hws'' : (GMap.delete P.ws U) !! ws' = some u := Hws'
                have hne : ws' ≠ P.ws := by
                  intro e; subst e; rw [GMap.lookup_delete] at Hws''; cases Hws''
                rw [GMap.lookup_delete_ne _ (Ne.symm hne)] at Hws''
                cases u
                iapply (client.wsElem_mono' V G n γs (S := S) (S' := S.answer m i m.watchId P.ws false) ws'
                  (fun P ph _ => client.wsRest_snoc_ctrl V γs S.Dm m P ph hs0)
                  (fun ph h => Hold1 ws' ph hne Hws'' h) rfl) $$ Hw'
              iapply (BigSepM.bigSepM_delete (Φ := fun ws (_ : Unit) =>
                client.wsElem V G n γs (S.answer m i m.watchId P.ws false) ws) (m := U) (i := P.ws) (x := ()) hU0).2
              iframe Hels
              unfold client.wsElem
              iexists P, .orphan
              isplitr
              · ipureintro; exact ⟨rfl, by simpa using Hnew1 hn0⟩
              iframe HP
              simp only [WPh.id, client.wsRest, client.noCancelOk, WPh.isOrphan]
              iframe Hid
              isplitr
              · itrivial
              isplitr
              · itrivial
              iapply client.wsLife_orphan $$ Hlife
            · have hca : m.canceled = false := by
                cases hcan : m.canceled
                · rfl
                · exfalso; apply hfail
                  rcases hcase with ⟨-, h⟩ | ⟨h, -⟩
                  · left; exact h
                  · rw [hcan] at h; cases h
              have hXn : m.watchId ≠ W64 (-1) := fun h => hfail (Or.inl h)
              have hXr : m.watchId ∉ S.regs := HXf hca
              have hMn : S.M !! m.watchId = none := hMf.resolve_right (fun h => hXr h.1)
              wp_apply wp_addSub V G.wgs p P.ws m.watchId m.canceled m.cancelReason (DFrac.own 1)
                (DFrac.own 1) (W64 (-1)) mref S.M e $$ [Hwid Hca Hcrs Hid Hsub Hm HcF]
                as ⟨Hwid, Hca, Hcrs, Hsub, Hpost⟩
              · iframe; iframe #
                iintro %h'; exact absurd h' hfail
              irevert Hpost
              rw [show decide (addFails m.watchId m.canceled m.cancelReason) = false from
                decide_eq_false hfail]
              simp only [Bool.false_eq_true, ↓reduceIte]
              iintro ⟨Hid, Hm, HcF⟩
              -- the watcher the server registered
              ihave ⟨%w, %rg, %fcs, %lo, %Hcrg, #Hwi, #Hfcs, #Hws, %γo', %γa', #Hax', #Hias⟩ := Hwf $$ %hca
              ihave #Hwi' := Hwi
              iunfold mvcc.watcherIs at Hwi'
              icases Hwi' with ⟨%γw0, %C0, -, #Hwfix, -⟩
              ihave %Hfresh := client.evsSoFar_fresh m.watchId w rg fcs HgOk hXr hXn Hcrg.2.2.1
                $$ [Hinfo Hwfix]
              · iframe #
              -- the cursors: one more, the same
              obtain ⟨HCl, HCh, HC2⟩ := HCs
              imod monoListAuthOwn_update_app (γ := P.γhi) (l := C) [B.hb]
                $$ Hauth with ⟨Hauth, #Hlb⟩
              ihave #Hi0 := monoListIdxOwn_get (γ := P.γhi) sent.length B.hb (by
                rw [List.getElem?_append_left (by omega), ← HCh, List.getLast?_eq_getElem?, HCl]; rfl) $$ Hlb
              ihave #Hi1 := monoListIdxOwn_get (γ := P.γhi) (sent.length + 1) B.hb (by
                rw [List.getElem?_append_right (by omega), HCl]; simp) $$ Hlb
              -- (K2e-7d) the second cursor: one more, the same
              imod monoListAuthOwn_update_app (γ := P.γh2) (l := C2) [B.rr - W64 1]
                $$ Hauth2 with ⟨Hauth2, #Hlb2⟩
              ihave #Hcm0 : client.recvCmpl V P (sent.length : Int) (client.wrOf m h sl)
                  ⟨[], W64 0, false, true, m.hdr.revision⟩ $$ []
              · unfold client.recvCmpl
                cases hcp : P.γ.cpl
                · ileft; ipureintro; rfl
                iright
                obtain ⟨HC2l, HC2h⟩ := HC2 hcp
                ihave #Hj0 := monoListIdxOwn_get (γ := P.γh2) sent.length (B.rr - W64 1) (by
                  rw [List.getElem?_append_left (by omega), ← HC2h, List.getLast?_eq_getElem?, HC2l]; rfl) $$ Hlb2
                ihave #Hj1 := monoListIdxOwn_get (γ := P.γh2) (sent.length + 1) (B.rr - W64 1) (by
                  rw [List.getElem?_append_right (by omega), HC2l]; simp) $$ Hlb2
                iexists B.rr - W64 1, B.rr - W64 1
                simp only [Int.toNat_natCast]
                iframe Hj0 Hj1
                unfold watchRespOk
                iright; ileft
                ipureintro
                refine ⟨?_, rfl, by simp [RespModel.isProgressNotify], rfl⟩
                unfold watchErr client.wrOf; simp [hcomp0, hca]
              ihave Hrf : iprop(respFields p (DFrac.own 1) m h sl) $$ [Hhdr Hwid Hcr Hca Hcomp Hcrs Hfr Hev]
              · unfold respFields
                rw [hcr0]
                iframe
                ipureintro; exact Hhn
              have hnb : ¬ client.isBroadcast m := fun h => by
                obtain ⟨-, -, h3, -⟩ := h; rw [hcr0] at h3; cases h3
              simp only [WPh.isOrphan]
              icases client.wsLife_cap V G n P $$ Hlife with ⟨%d, Hdc, Hback⟩
              wp_apply wp_dispatch V G.wgs p (DFrac.own 1) m h sl [] mref (GMap.insert m.watchId P.ws S.M)
                (DFrac.own 1) (DFrac.own 1) (fun _ => P) (fun _ => sent) (fun _ => d) G.γend n
                $$ [Hrf Hsub Hm Hgen Hprod Hrv Hdc] as %b ⟨Hrf, Hsub, Hm, Hgen, Hpost⟩
              · iframe
                iframe #
                isplitr
                · ipureintro; simp [hev0]
                isplitr
                · iintro %-; itrivial
                rw [if_neg (by simpa using hnb), GMap.lookup_insert]
                isplitr
                · ipureintro; rfl
                unfold sendCap
                iframe
                iframe #
                iintro %wr #Hwr
                iapply client.recvElem_created V P m h sl sent.length B.hb B.rr wr ⟨hcomp0, hca, hcr0⟩ Hhn
                iframe
                iframe #
              irevert Hpost
              rw [if_neg (show ¬ (decide (client.isBroadcast m) = true) by
                simp only [decide_eq_true_eq]; exact hnb)]
              iintro ⟨%wr, Hpost⟩
              ihave #Hsnap : iprop(client.regSnap γs S.Dm w) $$ []
              · irevert Hcaf
                unfold v3rpc.createdAfter
                rw [hcr0, hca]
                simp only [Bool.not_false, Bool.and_self, ↓reduceIte]
                iintro #Hcaf
                icases Hcaf with ⟨%γo2, %γa2, %w2, %l0, %l, %L, %n, #Hax2, #Hia2, #Hl0, #Hl, #HL,
                  #Hrn, %Hn, %Hpp⟩
                ihave %He : iprop(⌜v3rpc.auxOf γo' γa' = v3rpc.auxOf γo2 γa2⌝) $$ []
                · iapply streamAuxIs_agree
                  isplit
                  · iexact Hax'
                  · iexact Hax2
                obtain ⟨rfl, rfl⟩ := v3rpc.auxOf_inj He
                ihave %Hw := mvcc.idAssigned_agree γo' m.watchId w w2 $$ [Hias Hia2]
                · isplit
                  · iexact Hias
                  · iexact Hia2
                subst Hw
                ihave #HL' := HL
                iunfold v3rpc.downLbW at HL'
                ihave %HcL := mono_list_lb_valid _ _ _ $$ HDlb HL'
                have hLD : L = S.Dm := by
                  have hl : L.length = S.Dm.length := by rw [Hpp.2.1]
                  rcases HcL with h' | h'
                  · exact (h'.eq_of_length hl.symm).symm
                  · exact h'.eq_of_length hl
                unfold client.regSnap
                iexists γo', γa', l, L, n
                iframe Hax' Hl Hrn
                ipureintro
                exact ⟨Nat.le_trans Hn Hpp.1.length_le, by rw [hLD]; exact List.prefix_refl _, Hpp.2.2⟩
              ihave #Hrg : iprop(client.regFacts V γs S.Dm P B m.watchId w rg fcs lo) $$ []
              · unfold client.regFacts
                iframe Hwi Hfcs Hsnap
                isplitr
                · ipureintro; exact Hcrg
                isplitr
                · icases Hws with ⟨%γw', #Hm', %Hsr'⟩
                  iexists γw'; iframe Hm'; ipureintro; exact Hsr'
                iexists γo', γa'
                iframe Hax' Hias
              ihave Hpend : iprop(|==> client.cur2Pend V γs (S.Dm ++ [m]) P B m.watchId w rg lo sent
                  (C2 ++ [B.rr - W64 1])) $$ [Hauth2]
              · unfold client.cur2Pend
                cases hcp : P.γ.cpl
                · imodintro; iframe Hauth2; ileft; ipureintro; rfl
                obtain ⟨-, hrev1, -, hstart, -⟩ := client.cpl_facts V P B m.watchId rg HPq.1 HPq.2
                  hcp HB Hcrg
                ihave %Hlo := client.cpl_lo V w rg fcs lo B.rr hstart hrev1 $$ Hwi
                have hE : client.evsOf (S.Dm ++ [m]) w = [] := by
                  have := client.evsSoFar_snoc_ctrl S.Dm m w hs0
                  rw [Hfresh] at this; exact this
                imod client.cur2Ok_init V γs B.rr (S.Dm ++ [m]) m.watchId w rg lo hrev1 Hlo hE with #Hc0
                imodintro
                iframe Hauth2
                iright; iright
                obtain ⟨HC2l, -⟩ := HC2 hcp
                isplitr
                · ipureintro; simp [HC2l]
                iexists B.rr - W64 1
                iframe Hc0
                ipureintro; simp
              imod Hpend with Hpend
              icases client.reg_post V γs P B HB S.Dm m m.watchId w rg fcs lo sent
                (C ++ [B.hb]) (C2 ++ [B.rr - W64 1]) b wr
                d G.γend n $$ [Hauth Hpost Hpend Hpsq] with ⟨Hrest, Hdc⟩
              · iframe Hauth Hpost Hpend
                iframe #
                iright
                isplitr
                · ipureintro; simp [HCl]
                isplitr [Hpsq]
                · iexists B.hb
                  isplitr
                  · ipureintro; simp
                  unfold client.cursorOk
                  rw [client.evsSoFar_snoc_ctrl S.Dm m w hs0, Hfresh]
                  isplitr
                  · ipureintro; left; exact ⟨rfl, rfl⟩
                  ileft; ipureintro; rfl
                iapply client.psSt_psAt; iexact Hpsq
              rw [ite_eq_left Hbnd]
              wp_apply wp_store_slice_index s (sint.Z (W64 0)) S.l null $$ [Hs] as Hs
              · iframe; ipureintro; exact ⟨by simp, by have := Hsll.1; word⟩
              obtain ⟨Hg1, Hold1, Hnew1⟩ := client.answer_ok (U := U) (reg := true) HgOk hpend hh0 hs0
                hcr0 rfl HXf (fun hc => by rcases hcase with ⟨-, h⟩ | ⟨h, -⟩ <;> simp_all) (fun _ => hMn) (fun _ => ⟨hn0, hXn, hca⟩) (fun _ => Hph)
              isplitr
              · first | itrivial | (ipureintro; rfl)
              iexists S.answer m i m.watchId P.ws true, e
              have e1 : (S.answer m i m.watchId P.ws true).M = GMap.insert m.watchId P.ws S.M := by simp [client.RunSt.answer]
              have e2 : (S.answer m i m.watchId P.ws true).l = S.l.set (sint.Z (W64 0)).toNat null := by
                simp [client.RunSt.answer, hn0]
              have e3 : (S.answer m i m.watchId P.ws true).ansd = S.ansd ++ [i] := rfl
              have e4 : (S.answer m i m.watchId P.ws true).regs =
                  (if m.canceled then S.regs else S.regs ++ [m.watchId]) := rfl
              rw [e1, e2, e3, e4]
              isplitr
              · ipureintro; exact ⟨Hg1, rfl, rfl, rfl, rfl, rfl⟩
              iframe
              iframe #
              isplitl [Hat]
              · iapply BigSepL.bigSepL_singleton.2
                unfold client.ansH
                iexists γo, γa
                iframe; iframe #
              isplitl [Hids Hidn]
              · iapply client.regs_join; iframe
              ihave Hels := BigSepM.bigSepM_impl (Ψ := fun ws (_ : Unit) =>
                  client.wsElem V G n γs (S.answer m i m.watchId P.ws true) ws) $$ Hels []
              · iintro !> %ws' %u %Hws' Hw'
                have Hws'' : (GMap.delete P.ws U) !! ws' = some u := Hws'
                have hne : ws' ≠ P.ws := by
                  intro e; subst e; rw [GMap.lookup_delete] at Hws''; cases Hws''
                rw [GMap.lookup_delete_ne _ (Ne.symm hne)] at Hws''
                cases u
                iapply (client.wsElem_mono' V G n γs (S := S) (S' := S.answer m i m.watchId P.ws true) ws'
                  (fun P ph _ => client.wsRest_snoc_ctrl V γs S.Dm m P ph hs0)
                  (fun ph h => Hold1 ws' ph hne Hws'' h) rfl) $$ Hw'
              iapply (BigSepM.bigSepM_delete (Φ := fun ws (_ : Unit) =>
                client.wsElem V G n γs (S.answer m i m.watchId P.ws true) ws) (m := U) (i := P.ws) (x := ()) hU0).2
              iframe Hels
              unfold client.wsElem
              iexists P, .reg m.watchId
              isplitr
              · ipureintro; exact ⟨rfl, by simpa using Hnew1 hn0⟩
              iframe HP
              simp only [WPh.id]
              iframe Hid
              rw [show (S.answer m i m.watchId P.ws true).Dm = S.Dm ++ [m] from rfl]
              iframe Hrest
              -- a fresh id: no cancel request for it was sent (a cancel's id is registered)
              isplitr
              · unfold client.noCancelOk
                ileft; ipureintro
                intro j hj
                exact hXr (HgOk.2.2.2.2.2.2.2.2.1 j m.watchId hj)
              iunfold dnCap at Hdc
              icases Hdc with ⟨Hdc, -⟩
              simp only [WPh.isOrphan]
              iapply Hback $$ Hdc
          iintro %v ⟨%Hv, %S1, %e1, ⟨%Hg1, %Hp1, %HL1, %HD1, %HCL1, %HCS1⟩, Hsub, Hm, Hres, Hs, Hscap,
            HcF, #He1, Hans, Hids, Hels, Hgen⟩
          subst Hv
          wp_auto
          wp_apply wp_nextResume G.wgs s S1.l $$ [Hres Hs Hscap] as %ws2 ⟨%s2, Hres, Hs, %Hws2⟩
          · iframe #; unfold sliceOwn; iframe
          by_cases hn2 : ws2 = null
          · simp only [hn2, _root_.decide_true, Bool.not_true]
            have hhd : (S1.l.dropWhile (fun x => decide (x = null))).head? = none := by
              cases hd : (S1.l.dropWhile (fun x => decide (x = null))).head? with
              | none => rfl
              | some x =>
                exfalso
                have hx := client.dropNull_head hd
                rw [hd] at Hws2; simp at Hws2; exact hx (Hws2 ▸ hn2)
            obtain ⟨Hg2, Hold2, -⟩ := client.resume_ok (si := none) (U := U) Hg1 Hp1
              (Or.inl ⟨rfl, rfl, rfl⟩)
            ihave Hels := BigSepM.bigSepM_impl (Ψ := fun ws (_ : Unit) =>
                client.wsElem V G n γs (S1.resume S1.L none) ws) $$ Hels []
            · iintro !> %ws' %u %Hws' Hw'
              have Hws'' : U !! ws' = some u := Hws'
              cases u
              iapply (client.wsElem_mono V G n γs (S := S1) (S' := S1.resume S1.L none) ws' rfl
                (fun ph h => Hold2 ws' ph Hws'' (by rw [hhd]; simp) h) (fun _ _ _ hi => hi)) $$ Hw'
            wp_auto
            wp_for_post
            iexists bo, γs, b, n, _, Dn, cd', rc, γrc, csm
            simp only [named]
            iframe closeErr cur backoff wc cancelSet Hrc Hrcb Hcws Hspec
            unfold client.runCore
            iexists S1.resume S1.L none, U, rcv ++ [p], mref, s2, e1
            have r1 : (S1.resume S1.L none).Dm = S.Dm ++ [m] := HD1
            have r2 : (S1.resume S1.L none).M = S1.M := rfl
            have r3 : (S1.resume S1.L none).l = S1.l.dropWhile (fun x => decide (x = null)) := rfl
            have r4 : (S1.resume S1.L none).CL = S.CL := HCL1
            have r5 : (S1.resume S1.L none).CS = S.CS := HCS1
            have r6 : (S1.resume S1.L none).L = S1.L := rfl
            have r7 : (S1.resume S1.L none).ansd = S1.ansd := rfl
            have r8 : (S1.resume S1.L none).regs = S1.regs := rfl
            rw [r1, r2, r3, r4, r5, r6, r7, r8]
            rw [HL1]
            iframe
            iframe #
            isplitr
            · ipureintro; simp only [List.length_append, List.length_singleton]; omega
            isplitl []
            · unfold v3rpc.downLbW; iexact HLlb
            isplitr
            · ipureintro; first | exact Hg2 | (rw [← HL1]; exact Hg2)
            imodintro
            iapply BigSepL.bigSepL_singleton.2
            unfold client.respInfo; rw [hs0]; itrivial
          simp only [hn2, decide_false, Bool.not_false]
          have hhd : (S1.l.dropWhile (fun x => decide (x = null))).head? = some ws2 := by
            cases hd : (S1.l.dropWhile (fun x => decide (x = null))).head? with
            | none => rw [hd] at Hws2; simp at Hws2; exact absurd Hws2 hn2
            | some x => rw [hd] at Hws2; simp at Hws2; rw [Hws2]
          have hmem2 : ws2 ∈ S1.l :=
            (client.mem_dropNull hn2).1 (List.mem_of_getElem? (by rw [← List.head?_eq_getElem?]; exact hhd))
          have hU2 : U !! ws2 = some () := Hg1.2.2.1 ws2 hmem2 hn2
          icases (BigSepM.bigSepM_delete hU2).1 $$ Hels with ⟨Hw, Hels⟩
          iunfold client.wsElem at Hw
          icases Hw with ⟨%P2, %ph2, ⟨%HPws2, %Hph2⟩, #HP2, Hid2, Hrest2, #Hnc2, Hlife2⟩
          subst HPws2
          obtain ⟨si2, rfl⟩ : ∃ si2, ph2 = .queued si2 := by
            cases ph2 with
            | queued si => exact ⟨si, rfl⟩
            | reg X => exact absurd hmem2 Hph2.2.1
            | closedRun X => exact absurd hmem2 Hph2.2.1
            | orphan => exact absurd hmem2 Hph2.2.1
            | closed => exact absurd hmem2 Hph2.2.1
          icases client.queued_send V γs S1.Dm P2 si2 $$ Hrest2 with ⟨%B2, %q2, Hrv2, #HsoB2, Hback2⟩
          ihave #HP2' := HP2
          iunfold wsIs at HP2'
          icases HP2' with ⟨#Hro2, -⟩
          iunfold wrRO at Hro2
          icases Hro2 with ⟨-, #Rkey, #Rend, -, #Rpn, #Rfrag, -, #Rflt, #Rflts, #Rprev⟩
          wp_take_receipt as Hrc
          wp_apply wp_toPB (wsF P2.ws go!"initReq") P2.key P2.ed B2.rr P2.pn P2.flt
            (DFrac.own q2) B2.srr $$ [Hrv2] as %preq ⟨Hrv2, Hpsend⟩
          · iframe #; iframe
          imod mvcc.watchTokPool_take V.R.γ $$ Htoks Hrc with Hwt
          wp_apply HSend $$ %S.L %preq %(.create (createOf P2.key P2.ed B2.rr P2.pn B2.srr)) [Hstok Hpsend Hwt]
            as %err ⟨-, Hres'⟩
          · iframe
            unfold v3rpc.watchUp
            iframe
            isplitr
            · ipureintro; simp [v3rpc.watchReqOk, createOf]
            dsimp only; iframe
            simp only [createOf]; iapply client.startOk_read $$ HsoB2
          ihave ⟨%L', %si, Hstok, %Hcase, Hupi⟩ : iprop(∃ (L' : List v3rpc.WatchReqM) (si : Option Nat),
              cliSendTok (Req := v3rpc.pbWatchRequest) γs L' ∗
              ⌜(L' = S1.L ∧ si = none ∧ si = none) ∨
                ((∃ c, L' = S1.L ++ [.create c]) ∧ si = some S1.L.length ∧ si = some S1.L.length ∧
                  S1.l.dropWhile (fun y => decide (y = null)) ≠ [])⌝ ∗
              client.upAtOpt γs si (client.createOfB P2 B2)) $$ [Hres']
          · have hne2 : S1.l.dropWhile (fun y => decide (y = null)) ≠ [] := by
              intro e0; rw [e0] at hhd; simp at hhd
            ihave Hmk : iprop(∀ L2 : List v3rpc.WatchReqM,
                ⌜L2 = S.L ∨ L2 = S.L ++ [.create (createOf P2.key P2.ed B2.rr P2.pn B2.srr)]⌝ -∗
                cliSendTok (Req := v3rpc.pbWatchRequest) γs L2 -∗
                ∃ (L' : List v3rpc.WatchReqM) (si : Option Nat),
                cliSendTok (Req := v3rpc.pbWatchRequest) γs L' ∗
                ⌜(L' = S1.L ∧ si = none ∧ si = none) ∨
                  ((∃ c, L' = S1.L ++ [.create c]) ∧ si = some S1.L.length ∧ si = some S1.L.length ∧
                    S1.l.dropWhile (fun y => decide (y = null)) ≠ [])⌝ ∗
                client.upAtOpt γs si (client.createOfB P2 B2)) $$ []
            · iintro %L2 %HL2 Hst
              rw [← HL1] at HL2
              rcases HL2 with rfl | rfl
              · iexists S1.L, none
                iframe
                isplitr
                · ipureintro; exact Or.inl ⟨rfl, rfl, rfl⟩
                unfold client.upAtOpt; itrivial
              · ihave ⟨Hst, #Hlb⟩ := cliSendTok_lb $$ Hst
                iexists _, some S1.L.length
                iframe
                isplitr
                · ipureintro
                  exact Or.inr ⟨⟨_, rfl⟩, rfl, rfl, hne2⟩
                ihave Hu := upLb_at (Req := v3rpc.pbWatchRequest) γs _ S1.L.length
                  (.create (createOf P2.key P2.ed B2.rr P2.pn B2.srr)) (by simp) $$ Hlb
                unfold client.upAtOpt v3rpc.upAtW
                iunfold upAt at Hu
                iexact Hu
            icases Hres' with (⟨-, Htok⟩ | ⟨-, %L2, %HL2, Htok⟩)
            · iapply Hmk $$ %_ %(Or.inr rfl) Htok
            · iapply Hmk $$ %L2 %HL2 Htok
          obtain ⟨Hg2, Hold2, Hnew2⟩ := client.resume_ok (U := U) (L' := L') (pend' := si) (si := si)
            Hg1 Hp1 Hcase
          ihave Hels := BigSepM.bigSepM_impl (Ψ := fun ws (_ : Unit) =>
              client.wsElem V G n γs (S1.resume L' si) ws) $$ Hels []
          · iintro !> %ws' %u %Hws' Hw'
            have Hws'' : (GMap.delete P2.ws U) !! ws' = some u := Hws'
            have hne : ws' ≠ P2.ws := by
              intro e; subst e; rw [GMap.lookup_delete] at Hws''; cases Hws''
            rw [GMap.lookup_delete_ne _ (Ne.symm hne)] at Hws''
            cases u
            iapply (client.wsElem_mono V G n γs (S := S1) (S' := S1.resume L' si) ws' rfl
              (fun ph h => Hold2 ws' ph Hws'' (by rw [hhd]; intro e; exact hne (Option.some.inj e).symm) h)
              (fun X _ => client.create_or (by
                rcases Hcase with ⟨h, -⟩ | ⟨h, -⟩
                · exact Or.inl h
                · exact Or.inr h) X))
              $$ Hw'
          ihave Hels := (BigSepM.bigSepM_delete (Φ := fun ws (_ : Unit) =>
              client.wsElem V G n γs (S1.resume L' si) ws) (m := U) (i := P2.ws) (x := ()) hU2).2
              $$ [Hels Hid2 Hback2 Hrv2 Hupi Hlife2]
          · iframe Hels
            unfold client.wsElem
            iexists P2, .queued si
            isplitr
            · ipureintro; exact ⟨rfl, Hnew2 P2.ws hhd hU2 _ Hph2⟩
            iframe HP2
            simp only [WPh.id]
            iframe Hid2
            simp only [client.noCancelOk, WPh.isOrphan]
            iframe Hlife2
            iapply Hback2 $$ Hrv2 Hupi
          cases err with
          | nil =>
            wp_auto
            wp_for_post
            iexists bo, γs, b, n, _, Dn, cd', rc, γrc, csm
            simp only [named]
            iframe closeErr cur backoff wc cancelSet Hrc Hrcb Hcws Hspec
            unfold client.runCore
            iexists S1.resume L' si, U, rcv ++ [p], mref, s2, e1
            have r1 : (S1.resume L' si).Dm = S.Dm ++ [m] := HD1
            have r2 : (S1.resume L' si).M = S1.M := rfl
            have r3 : (S1.resume L' si).l = S1.l.dropWhile (fun x => decide (x = null)) := rfl
            have r4 : (S1.resume L' si).CL = S.CL := HCL1
            have r5 : (S1.resume L' si).CS = S.CS := HCS1
            have r6 : (S1.resume L' si).L = L' := rfl
            have r7 : (S1.resume L' si).ansd = S1.ansd := rfl
            have r8 : (S1.resume L' si).regs = S1.regs := rfl
            rw [r1, r2, r3, r4, r5, r6, r7, r8]
            iframe
            iframe #
            isplitr
            · ipureintro; simp only [List.length_append, List.length_singleton]; omega
            isplitl []
            · unfold v3rpc.downLbW; iexact HLlb
            isplitr
            · ipureintro; exact Hg2
            imodintro
            iapply BigSepL.bigSepL_singleton.2
            unfold client.respInfo; rw [hs0]; itrivial
          | ok ei =>
            wp_auto
            wp_apply wp_zapError as %f2 -
            wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f2]
            isplitr
            · ipureintro; rfl
            iintro %fsl ⟨-, -⟩
            wp_auto
            wp_apply wp_Debug V.lg _ _ $$ []
            · iframe #; ipureintro; exact Hlg
            (try wp_auto)
            wp_for_post
            iexists bo, γs, b, n, _, Dn, cd', rc, γrc, csm
            simp only [named]
            iframe closeErr cur backoff wc cancelSet Hrc Hrcb Hcws Hspec
            unfold client.runCore
            iexists S1.resume L' si, U, rcv ++ [p], mref, s2, e1
            have r1 : (S1.resume L' si).Dm = S.Dm ++ [m] := HD1
            have r2 : (S1.resume L' si).M = S1.M := rfl
            have r3 : (S1.resume L' si).l = S1.l.dropWhile (fun x => decide (x = null)) := rfl
            have r4 : (S1.resume L' si).CL = S.CL := HCL1
            have r5 : (S1.resume L' si).CS = S.CS := HCS1
            have r6 : (S1.resume L' si).L = L' := rfl
            have r7 : (S1.resume L' si).ansd = S1.ansd := rfl
            have r8 : (S1.resume L' si).regs = S1.regs := rfl
            rw [r1, r2, r3, r4, r5, r6, r7, r8]
            iframe
            iframe #
            isplitr
            · ipureintro; simp only [List.length_append, List.length_singleton]; omega
            isplitl []
            · unfold v3rpc.downLbW; iexact HLlb
            isplitr
            · ipureintro; exact Hg2
            imodintro
            iapply BigSepL.bigSepL_singleton.2
            unfold client.respInfo; rw [hs0]; itrivial
        | cancel X =>
          obtain ⟨hs0, hev0, hcomp0, hfr0, hcr0, hca0, hid0⟩ : m.src = none ∧ m.evs = [] ∧
              m.compactRev = W64 0 ∧ m.fragment = false ∧ m.created = false ∧ m.canceled = true ∧
              m.watchId = X := by
            simp only [v3rpc.ctrlAnswers] at Hcans; exact Hcans
          rw [hcr0]
          wp_auto
          rw [hca0, hcomp0, hid0]
          wp_auto
          wp_apply wp_mapDelete $$ Hcsm as Hcsm
          wp_apply wp_map_lookup2 $$ Hm as Hm
          icases client.sendTok_lookup γs S.L i (.cancel X) $$ [Hstok Hup] with ⟨Hstok, %HLi⟩
          · iframe; iframe #
          ihave Hfr : iprop(⌜i ∉ S.ansd⌝ ∗ ([∗list] j ∈ S.ansd, client.ansH γs j) ∗ v3rpc.ansTok γa i)
            $$ [Hans Hat]
          · iapply client.ans_fresh
            iframe
            iframe #
          icases Hfr with ⟨%Hia, Hans, Hat⟩
          obtain ⟨Hg2, Hold, Hnew⟩ := client.cancelAns_ok (U := U) (fw := S.M !! X) HgOk HLi Hia
            hs0 hcr0 hid0 rfl
          cases hMX : S.M !! X with
          | none =>
            rw [hMX] at Hg2 Hold
            simp only [hMX, Option.isSome_none, Bool.false_eq_true, decide_false]
            wp_auto
            ihave Hels := BigSepM.bigSepM_impl
                (Ψ := fun ws (_ : Unit) => client.wsElem V G n γs (S.cancelAns m i X none) ws) $$ Hels []
            · iintro !> %ws' %u %Hws' Hw'
              have Hws'' : U !! ws' = some u := Hws'
              cases u
              iapply (client.wsElem_mono' V G n γs (S := S) (S' := S.cancelAns m i X none) ws'
                (fun P ph _ => client.wsRest_snoc_ctrl V γs S.Dm m P ph hs0)
                (fun ph h => Hold ws' ph Hws'' (by simp) h) rfl) $$ Hw'
            wp_for_post
            iexists bo, γs, b, n, _, Dn, cd', rc, γrc, csm
            simp only [named]
            iframe closeErr cur backoff wc cancelSet Hrc Hrcb Hcws Hspec
            unfold client.runCore
            iexists S.cancelAns m i X none, U, rcv ++ [p], mref, s, e
            have e1 : (S.cancelAns m i X none).Dm = S.Dm ++ [m] := rfl
            have e2 : (S.cancelAns m i X none).L = S.L := rfl
            have e3 : (S.cancelAns m i X none).ansd = S.ansd ++ [i] := rfl
            have e4 : (S.cancelAns m i X none).regs = S.regs := rfl
            have e5 : (S.cancelAns m i X none).CS = GMap.delete X S.CS := rfl
            have e6 : (S.cancelAns m i X none).M = S.M := rfl
            have e7 : (S.cancelAns m i X none).CL = S.CL := rfl
            have e8 : (S.cancelAns m i X none).l = S.l := rfl
            rw [e1, e2, e3, e4, e5, e6, e7, e8]
            iframe
            iframe #
            isplitr
            · ipureintro; simp only [List.length_append, List.length_singleton]; omega
            isplitl []
            · unfold v3rpc.downLbW; iexact HLlb
            isplitr
            · ipureintro; exact Hg2
            isplitl [Hat]
            · iapply BigSepL.bigSepL_singleton.2
              unfold client.ansH
              iexists γo, γa
              iframe #; iframe
            imodintro
            iapply BigSepL.bigSepL_singleton.2
            unfold client.respInfo; rw [hs0]; itrivial
          | some wsx =>
            rw [hMX] at Hg2 Hold Hnew
            have hUx : U !! wsx = some () := HgOk.1 X wsx hMX
            icases (BigSepM.bigSepM_delete hUx).1 $$ Hels with ⟨Hx, Hels⟩
            iunfold client.wsElem at Hx
            icases Hx with ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest, #Hnc, Hlife⟩
            subst HPws
            have hreg : ph = .reg X := by
              cases ph with
              | queued si => exact absurd hMX (Hph.1 X)
              | orphan => exact absurd hMX (Hph.1 X)
              | closed => exact absurd hMX (Hph.1 X)
              | closedRun Y => exact absurd hMX (Hph.1.2.1 X)
              | reg Y =>
                have hY : Y = X := HgOk.2.1 Y X P.ws Hph.1 hMX
                rw [hY]
            subst hreg
            have Hph2 := Hnew P.ws (.reg X) rfl Hph
            simp only [client.wsRest, client.noCancelOk]
            icases Hrest with ⟨%B, %w, %rg, %fcs, %lo, %sent, %C, -, -, -, Hprod, -, -⟩
            ihave #HP' := HP
            iunfold wsIs at HP'
            icases HP' with ⟨-, #Frecvc, -, #Hrecvc, -⟩
            simp only [hMX, Option.isSome_some, _root_.decide_true, Option.getD_some]
            wp_auto
            wp_apply wp_sspsc_close P.γr P.recvc (client.recvElem V P) (fun _ => iprop(True)) sent
              $$ [Hprod]
            · iframe Hrecvc Hprod
            wp_pures
            wp_apply wp_mapInsert $$ Hclm as Hclm
            wp_apply wp_mapDelete $$ Hm as Hm
            ihave Hels := BigSepM.bigSepM_impl
                (Ψ := fun ws (_ : Unit) => client.wsElem V G n γs (S.cancelAns m i X (some P.ws)) ws)
                $$ Hels []
            · iintro !> %ws' %u %Hws' Hw'
              have Hws'' : (GMap.delete P.ws U) !! ws' = some u := Hws'
              have hne : ws' ≠ P.ws := by
                intro e; subst e; rw [GMap.lookup_delete] at Hws''; cases Hws''
              rw [GMap.lookup_delete_ne _ (Ne.symm hne)] at Hws''
              cases u
              iapply (client.wsElem_mono' V G n γs (S := S) (S' := S.cancelAns m i X (some P.ws)) ws'
                (fun P ph _ => client.wsRest_snoc_ctrl V γs S.Dm m P ph hs0)
                (fun ph h => Hold ws' ph Hws'' (fun e => hne (Option.some.inj e).symm) h) rfl) $$ Hw'
            ihave Hels := (BigSepM.bigSepM_delete (Φ := fun ws (_ : Unit) =>
                client.wsElem V G n γs (S.cancelAns m i X (some P.ws)) ws) (m := U) (i := P.ws) (x := ())
                hUx).2 $$ [Hels Hid Hlife]
            · iframe Hels
              unfold client.wsElem
              iexists P, .closedRun X
              isplitr
              · ipureintro; exact ⟨rfl, Hph2⟩
              iframe HP
              -- (D24) a cancel for its id was sent: its goroutine had stopped (`noCancelOk`)
              ihave #Hx : iprop(dghostVar P.γx DFrac.discard true) $$ []
              · icases Hnc with (%Hn | #Hx)
                · exact absurd HLi (Hn i)
                · iexact Hx
              simp only [WPh.id, client.wsRest, client.noCancelOk, WPh.isOrphan]
              iframe Hid Hlife Hx
              try itrivial
            wp_for_post
            iexists bo, γs, b, n, _, Dn, cd', rc, γrc, csm
            simp only [named]
            iframe closeErr cur backoff wc cancelSet Hrc Hrcb Hcws Hspec
            unfold client.runCore
            iexists S.cancelAns m i X (some P.ws), U, rcv ++ [p], mref, s, e
            have e1 : (S.cancelAns m i X (some P.ws)).Dm = S.Dm ++ [m] := rfl
            have e2 : (S.cancelAns m i X (some P.ws)).L = S.L := rfl
            have e3 : (S.cancelAns m i X (some P.ws)).ansd = S.ansd ++ [i] := rfl
            have e4 : (S.cancelAns m i X (some P.ws)).regs = S.regs := rfl
            have e5 : (S.cancelAns m i X (some P.ws)).CS = GMap.delete X S.CS := rfl
            have e6 : (S.cancelAns m i X (some P.ws)).M = GMap.delete X S.M := rfl
            have e7 : (S.cancelAns m i X (some P.ws)).CL = GMap.insert P.ws () S.CL := rfl
            have e8 : (S.cancelAns m i X (some P.ws)).l = S.l := rfl
            rw [e1, e2, e3, e4, e5, e6, e7, e8]
            iframe
            iframe #
            isplitr
            · ipureintro; simp only [List.length_append, List.length_singleton]; omega
            isplitl []
            · unfold v3rpc.downLbW; iexact HLlb
            isplitr
            · ipureintro; exact Hg2
            isplitl [Hat]
            · iapply BigSepL.bigSepL_singleton.2
              unfold client.ansH
              iexists γo, γa
              iframe #; iframe
            imodintro
            iapply BigSepL.bigSepL_singleton.2
            unfold client.respInfo; rw [hs0]; itrivial

        | progress => exact absurd Hcans (by simp [v3rpc.ctrlAnswers])
        | other => exact absurd Hcans (by simp [v3rpc.ctrlAnswers])
      ihave #Hmvcc' := Hmvcc
      iunfold v3rpc.mvccOk at Hmvcc'
      icases Hmvcc' with ⟨%ρ, %rs, %Lp, %Hpure, #HLp, #Hrecv, %Hfilt, -, #Hcov, %Hfr2⟩
      obtain ⟨Hmeq, Hrev, HLplen, Hlast, Hlive⟩ := Hpure
      have hsrc : m.src = some ρ := by rw [Hmeq]; rfl
      have hcr0 : m.created = false := by rw [Hmeq]; rfl
      have hca0 : m.canceled = false := by rw [Hmeq]; rfl
      have hcomp0 : m.compactRev = W64 0 := by rw [Hmeq]; rfl
      have hfr0 : m.fragment = false := by rw [Hmeq]; rfl
      have hid0 : m.watchId = ρ.id := by rw [Hmeq]; rfl
      have hev0 : m.evs = ρ.evs := by rw [Hmeq]; rfl
      iunfold v3rpc.downLbW at HLp
      ihave %Hcmp2 := mono_list_lb_valid _ _ _ $$ HDlb HLp
      have HLpe : Lp = S.Dm := by
        rcases Hcmp2 with h | h
        · exact (List.prefix_iff_eq_take.1 h).trans (List.take_of_length_le (by omega)) |>.symm
        · exact (List.prefix_iff_eq_take.1 h).trans (List.take_of_length_le (by omega))
      subst HLpe
      rw [hcr0]
      wp_auto
      rw [hca0]
      wp_auto
      rw [hfr0]
      wp_auto
      -- what the dispatch reads
      ihave #Hrok : mvcc.respOk ρ $$ []
      · iunfold mvcc.watchRecvOk at Hrecv
        icases Hrecv with ⟨%γw, %rr, %fcs, %Lr, %D, %d, -, -, -, -, -, -, -, #Hrs⟩
        iapply Hrs $$ %ρ %(List.mem_of_getLast? Hlast)
      ihave ⟨%kvs, %Hkvl, #Hea, #Hkv⟩ := client.evs_eventsAt sl ps ρ.evs (by rw [← hev0]; exact Hpslen)
        $$ [Hps Hevs]
      · iframe #; rw [← hev0]; iframe #
      iunfold v3rpc.hdrOwn at Hho
      icases Hho with ⟨%Hhn, Hh1, Hh2, Hhrev, Hh4, Hh5⟩
      ihave Hrf : iprop(respFields p (DFrac.own 1) m h sl) $$ [Hhdr Hwid Hcr Hca Hcomp Hcrs Hfr Hev]
      · unfold respFields
        rw [hcr0, hca0, hcomp0, hfr0, hid0]
        iframe
        ipureintro; exact Hhn
      by_cases hid : ρ.id = W64 (-1)
      · -- a progress response of id `-1` (unit W-K): broadcast to every registered substream
        iunfold v3rpc.mvccCov at Hcov
        icases Hcov with ⟨%γc, %pre, %γo, %γa, #Hax, %Hγ, #Hfwd, #Hsl0, #Hrc, #Hra, #Hcq⟩
        iunfold mvcc.respCov at Hrc
        icases Hrc with ⟨-, #Hcmp, -⟩
        ihave #Hcmp0 := Hcmp
        iunfold mvcc.respCompl at Hcmp
        icases Hcmp with (%hne | ⟨-, %Hr1⟩)
        · exact absurd hid hne
        obtain ⟨hr1, hevn⟩ := Hr1
        have hb : client.isBroadcast m := by
          refine ⟨by rw [hev0, hevn], hca0, hcr0, hcomp0, ?_, by rw [hid0, hid]⟩
          rw [Hrev]; intro h0; rw [h0] at hr1; exact absurd hr1 (by decide)
        have hinj : ∀ X Y ws, S.M !! X = some ws → S.M !! Y = some ws → X = Y := HgOk.2.1
        have hU : ∀ X ws, S.M !! X = some ws → U !! ws = some () := HgOk.1
        obtain ⟨Hg1, Hph1⟩ := client.recvMvcc_ok HgOk hsrc (fun hne => absurd hid hne)
        ipersist Hhrev
        ihave #Hha : hdrAt h m.hdr.revision $$ []
        · unfold hdrAt; iright; iframe Hhrev; ipureintro; exact Hhn
        have hkv0 : List.zipWith client.evModelOf ρ.evs kvs = [] := by rw [hevn]; rfl
        irevert Hea; rw [hkv0]; iintro #Hea
        -- the registered substreams (`substreams`'s) and the others
        icases client.bigSepM_split_inj (fun ws => client.wsElem V G n γs S ws) U S.M hU hinj $$ Hels
          with ⟨HelM, HelR⟩
        -- (K2e-7d) the broadcast covers every registered substream's watcher, unless it stopped
        imod client.bcast_covAll V G n γs ρ γc pre γo γa hinj Hγ.1 Hγ.2.1 Hγ.2.2.1 Hfr2.1 hid
          $$ [Hax Hsl0 Hra Hcmp0 Hcq Hlc3 Hstok HelM] with ⟨Hstok, HelM, #Hcall⟩
        · iframe Hlc3 Hstok HelM; iframe #
        ihave #HDw : v3rpc.downLbW γs S.Dm $$ []
        · unfold v3rpc.downLbW; iexact HDlb
        ihave HelR := BigSepM.bigSepM_impl
            (Ψ := fun ws (_ : Unit) => iprop(⌜∃ X, S.M !! X = some ws⌝ ∨
              client.wsElem V G n γs (S.recvMvcc m) ws)) $$ HelR []
        · iintro !> %ws' %u %Hws' Hw'
          icases Hw' with (%Hin | Hw')
          · ileft; ipureintro; exact Hin
          iright
          iapply (client.wsElem_recv_other V G n γs (S := S) (S' := S.recvMvcc m) ws' m ρ hsrc rfl
            (fun X h e => by rw [hid] at e; exact h.2.2.2.2.1 e.symm)
            (fun ph h => Hph1 ws' ph h) rfl) $$ [Hw']
          iframe; iframe #
        ihave HelM := BigSepM.bigSepM_impl
            (Ψ := fun (_X : w64) ws => iprop(|={⊤}=> ∃ a : client.WsPrm GF × List Loc × DnInfo GF,
              ⌜a.1.ws = ws⌝ ∗
              client.sendCap V a.1 a.2.1 (fun wr => iprop(wr ↦□ client.wrOf m h sl)) a.2.2 G.γend n ∗
              (∀ wr : Loc, (client.sendDone a.1 a.2.1 wr a.2.2 G.γend n ∨
                client.sendFail V a.1 a.2.1 wr a.2.2 G.γend n) -∗
                client.wsElem V G n γs (S.recvMvcc m) ws))) $$ HelM []
        · iintro !> %X %ws' %HX Hw'
          iapply (client.bcast_elem V G n γs (S := S) (S' := S.recvMvcc m) X ws' S.Dm.length m ρ h sl hsrc
            hevn ⟨hcomp0, hca0, hcr0⟩ Hhn HX hinj rfl (fun ph h => Hph1 ws' ph h) rfl rfl hid
            Hpre.1)
          iframe Hha Hea Hw' Hmvcc HDw Hsmall
          iapply Hcall $$ %X %ws' %HX
        imod (BigSepM.bigSepM_fupd ⊤ _ _) $$ HelM with HelM
        icases client.bigSepM_choice_inj (client.dummyWsPrm G G.γr, ([] : List Loc), client.dummyDn G)
            (fun ws a => iprop(⌜a.1.ws = ws⌝ ∗
              client.sendCap V a.1 a.2.1 (fun wr => iprop(wr ↦□ client.wrOf m h sl)) a.2.2 G.γend n ∗
              (∀ wr : Loc, (client.sendDone a.1 a.2.1 wr a.2.2 G.γend n ∨
                client.sendFail V a.1 a.2.1 wr a.2.2 G.γend n) -∗
                client.wsElem V G n γs (S.recvMvcc m) ws))) S.M hinj $$ HelM with ⟨%f, HelM⟩
        ihave HelM : iprop([∗map] _X ↦ ws ∈ S.M, iprop((⌜(f ws).1.ws = ws⌝ ∗
              client.sendCap V (f ws).1 (f ws).2.1 (fun wr => iprop(wr ↦□ client.wrOf m h sl))
                (f ws).2.2 G.γend n) ∗
              (∀ wr : Loc, (client.sendDone (f ws).1 (f ws).2.1 wr (f ws).2.2 G.γend n ∨
                client.sendFail V (f ws).1 (f ws).2.1 wr (f ws).2.2 G.γend n) -∗
                client.wsElem V G n γs (S.recvMvcc m) ws)))
            $$ [HelM]
        · iapply (BigSepM.bigSepM_mono (fun {_ _} _ => by
            iintro ⟨Hp, Hc, Hw⟩
            isplitl [Hp Hc]
            · iframe Hp Hc
            iexact Hw)) $$ HelM
        rw [BigSepM.bigSepM_sep_eq]
        icases HelM with ⟨HcapM, HwM⟩
        ihave Hhw : iprop(⌜m.evs = []⌝ -∗ hdrAt h m.hdr.revision) $$ []
        · iintro %-; iexact Hha
        wp_apply wp_dispatch V G.wgs p (DFrac.own 1) m h sl [] mref S.M (DFrac.own 1) (DFrac.own 1)
          (fun ws => (f ws).1) (fun ws => (f ws).2.1) (fun ws => (f ws).2.2) G.γend n
          $$ [Hrf Hhw Hsub Hm Hgen HcapM] as %b ⟨Hrf, Hsub, Hm, Hgen, Hpost⟩
        · rw [if_pos (decide_eq_true hb)]
          iframe
          iframe #
          ipureintro; rw [hev0, hevn]; rfl
        irevert Hpost
        rw [if_pos (decide_eq_true hb)]
        iintro ⟨%Hbt, %wr, Hpost⟩
        subst Hbt
        ihave HelM : iprop([∗map] _X ↦ ws ∈ S.M, client.wsElem V G n γs (S.recvMvcc m) ws) $$ [Hpost HwM]
        · iapply BigSepM.bigSepM_wand $$ Hpost
          iapply BigSepM.bigSepM_impl $$ HwM
          iintro !> %X %ws' %HX Hw' Hs
          iapply Hw' $$ %wr Hs
        ihave Hels := client.bigSepM_join_inj (fun ws => client.wsElem V G n γs (S.recvMvcc m) ws) U S.M
          hU hinj $$ [HelM HelR]
        · iframe
        iunfold respFields at Hrf
        icases Hrf with ⟨%Hhn', Hhdr, Hwid, Hcr, Hca, Hcomp, Hcrs, Hfr, Hev⟩
        wp_auto
        wp_for_post
        iexists bo, γs, b, n, _, Dn, cd', rc, γrc, csm
        simp only [named]
        iframe closeErr cur backoff wc cancelSet Hrc Hrcb Hcws Hspec
        unfold client.runCore
        iexists S.recvMvcc m, U, rcv ++ [p], mref, s, e
        have r0 : (S.recvMvcc m).Dm = S.Dm ++ [m] := rfl
        have r1 : (S.recvMvcc m).ansd = S.ansd := rfl
        have r2 : (S.recvMvcc m).regs = S.regs := rfl
        have r3 : (S.recvMvcc m).M = S.M := rfl
        have r4 : (S.recvMvcc m).CL = S.CL := rfl
        have r5 : (S.recvMvcc m).l = S.l := rfl
        have r6 : (S.recvMvcc m).L = S.L := rfl
        have r7 : (S.recvMvcc m).CS = S.CS := rfl
        rw [r0, r1, r2, r3, r4, r5, r6, r7]
        iframe
        iframe #
        isplitr
        · ipureintro; simp only [List.length_append, List.length_singleton]; omega
        isplitl []
        · unfold v3rpc.downLbW; iexact HLlb
        isplitr
        · ipureintro; exact Hg1
        imodintro
        iapply BigSepL.bigSepL_singleton.2
        unfold client.respInfo; rw [hsrc]; iexact Hrok
      have hlive : v3rpc.idLive S.Dm ρ.id := Hlive hid
      cases hMX : S.M !! ρ.id with
      | none =>
        have hnb : ¬ client.isBroadcast m := fun h => by
          obtain ⟨-, -, -, -, -, hw⟩ := h; rw [hid0] at hw; exact hid hw
        ihave Hhw : iprop(|==> (⌜m.evs = []⌝ -∗ hdrAt h m.hdr.revision)) $$ [Hhrev]
        · by_cases hne : m.evs = []
          · ipersist Hhrev
            imodintro
            iintro %-
            unfold hdrAt; iright
            iframe Hhrev
            ipureintro; exact Hhn
          · imodintro; iintro %he; exact absurd he hne
        imod Hhw
        wp_apply wp_dispatch V G.wgs p (DFrac.own 1) m h sl (List.zipWith client.evModelOf ρ.evs kvs)
          mref S.M (DFrac.own 1) (DFrac.own 1) (fun _ => client.dummyWsPrm G G.γr) (fun _ => [])
          (fun _ => client.dummyDn G) G.γend n
          $$ [Hrf Hhw Hsub Hm Hgen] as %b ⟨Hrf, Hsub, Hm, Hgen, Hpost⟩
        · iframe
          iframe #
          isplitr
          · ipureintro; simp [Hkvl, hev0]
          rw [if_neg (by simpa using hnb), hid0, hMX]
          itrivial
        irevert Hpost
        rw [if_neg (by simpa using hnb), hid0, hMX]
        iintro %Hb
        subst Hb
        wp_auto
        iunfold respFields at Hrf
        icases Hrf with ⟨%Hhn', Hhdr, Hwid, Hcr, Hca, Hcomp, Hcrs, Hfr, Hev⟩
        wp_auto
        wp_apply wp_map_lookup2 $$ Hcsm as Hcsm
        rw [hid0]
        have hXr : ρ.id ∈ S.regs := by
          obtain ⟨mc, hmc, hs, hw, hc, hca⟩ := client.idLive_exists hlive
          rw [← hw]; exact HgOk.2.2.2.2.2.2.2.2.2.2.2.2 mc hmc hs hc hca
        obtain ⟨Hg1, Hph1⟩ := client.recvMvcc_ok HgOk hsrc (fun _ => hlive)
        ihave Hels := BigSepM.bigSepM_impl
            (Ψ := fun ws (_ : Unit) => client.wsElem V G n γs (S.recvMvcc m) ws) $$ Hels []
        · iintro !> %ws' %u %Hws' Hw'
          iapply (client.wsElem_recv_other V G n γs (S := S) (S' := S.recvMvcc m) ws' m ρ hsrc rfl
            (fun X h e => by subst e; have h1 := h.1; rw [hMX] at h1; cases h1)
            (fun ph h => Hph1 ws' ph h) rfl) $$ [Hw']
          iframe; iframe #
        cases hCS : S.CS !! ρ.id with
        | some u =>
          simp only [Option.isSome_some, _root_.decide_true]
          wp_auto
          wp_for_post
          iexists bo, γs, b, n, _, Dn, cd', rc, γrc, csm
          simp only [named]
          iframe closeErr cur backoff wc cancelSet Hrc Hrcb Hcws Hspec
          unfold client.runCore
          iexists S.recvMvcc m, U, rcv ++ [p], mref, s, e
          have r0 : (S.recvMvcc m).Dm = S.Dm ++ [m] := rfl
          have r1 : (S.recvMvcc m).ansd = S.ansd := rfl
          have r2 : (S.recvMvcc m).regs = S.regs := rfl
          have r3 : (S.recvMvcc m).M = S.M := rfl
          have r4 : (S.recvMvcc m).CL = S.CL := rfl
          have r5 : (S.recvMvcc m).l = S.l := rfl
          have r6 : (S.recvMvcc m).L = S.L := rfl
          have r7 : (S.recvMvcc m).CS = S.CS := rfl
          rw [r0, r1, r2, r3, r4, r5, r6, r7]
          iframe
          iframe #
          isplitr
          · ipureintro; simp only [List.length_append, List.length_singleton]; omega
          isplitl []
          · unfold v3rpc.downLbW; iexact HLlb
          isplitr
          · ipureintro; exact Hg1
          imodintro
          iapply BigSepL.bigSepL_singleton.2
          unfold client.respInfo; rw [hsrc]; iexact Hrok
        | none =>
          simp only [Option.isSome_none, Bool.false_eq_true, decide_false]
          wp_auto
          wp_apply wp_mapInsert $$ Hcsm as Hcsm
          rename_i crp
          irename : (crp ↦ (_ : etcdserverpb.WatchRequest_CancelRequest) : IProp GF) => Hcr'
          imod client.cancelReq_send «$v0_ptr» crp «$r0_ptr» ρ.id
            $$ [«$v0» Hcr' «$r0»] with Hsend
          · iframe
          wp_apply wp_zapInt64 as %f1 -
          wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
          isplitr
          · ipureintro; rfl
          iintro %fsl ⟨-, -⟩
          wp_auto
          wp_apply wp_Debug V.lg _ _ $$ []
          · iframe #; ipureintro; exact Hlg
          wp_apply HSend $$ %S.L %«$r0_ptr» %(.cancel ρ.id) [Hstok Hsend] as %err ⟨-, Hres'⟩
          · iframe
            unfold v3rpc.watchUp v3rpc.watchReqOk
            isplitr <;> itrivial
          ihave ⟨%L', %HL', Hstok⟩ : iprop(∃ L' : List v3rpc.WatchReqM,
              ⌜L' = S.L ∨ L' = S.L ++ [.cancel ρ.id]⌝ ∗ cliSendTok (Req := v3rpc.pbWatchRequest) γs L')
              $$ [Hres']
          · icases Hres' with (⟨-, Htok⟩ | ⟨-, %L', %HL', Htok⟩)
            · iexists _; iframe; ipureintro; right; rfl
            · iexists L'; iframe; ipureintro; exact HL'
          cases err with
          | nil =>
            wp_auto
            wp_for_post
            iexists bo, γs, b, n, _, Dn, cd', rc, γrc, csm
            simp only [named]
            iframe closeErr cur backoff wc cancelSet Hrc Hrcb Hcws Hspec
            obtain ⟨Hg2, Hph2⟩ := client.cancel_ok (S := S.recvMvcc m) (U := U) Hg1 hXr HL'
            ihave Hels := BigSepM.bigSepM_impl
                (Ψ := fun ws (_ : Unit) => client.wsElem V G n γs ((S.recvMvcc m).sentCancel ρ.id L') ws) $$ Hels []
            · iintro !> %ws' %u %Hws' Hw'
              iapply (client.wsElem_mono V G n γs (S := S.recvMvcc m) (S' := (S.recvMvcc m).sentCancel ρ.id L') ws' rfl
                (fun ph' h => Hph2 ws' ph' h
                  (fun X' e => by
                    subst e; intro eX; subst eX
                    apply h.2.2.2.2.2.1
                    simp only [client.RunSt.recvMvcc]
                    rw [client.idLive_snoc, if_neg (fun hc => by rw [hsrc] at hc; cases hc.1)]
                    exact hlive)
                  (fun e => by subst e; have h1 : S.M !! ρ.id = some ws' := h.1; rw [hMX] at h1; cases h1))
                (fun X hph => client.cancels_of_snoc (.cancel ρ.id) X (fun e => by
                  cases e; have h1 : S.M !! ρ.id = some ws' := hph.1; rw [hMX] at h1; cases h1) HL')) $$ Hw'
            unfold client.runCore
            iexists (S.recvMvcc m).sentCancel ρ.id L', U, rcv ++ [p], mref, s, e
            have r0 : ((S.recvMvcc m).sentCancel ρ.id L').Dm = S.Dm ++ [m] := rfl
            have r1 : ((S.recvMvcc m).sentCancel ρ.id L').ansd = S.ansd := rfl
            have r2 : ((S.recvMvcc m).sentCancel ρ.id L').regs = S.regs := rfl
            have r3 : ((S.recvMvcc m).sentCancel ρ.id L').M = S.M := rfl
            have r4 : ((S.recvMvcc m).sentCancel ρ.id L').CL = S.CL := rfl
            have r5 : ((S.recvMvcc m).sentCancel ρ.id L').l = S.l := rfl
            have r6 : ((S.recvMvcc m).sentCancel ρ.id L').L = L' := rfl
            have r7 : ((S.recvMvcc m).sentCancel ρ.id L').CS = GMap.insert ρ.id () S.CS := rfl
            rw [r0, r1, r2, r3, r4, r5, r6, r7]
            iframe
            iframe #
            isplitr
            · ipureintro; simp only [List.length_append, List.length_singleton]; omega
            isplitl []
            · unfold v3rpc.downLbW; iexact HLlb
            isplitr
            · ipureintro; exact Hg2
            imodintro
            iapply BigSepL.bigSepL_singleton.2
            unfold client.respInfo; rw [hsrc]; iexact Hrok
          | ok ei =>
            wp_auto
            wp_apply wp_zapInt64 as %f1 -
            wp_apply wp_zapError as %f2 -
            wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
            isplitr
            · ipureintro; rfl
            iintro %fsl ⟨-, -⟩
            wp_auto
            wp_apply wp_Debug V.lg _ _ $$ []
            · iframe #; ipureintro; exact Hlg
            wp_for_post
            iexists bo, γs, b, n, _, Dn, cd', rc, γrc, csm
            simp only [named]
            iframe closeErr cur backoff wc cancelSet Hrc Hrcb Hcws Hspec
            obtain ⟨Hg2, Hph2⟩ := client.cancel_ok (S := S.recvMvcc m) (U := U) Hg1 hXr HL'
            ihave Hels := BigSepM.bigSepM_impl
                (Ψ := fun ws (_ : Unit) => client.wsElem V G n γs ((S.recvMvcc m).sentCancel ρ.id L') ws) $$ Hels []
            · iintro !> %ws' %u %Hws' Hw'
              iapply (client.wsElem_mono V G n γs (S := S.recvMvcc m) (S' := (S.recvMvcc m).sentCancel ρ.id L') ws' rfl
                (fun ph' h => Hph2 ws' ph' h
                  (fun X' e => by
                    subst e; intro eX; subst eX
                    apply h.2.2.2.2.2.1
                    simp only [client.RunSt.recvMvcc]
                    rw [client.idLive_snoc, if_neg (fun hc => by rw [hsrc] at hc; cases hc.1)]
                    exact hlive)
                  (fun e => by subst e; have h1 : S.M !! ρ.id = some ws' := h.1; rw [hMX] at h1; cases h1))
                (fun X hph => client.cancels_of_snoc (.cancel ρ.id) X (fun e => by
                  cases e; have h1 : S.M !! ρ.id = some ws' := hph.1; rw [hMX] at h1; cases h1) HL')) $$ Hw'
            unfold client.runCore
            iexists (S.recvMvcc m).sentCancel ρ.id L', U, rcv ++ [p], mref, s, e
            have r0 : ((S.recvMvcc m).sentCancel ρ.id L').Dm = S.Dm ++ [m] := rfl
            have r1 : ((S.recvMvcc m).sentCancel ρ.id L').ansd = S.ansd := rfl
            have r2 : ((S.recvMvcc m).sentCancel ρ.id L').regs = S.regs := rfl
            have r3 : ((S.recvMvcc m).sentCancel ρ.id L').M = S.M := rfl
            have r4 : ((S.recvMvcc m).sentCancel ρ.id L').CL = S.CL := rfl
            have r5 : ((S.recvMvcc m).sentCancel ρ.id L').l = S.l := rfl
            have r6 : ((S.recvMvcc m).sentCancel ρ.id L').L = L' := rfl
            have r7 : ((S.recvMvcc m).sentCancel ρ.id L').CS = GMap.insert ρ.id () S.CS := rfl
            rw [r0, r1, r2, r3, r4, r5, r6, r7]
            iframe
            iframe #
            isplitr
            · ipureintro; simp only [List.length_append, List.length_singleton]; omega
            isplitl []
            · unfold v3rpc.downLbW; iexact HLlb
            isplitr
            · ipureintro; exact Hg2
            imodintro
            iapply BigSepL.bigSepL_singleton.2
            unfold client.respInfo; rw [hsrc]; iexact Hrok
      | some wsx =>
        have hnb : ¬ client.isBroadcast m := fun h => by
          obtain ⟨-, -, -, -, -, hw⟩ := h; rw [hid0] at hw; exact hid hw
        have hU : U !! wsx = some () := HgOk.1 ρ.id wsx hMX
        icases (BigSepM.bigSepM_delete hU).1 $$ Hels with ⟨Hw, Hels⟩
        iunfold client.wsElem at Hw
        icases Hw with ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest, #Hnc, Hlife⟩
        subst HPws
        have hlive' : v3rpc.idLive (S.Dm ++ [m]) ρ.id := by
          rw [client.idLive_snoc, if_neg (fun h => by rw [hsrc] at h; cases h.1)]; exact hlive
        -- its phase: registered under the response's id
        have hph : ph = WPh.reg ρ.id := by
          cases ph with
          | queued si => exact absurd hMX (Hph.1 ρ.id)
          | orphan => exact absurd hMX (Hph.1 ρ.id)
          | closed => exact absurd hMX (Hph.1 ρ.id)
          | closedRun X => exact absurd hMX (Hph.1.2.1 ρ.id)
          | reg X =>
            have hX : X = ρ.id := HgOk.2.1 X ρ.id P.ws Hph.1 hMX
            rw [hX]
        subst hph
        iunfold client.wsRest at Hrest
        icases Hrest with ⟨%B, %w, %rg, %fcs, %lo, %sent, %C, %HB, #HsoB, #Hrg, Hprod, Hauth, Hst, Hc2⟩
        ihave #HP' := HP
        iunfold wsIs at HP'
        icases HP' with ⟨-, -, -, -, -, -, %HPpure, #Hso⟩
        ihave #HDw : v3rpc.downLbW γs S.Dm $$ []
        · unfold v3rpc.downLbW; iexact HDlb
        ihave #Hevs' : iprop([∗list] x ∈ ps.zip ρ.evs, mvcc.evIs x.1 x.2) $$ []
        · rw [← hev0]; iexact Hevs
        ihave Hpre := client.reg_pre V γs P B HB S.Dm S.Dm.length m ρ rs w rg fcs lo sent C h sl ps kvs
            hsrc hev0 ⟨hcomp0, hca0, hcr0⟩ Hfilt (by rw [← hev0]; exact Hpslen) Hkvl HPpure.2.1 Hpre.2
            Hpre.1 Hhn rfl HPpure.2.2 hlive hid $$ [Hauth Hst Hhrev Hc2]
        · iframe; iframe #
        imod Hpre with ⟨%es, %C', %C2, #Hes, %Hesl, Hhw, Hauth, Hcap, Hst, Hpend⟩
        simp only [WPh.isOrphan]
        icases client.wsLife_cap V G n P $$ Hlife with ⟨%d, Hdc, Hback⟩
        wp_apply wp_dispatch V G.wgs p (DFrac.own 1) m h sl es mref S.M (DFrac.own 1) (DFrac.own 1)
          (fun _ => P) (fun _ => sent) (fun _ => d) G.γend n
          $$ [Hrf Hhw Hsub Hm Hgen Hprod Hcap Hdc] as %b ⟨Hrf, Hsub, Hm, Hgen, Hpost⟩
        · iframe
          iframe #
          isplitr
          · ipureintro; exact Hesl
          rw [if_neg (by simpa using hnb), hid0, hMX]
          isplitr
          · ipureintro; rfl
          unfold sendCap
          iframe
          iframe #
        irevert Hpost
        rw [if_neg (by simpa using hnb), hid0, hMX]
        iintro ⟨%wr, Hpost⟩
        icases client.post_gx V P sent wr b d G.γend n $$ Hpost with ⟨Hpost, #Hxb⟩
        icases client.reg_post V γs P B HB S.Dm m ρ.id w rg fcs lo sent C' C2 b wr d G.γend n
          $$ [Hauth Hst Hpend Hpost] with ⟨Hrest, Hdc⟩
        · iframe; iframe #
        ihave HlifeR : iprop(client.wsLife V G n P false) $$ [Hdc Hback]
        · iunfold dnCap at Hdc
          icases Hdc with ⟨Hdc, -⟩
          iapply Hback $$ Hdc
        obtain ⟨Hg1, Hph1⟩ := client.recvMvcc_ok HgOk hsrc (fun _ => hlive)
        ihave Hels := BigSepM.bigSepM_impl
            (Ψ := fun ws (_ : Unit) => client.wsElem V G n γs (S.recvMvcc m) ws) $$ Hels []
        · iintro !> %ws' %u %Hws' Hw'
          have Hws'' : (GMap.delete P.ws U) !! ws' = some u := Hws'
          have hne : ws' ≠ P.ws := by
            intro e; subst e; rw [GMap.lookup_delete] at Hws''; cases Hws''
          iapply (client.wsElem_recv_other V G n γs (S := S) (S' := S.recvMvcc m) ws' m ρ hsrc rfl
            (fun X h e => by
              subst e; have h1 : S.M !! ρ.id = some ws' := h.1; rw [hMX] at h1
              exact hne (Option.some.inj h1).symm)
            (fun ph h => Hph1 ws' ph h) rfl) $$ [Hw']
          iframe; iframe #
        iunfold respFields at Hrf
        icases Hrf with ⟨%Hhn', Hhdr, Hwid, Hcr, Hca, Hcomp, Hcrs, Hfr, Hev⟩
        cases b with
        | true =>
          ihave Hels := (BigSepM.bigSepM_delete (Φ := fun ws (_ : Unit) =>
              client.wsElem V G n γs (S.recvMvcc m) ws) (m := U) (i := P.ws) (x := ()) hU).2 $$ [Hels Hid Hrest HlifeR]
          · iframe Hels
            unfold client.wsElem
            iexists P, .reg ρ.id
            isplitr
            · ipureintro; exact ⟨rfl, Hph1 P.ws _ Hph⟩
            iframe HP
            iframe
            iapply client.noCancelOk_mono (S := S) (S' := S.recvMvcc m) P _ (fun _ _ _ hi => hi) $$ Hnc
          wp_auto
          wp_for_post
          iexists bo, γs, b, n, _, Dn, cd', rc, γrc, csm
          simp only [named]
          iframe closeErr cur backoff wc cancelSet Hrc Hrcb Hcws Hspec
          unfold client.runCore
          iexists S.recvMvcc m, U, rcv ++ [p], mref, s, e
          have r0 : (S.recvMvcc m).Dm = S.Dm ++ [m] := rfl
          have r1 : (S.recvMvcc m).ansd = S.ansd := rfl
          have r2 : (S.recvMvcc m).regs = S.regs := rfl
          have r3 : (S.recvMvcc m).M = S.M := rfl
          have r4 : (S.recvMvcc m).CL = S.CL := rfl
          have r5 : (S.recvMvcc m).l = S.l := rfl
          have r6 : (S.recvMvcc m).L = S.L := rfl
          have r7 : (S.recvMvcc m).CS = S.CS := rfl
          rw [r0, r1, r2, r3, r4, r5, r6, r7]
          iframe
          iframe #
          isplitr
          · ipureintro; simp only [List.length_append, List.length_singleton]; omega
          isplitl []
          · unfold v3rpc.downLbW; iexact HLlb
          isplitr
          · ipureintro; exact Hg1
          imodintro
          iapply BigSepL.bigSepL_singleton.2
          unfold client.respInfo; rw [hsrc]; iexact Hrok
        | false =>
          -- the dispatch failed: the substream stopped (`γx`), so cancelling its id is fine
          icases Hxb with (%hbf | #Hx)
          · cases hbf
          wp_auto
          wp_apply wp_map_lookup2 $$ Hcsm as Hcsm
          rw [hid0]
          have hXr : ρ.id ∈ S.regs := Hph.2.2.2.1
          cases hCS : S.CS !! ρ.id with
          | some u =>
            simp only [Option.isSome_some, _root_.decide_true]
            wp_auto
            wp_for_post
            iexists bo, γs, b, n, _, Dn, cd', rc, γrc, csm
            simp only [named]
            iframe closeErr cur backoff wc cancelSet Hrc Hrcb Hcws Hspec
            ihave Hels := (BigSepM.bigSepM_delete (Φ := fun ws (_ : Unit) =>
                client.wsElem V G n γs (S.recvMvcc m) ws) (m := U) (i := P.ws) (x := ()) hU).2
                $$ [Hels Hid Hrest HlifeR]
            · iframe Hels
              unfold client.wsElem
              iexists P, .reg ρ.id
              isplitr
              · ipureintro; exact ⟨rfl, Hph1 P.ws _ Hph⟩
              iframe HP
              iframe
              unfold client.noCancelOk; iright; iexact Hx
            unfold client.runCore
            iexists S.recvMvcc m, U, rcv ++ [p], mref, s, e
            have r0 : (S.recvMvcc m).Dm = S.Dm ++ [m] := rfl
            have r1 : (S.recvMvcc m).ansd = S.ansd := rfl
            have r2 : (S.recvMvcc m).regs = S.regs := rfl
            have r3 : (S.recvMvcc m).M = S.M := rfl
            have r4 : (S.recvMvcc m).CL = S.CL := rfl
            have r5 : (S.recvMvcc m).l = S.l := rfl
            have r6 : (S.recvMvcc m).L = S.L := rfl
            have r7 : (S.recvMvcc m).CS = S.CS := rfl
            rw [r0, r1, r2, r3, r4, r5, r6, r7]
            iframe
            iframe #
            isplitr
            · ipureintro; simp only [List.length_append, List.length_singleton]; omega
            isplitl []
            · unfold v3rpc.downLbW; iexact HLlb
            isplitr
            · ipureintro; exact Hg1
            imodintro
            iapply BigSepL.bigSepL_singleton.2
            unfold client.respInfo; rw [hsrc]; iexact Hrok
          | none =>
            simp only [Option.isSome_none, Bool.false_eq_true, decide_false]
            wp_auto
            wp_apply wp_mapInsert $$ Hcsm as Hcsm
            rename_i crp
            irename : (crp ↦ (_ : etcdserverpb.WatchRequest_CancelRequest) : IProp GF) => Hcr'
            imod client.cancelReq_send «$v0_ptr» crp «$r0_ptr» ρ.id
              $$ [«$v0» Hcr' «$r0»] with Hsend
            · iframe
            wp_apply wp_zapInt64 as %f1 -
            wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
            isplitr
            · ipureintro; rfl
            iintro %fsl ⟨-, -⟩
            wp_auto
            wp_apply wp_Debug V.lg _ _ $$ []
            · iframe #; ipureintro; exact Hlg
            wp_apply HSend $$ %S.L %«$r0_ptr» %(.cancel ρ.id) [Hstok Hsend] as %err ⟨-, Hres'⟩
            · iframe
              unfold v3rpc.watchUp v3rpc.watchReqOk
              isplitr <;> itrivial
            ihave ⟨%L', %HL', Hstok⟩ : iprop(∃ L' : List v3rpc.WatchReqM,
                ⌜L' = S.L ∨ L' = S.L ++ [.cancel ρ.id]⌝ ∗ cliSendTok (Req := v3rpc.pbWatchRequest) γs L')
                $$ [Hres']
            · icases Hres' with (⟨-, Htok⟩ | ⟨-, %L', %HL', Htok⟩)
              · iexists _; iframe; ipureintro; right; rfl
              · iexists L'; iframe; ipureintro; exact HL'
            cases err with
            | nil =>
              wp_auto
              wp_for_post
              iexists bo, γs, b, n, _, Dn, cd', rc, γrc, csm
              simp only [named]
              iframe closeErr cur backoff wc cancelSet Hrc Hrcb Hcws Hspec
              obtain ⟨Hg2, Hph2⟩ := client.cancel_ok (S := S.recvMvcc m) (U := U) Hg1 hXr HL'
              ihave Hels := BigSepM.bigSepM_impl
                  (Ψ := fun ws (_ : Unit) => client.wsElem V G n γs ((S.recvMvcc m).sentCancel ρ.id L') ws) $$ Hels []
              · iintro !> %ws' %u %Hws' Hw'
                have Hws'' : (GMap.delete P.ws U) !! ws' = some u := Hws'
                have hne : ws' ≠ P.ws := by
                  intro e; subst e; rw [GMap.lookup_delete] at Hws''; cases Hws''
                iapply (client.wsElem_mono V G n γs (S := S.recvMvcc m) (S' := (S.recvMvcc m).sentCancel ρ.id L') ws' rfl
                  (fun ph' h => Hph2 ws' ph' h
                    (fun X' e => by
                      subst e; intro eX; subst eX; exact h.2.2.2.2.2.1 hlive')
                    (fun _ => hCS))
                  (fun X hph => client.cancels_of_snoc (.cancel ρ.id) X (fun e => by
                    cases e
                    have h1 : S.M !! ρ.id = some ws' := hph.1
                    rw [hMX] at h1; cases h1
                    exact absurd rfl hne) HL')) $$ Hw'
              ihave Hels := (BigSepM.bigSepM_delete (Φ := fun ws (_ : Unit) =>
                  client.wsElem V G n γs ((S.recvMvcc m).sentCancel ρ.id L') ws) (m := U) (i := P.ws)
                  (x := ()) hU).2 $$ [Hels Hid Hrest HlifeR]
              · iframe Hels
                unfold client.wsElem
                iexists P, .reg ρ.id
                isplitr
                · ipureintro
                  exact ⟨rfl, Hph2 P.ws _ (Hph1 P.ws _ Hph) (fun X' e => by cases e) (fun _ => hCS)⟩
                iframe HP
                iframe
                unfold client.noCancelOk; iright; iexact Hx
              unfold client.runCore
              iexists (S.recvMvcc m).sentCancel ρ.id L', U, rcv ++ [p], mref, s, e
              have r0 : ((S.recvMvcc m).sentCancel ρ.id L').Dm = S.Dm ++ [m] := rfl
              have r1 : ((S.recvMvcc m).sentCancel ρ.id L').ansd = S.ansd := rfl
              have r2 : ((S.recvMvcc m).sentCancel ρ.id L').regs = S.regs := rfl
              have r3 : ((S.recvMvcc m).sentCancel ρ.id L').M = S.M := rfl
              have r4 : ((S.recvMvcc m).sentCancel ρ.id L').CL = S.CL := rfl
              have r5 : ((S.recvMvcc m).sentCancel ρ.id L').l = S.l := rfl
              have r6 : ((S.recvMvcc m).sentCancel ρ.id L').L = L' := rfl
              have r7 : ((S.recvMvcc m).sentCancel ρ.id L').CS = GMap.insert ρ.id () S.CS := rfl
              rw [r0, r1, r2, r3, r4, r5, r6, r7]
              iframe
              iframe #
              isplitr
              · ipureintro; simp only [List.length_append, List.length_singleton]; omega
              isplitl []
              · unfold v3rpc.downLbW; iexact HLlb
              isplitr
              · ipureintro; exact Hg2
              imodintro
              iapply BigSepL.bigSepL_singleton.2
              unfold client.respInfo; rw [hsrc]; iexact Hrok
            | ok ei =>
              wp_auto
              wp_apply wp_zapInt64 as %f1 -
              wp_apply wp_zapError as %f2 -
              wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
              isplitr
              · ipureintro; rfl
              iintro %fsl ⟨-, -⟩
              wp_auto
              wp_apply wp_Debug V.lg _ _ $$ []
              · iframe #; ipureintro; exact Hlg
              wp_for_post
              iexists bo, γs, b, n, _, Dn, cd', rc, γrc, csm
              simp only [named]
              iframe closeErr cur backoff wc cancelSet Hrc Hrcb Hcws Hspec
              obtain ⟨Hg2, Hph2⟩ := client.cancel_ok (S := S.recvMvcc m) (U := U) Hg1 hXr HL'
              ihave Hels := BigSepM.bigSepM_impl
                  (Ψ := fun ws (_ : Unit) => client.wsElem V G n γs ((S.recvMvcc m).sentCancel ρ.id L') ws) $$ Hels []
              · iintro !> %ws' %u %Hws' Hw'
                have Hws'' : (GMap.delete P.ws U) !! ws' = some u := Hws'
                have hne : ws' ≠ P.ws := by
                  intro e; subst e; rw [GMap.lookup_delete] at Hws''; cases Hws''
                iapply (client.wsElem_mono V G n γs (S := S.recvMvcc m) (S' := (S.recvMvcc m).sentCancel ρ.id L') ws' rfl
                  (fun ph' h => Hph2 ws' ph' h
                    (fun X' e => by
                      subst e; intro eX; subst eX; exact h.2.2.2.2.2.1 hlive')
                    (fun _ => hCS))
                  (fun X hph => client.cancels_of_snoc (.cancel ρ.id) X (fun e => by
                    cases e
                    have h1 : S.M !! ρ.id = some ws' := hph.1
                    rw [hMX] at h1; cases h1
                    exact absurd rfl hne) HL')) $$ Hw'
              ihave Hels := (BigSepM.bigSepM_delete (Φ := fun ws (_ : Unit) =>
                  client.wsElem V G n γs ((S.recvMvcc m).sentCancel ρ.id L') ws) (m := U) (i := P.ws)
                  (x := ()) hU).2 $$ [Hels Hid Hrest HlifeR]
              · iframe Hels
                unfold client.wsElem
                iexists P, .reg ρ.id
                isplitr
                · ipureintro
                  exact ⟨rfl, Hph2 P.ws _ (Hph1 P.ws _ Hph) (fun X' e => by cases e) (fun _ => hCS)⟩
                iframe HP
                iframe
                unfold client.noCancelOk; iright; iexact Hx
              unfold client.runCore
              iexists (S.recvMvcc m).sentCancel ρ.id L', U, rcv ++ [p], mref, s, e
              have r0 : ((S.recvMvcc m).sentCancel ρ.id L').Dm = S.Dm ++ [m] := rfl
              have r1 : ((S.recvMvcc m).sentCancel ρ.id L').ansd = S.ansd := rfl
              have r2 : ((S.recvMvcc m).sentCancel ρ.id L').regs = S.regs := rfl
              have r3 : ((S.recvMvcc m).sentCancel ρ.id L').M = S.M := rfl
              have r4 : ((S.recvMvcc m).sentCancel ρ.id L').CL = S.CL := rfl
              have r5 : ((S.recvMvcc m).sentCancel ρ.id L').l = S.l := rfl
              have r6 : ((S.recvMvcc m).sentCancel ρ.id L').L = L' := rfl
              have r7 : ((S.recvMvcc m).sentCancel ρ.id L').CS = GMap.insert ρ.id () S.CS := rfl
              rw [r0, r1, r2, r3, r4, r5, r6, r7]
              iframe
              iframe #
              isplitr
              · ipureintro; simp only [List.length_append, List.length_singleton]; omega
              isplitl []
              · unfold v3rpc.downLbW; iexact HLlb
              isplitr
              · ipureintro; exact Hg2
              imodintro
              iapply BigSepL.bigSepL_singleton.2
              unfold client.respInfo; rw [hsrc]; iexact Hrok

    -- errc
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, G.errc, G.γerr
      isplit
      · ipureintro; rfl
      isplit
      · iapply is_bag_is_chan $$ Herrb
      iapply bag_recv_au G.γerr G.errc (errP G.γr G.γep) _ $$ [$Hlc1 $Hlc2] Herrb
      inext
      iintro %err Herr
      iunfold errP at Herr
      icases Herr with ⟨%Hen, #Herrk, #Hse, Hpback⟩
      wp_auto
      wp_apply +noauto wp_isHaltErr G.ctx G.cd err $$ [] as %bh %Hbh
      · iframe #
      cases bh
      · -- (D24) not a halting error: no leader, or a reconnection
        wp_auto_lc 1
        ihave #Hcea' := Hcea
        iunfold ctxErrClientAllW at Hcea'
        ihave #Hcec := Hcea' $$ %G.ctx %G.cd HGctx
        ihave %Hce : iprop(⌜err ≠ GoInterface.nil → clientErr err⌝) $$ []
        · icases Herrk with (Hcs | #Heo)
          · iunfold cliStreamErr at Hcs
            icases Hcs with ⟨%Hc, -, -⟩
            ipureintro; exact fun _ => Hc.2
          · iunfold eofOk at Heof
            ihave ⟨%Hc, -⟩ := Heof $$ %err Heo
            ipureintro; exact fun _ => Hc.2
        wp_apply wp_ctxErr G.ctx G.cd err $$ [] as %err' ⟨%Herr', #Hse'⟩
        · iframe #; ipureintro; exact Hce
        (try wp_auto)
        ihave #Hrp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
        · iPkgInit
        ihave ⟨%xnl, #Hnl⟩ := errNoLeader_of_init $$ Hrp
        ihave #Herrp : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
        · iPkgInit
        (try wp_auto)
        wp_apply (wp_isStatus err' _ (Or.inl ⟨xnl, rfl⟩)) $$ [] as %bnl -
        · iframe #
        cases bnl
        rotate_left
        · -- no leader: `run` stops
          (try wp_auto)
          wp_for_post
          isplitr
          · ipureintro; rfl
          iapply client.runExit_of_core V G γs b n clm csm closeErr_ptr err
          iframe
          iframe #
        (try wp_auto)
        wp_apply wp_backoff G.wgs G.ctx G.cd bo err $$ [] as %bo' -
        · iframe #
        (try wp_auto)
        -- the reconnection (D24): the old stream's epoch ends at `respc`'s position
        iunfold client.runCore at Hcore
        icases Hcore with ⟨%S, %U, %rcv, %mref, %s, %e, Hclm, Hcsm, Hsub, Hm, Hres, Hs, HcF, #He,
          Hstok, Hrcons, %Hrcv, Hepst, -, %HgOk, -, -, -, Hwsa, Hels, Had, Htt, Hdn, Hgen⟩
        iunfold prodBack at Hpback
        icases Hpback with ⟨%e0, %b0, %γs0, %γc0, %sent, #Hi0, Hprod, Hcnt, %Hb0⟩
        imod sspsc_sync G.γr _ _ _ sent rcv $$ Hrspsc Hlc1 Hprod Hrcons with ⟨%Hsr, Hprod, Hrcons⟩
        subst Hsr
        ihave ⟨%eps, Hep, Hend⟩ := client.epochSt_close G γs b e0 b0 γs0 γc0 sent.length (by omega)
          $$ [Hepst Hi0 Hcnt]
        · iframe; iframe #
        wp_apply wp_newWC V G callSl mref s rc γrc n sent eps γs S U
          $$ [Hsub Hm Hres Hs Hrc Hrcb Hgen Hprod Hep Hwsa Hels Had Htt]
          as %wcv' %err2 ⟨%m', %s', %rc', %γrc', %l', Hsub, Hm', Hres, Hs', Hrc, Hrcb, Hgen,
            %HgOk', Hwsa, Hels', Had, Htt, Hcase⟩
        · iframe #; iframe
          ipureintro; exact HgOk
        icases Hcase with (⟨%Herr2, %γs', %Dn', %cd2, %γc', #Hcws2, Hstok2, #Hspec2, Hep⟩ |
          ⟨⟨%Hwcn, %Herr2⟩, #Hse2, -, -⟩)
        rotate_left
        · -- the new stream failed: `run` stops
          cases err2 with
          | nil => exact absurd rfl Herr2
          | ok ei2 =>
          wp_auto
          wp_for_post
          isplitr
          · ipureintro; rfl
          unfold client.runExit
          iexists γs, S.reconnect l', U, GoInterface.ok ei2, e, m', s', n + 1
          ihave Hels' := Hels' $$ %γs
          simp only [client.RunSt.reconnect]
          iframe
          iframe #
          ipureintro; exact HgOk'
        subst Herr2
        wp_auto
        ihave Hepst := client.epochSt_open G γs' sent.length γc' eps $$ [Hep Hend]
        · iframe
        ihave Hels := Hels' $$ %γs'
        ihave #Hcws2' := Hcws2
        iunfold v3rpc.cliWatchStreamIs at Hcws2'
        iunfold cliBidiStreamIs at Hcws2'
        icases Hcws2' with ⟨%ci2, %Hci2, #HSend2, -, -, -⟩
        subst Hci2
        imod monoListLbOwn_nil (GF := GF) (A := v3rpc.WatchRespM) γs'.down with #Hlb'
        have hp0 : (S.reconnect l').pend = none := rfl
        wp_apply wp_nextResume G.wgs s' (S.reconnect l').l $$ [Hres Hs'] as %ws2 ⟨%s2, Hres, Hs, %Hws2⟩
        · iframe #; iframe
        by_cases hn2 : ws2 = null
        · simp only [hn2, _root_.decide_true, Bool.not_true]
          have hhd : ((S.reconnect l').l.dropWhile (fun x => decide (x = null))).head? = none := by
            cases hd : ((S.reconnect l').l.dropWhile (fun x => decide (x = null))).head? with
            | none => rfl
            | some x =>
              exfalso
              have hx := client.dropNull_head hd
              rw [hd] at Hws2; simp at Hws2; exact hx (Hws2 ▸ hn2)
          obtain ⟨Hg2, Hold2, -⟩ := client.resume_ok (si := none) (U := U) HgOk' hp0
            (Or.inl ⟨rfl, rfl, rfl⟩)
          ihave Hels := BigSepM.bigSepM_impl (Ψ := fun ws (_ : Unit) =>
              client.wsElem V G (n + 1) γs' ((S.reconnect l').resume (S.reconnect l').L none) ws) $$ Hels []
          · iintro !> %ws' %u %Hws' Hw'
            have Hws'' : U !! ws' = some u := Hws'
            cases u
            iapply (client.wsElem_mono V G (n + 1) γs' (S := S.reconnect l')
              (S' := (S.reconnect l').resume (S.reconnect l').L none) ws' rfl
              (fun ph h => Hold2 ws' ph Hws'' (by rw [hhd]; simp) h) (fun _ _ _ hi => hi)) $$ Hw'
          wp_auto
          wp_apply (wp_map_make1 (K := w64) (V := Unit) go.int64 (go.GoType.StructType [])) as %csm' Hcsm'
          (try wp_auto)
          wp_for_post
          iexists bo', γs', sent.length, n + 1, _, Dn', cd2, rc', γrc', csm'
          simp only [named]
          rw [show n + 2 = n + 1 + 1 from rfl]
          iframe closeErr cur backoff wc cancelSet Hrc Hrcb Hcws2 Hspec2
          unfold client.runCore
          iexists (S.reconnect l').resume (S.reconnect l').L none, U, sent, m', s2, e
          simp only [client.RunSt.resume, client.RunSt.reconnect]
          iframe
          iframe #
          isplitr
          · ipureintro; simp
          isplitr
          · unfold v3rpc.downLbW; iexact Hlb'
          isplitr
          · ipureintro; exact Hg2
          isplitr
          · iapply BigSepL.bigSepL_nil.2; itrivial
          isplitr
          · iapply BigSepL.bigSepL_nil.2; itrivial
          imodintro; iapply BigSepL.bigSepL_nil.2; itrivial
        simp only [hn2, decide_false, Bool.not_false]
        have hhd : ((S.reconnect l').l.dropWhile (fun x => decide (x = null))).head? = some ws2 := by
          cases hd : ((S.reconnect l').l.dropWhile (fun x => decide (x = null))).head? with
          | none => rw [hd] at Hws2; simp at Hws2; exact absurd Hws2 hn2
          | some x => rw [hd] at Hws2; simp at Hws2; rw [Hws2]
        have hmem2 : ws2 ∈ (S.reconnect l').l :=
          (client.mem_dropNull hn2).1 (List.mem_of_getElem? (by rw [← List.head?_eq_getElem?]; exact hhd))
        have hU2 : U !! ws2 = some () := HgOk'.2.2.1 ws2 hmem2 hn2
        icases (BigSepM.bigSepM_delete hU2).1 $$ Hels with ⟨Hw, Hels⟩
        iunfold client.wsElem at Hw
        icases Hw with ⟨%P2, %ph2, ⟨%HPws2, %Hph2⟩, #HP2, Hid2, Hrest2, #Hnc2, Hlife2⟩
        subst HPws2
        obtain ⟨si2, rfl⟩ : ∃ si2, ph2 = .queued si2 := by
          cases ph2 with
          | queued si => exact ⟨si, rfl⟩
          | reg X => exact absurd hmem2 Hph2.2.1
          | closedRun X => exact absurd hmem2 Hph2.2.1
          | orphan => exact absurd hmem2 Hph2.2.1
          | closed => exact absurd hmem2 Hph2.2.1
        icases client.queued_send V γs' (S.reconnect l').Dm P2 si2 $$ Hrest2 with ⟨%B2, %q2, Hrv2, #HsoB2, Hback2⟩
        ihave #HP2' := HP2
        iunfold wsIs at HP2'
        icases HP2' with ⟨#Hro2, -⟩
        iunfold wrRO at Hro2
        icases Hro2 with ⟨-, #Rkey, #Rend, -, #Rpn, #Rfrag, -, #Rflt, #Rflts, #Rprev⟩
        wp_take_receipt as Hrc0
        wp_apply wp_toPB (wsF P2.ws go!"initReq") P2.key P2.ed B2.rr P2.pn P2.flt
          (DFrac.own q2) B2.srr $$ [Hrv2] as %preq ⟨Hrv2, Hpsend⟩
        · iframe #; iframe
        imod mvcc.watchTokPool_take V.R.γ $$ Htoks Hrc0 with Hwt
        wp_apply HSend2 $$ %([] : List v3rpc.WatchReqM) %preq
          %(.create (createOf P2.key P2.ed B2.rr P2.pn B2.srr)) [Hstok2 Hpsend Hwt]
          as %err3 ⟨-, Hres'⟩
        · iframe
          unfold v3rpc.watchUp
          iframe
          isplitr
          · ipureintro; simp [v3rpc.watchReqOk, createOf]
          dsimp only; iframe
          simp only [createOf]; iapply client.startOk_read $$ HsoB2
        have hne2 : (S.reconnect l').l.dropWhile (fun y => decide (y = null)) ≠ [] := by
          intro e0; rw [e0] at hhd; simp at hhd
        ihave ⟨%L', %si, Hstok, %Hcase, Hupi⟩ : iprop(∃ (L' : List v3rpc.WatchReqM) (si : Option Nat),
            cliSendTok (Req := v3rpc.pbWatchRequest) γs' L' ∗
            ⌜(L' = (S.reconnect l').L ∧ si = none ∧ si = none) ∨
              ((∃ c, L' = (S.reconnect l').L ++ [.create c]) ∧ si = some (S.reconnect l').L.length ∧
                si = some (S.reconnect l').L.length ∧
                (S.reconnect l').l.dropWhile (fun y => decide (y = null)) ≠ [])⌝ ∗
            client.upAtOpt γs' si (client.createOfB P2 B2)) $$ [Hres']
        · ihave Hmk : iprop(∀ L2 : List v3rpc.WatchReqM,
              ⌜L2 = [] ∨ L2 = [] ++ [.create (createOf P2.key P2.ed B2.rr P2.pn B2.srr)]⌝ -∗
              cliSendTok (Req := v3rpc.pbWatchRequest) γs' L2 -∗
              ∃ (L' : List v3rpc.WatchReqM) (si : Option Nat),
              cliSendTok (Req := v3rpc.pbWatchRequest) γs' L' ∗
              ⌜(L' = (S.reconnect l').L ∧ si = none ∧ si = none) ∨
                ((∃ c, L' = (S.reconnect l').L ++ [.create c]) ∧ si = some (S.reconnect l').L.length ∧
                  si = some (S.reconnect l').L.length ∧
                  (S.reconnect l').l.dropWhile (fun y => decide (y = null)) ≠ [])⌝ ∗
              client.upAtOpt γs' si (client.createOfB P2 B2)) $$ []
          · iintro %L2 %HL2 Hst
            rcases HL2 with rfl | rfl
            · iexists [], none
              iframe
              isplitr
              · ipureintro; exact Or.inl ⟨rfl, rfl, rfl⟩
              unfold client.upAtOpt; itrivial
            · ihave ⟨Hst, #Hlb⟩ := cliSendTok_lb $$ Hst
              iexists _, some 0
              iframe
              isplitr
              · ipureintro
                exact Or.inr ⟨⟨_, rfl⟩, rfl, rfl, hne2⟩
              ihave Hu := upLb_at (Req := v3rpc.pbWatchRequest) γs' _ 0
                (.create (createOf P2.key P2.ed B2.rr P2.pn B2.srr)) (by simp) $$ Hlb
              unfold client.upAtOpt v3rpc.upAtW
              iunfold upAt at Hu
              iexact Hu
          icases Hres' with (⟨-, Htok⟩ | ⟨-, %L2, %HL2, Htok⟩)
          · iapply Hmk $$ %_ %(Or.inr rfl) Htok
          · iapply Hmk $$ %L2 %HL2 Htok
        obtain ⟨Hg2, Hold2, Hnew2⟩ := client.resume_ok (U := U) (L' := L') (pend' := si) (si := si)
          HgOk' hp0 Hcase
        ihave Hels := BigSepM.bigSepM_impl (Ψ := fun ws (_ : Unit) =>
            client.wsElem V G (n + 1) γs' ((S.reconnect l').resume L' si) ws) $$ Hels []
        · iintro !> %ws' %u %Hws' Hw'
          have Hws'' : (GMap.delete P2.ws U) !! ws' = some u := Hws'
          have hne : ws' ≠ P2.ws := by
            intro e; subst e; rw [GMap.lookup_delete] at Hws''; cases Hws''
          rw [GMap.lookup_delete_ne _ (Ne.symm hne)] at Hws''
          cases u
          iapply (client.wsElem_mono V G (n + 1) γs' (S := S.reconnect l')
            (S' := (S.reconnect l').resume L' si) ws' rfl
            (fun ph h => Hold2 ws' ph Hws'' (by rw [hhd]; intro e; exact hne (Option.some.inj e).symm) h)
            (fun X _ => client.create_or (by
              rcases Hcase with ⟨h, -⟩ | ⟨h, -⟩
              · exact Or.inl h
              · exact Or.inr h) X))
            $$ Hw'
        ihave Hels := (BigSepM.bigSepM_delete (Φ := fun ws (_ : Unit) =>
            client.wsElem V G (n + 1) γs' ((S.reconnect l').resume L' si) ws) (m := U) (i := P2.ws)
            (x := ()) hU2).2 $$ [Hels Hid2 Hback2 Hrv2 Hupi Hlife2]
        · iframe Hels
          unfold client.wsElem
          iexists P2, .queued si
          isplitr
          · ipureintro; exact ⟨rfl, Hnew2 P2.ws hhd hU2 _ Hph2⟩
          iframe HP2
          simp only [WPh.id]
          iframe Hid2
          simp only [client.noCancelOk, WPh.isOrphan]
          iframe Hlife2
          iapply Hback2 $$ Hrv2 Hupi
        ihave Hfin : iprop(∀ csm' : Loc, ownMap csm' (DFrac.own 1) (∅ : GMap w64 Unit) -∗
            client.runCore V G γs' sent.length (n + 1) clm csm') $$
            [Hclm Hsub Hm' Hres Hs HcF Hstok Hrcons Hepst Hwsa Hels Had Htt Hdn Hgen]
        · iintro %csm' Hcsm'
          unfold client.runCore
          iexists (S.reconnect l').resume L' si, U, sent, m', s2, e
          have r1 : ((S.reconnect l').resume L' si).L = L' := rfl
          rw [r1]
          simp only [client.RunSt.resume, client.RunSt.reconnect]
          iframe
          iframe #
          isplitr
          · ipureintro; simp
          isplitr
          · unfold v3rpc.downLbW; iexact Hlb'
          isplitr
          · ipureintro; exact Hg2
          isplitr
          · iapply BigSepL.bigSepL_nil.2; itrivial
          isplitr
          · iapply BigSepL.bigSepL_nil.2; itrivial
          imodintro; iapply BigSepL.bigSepL_nil.2; itrivial
        cases err3 with
        | nil =>
          wp_auto
          wp_apply (wp_map_make1 (K := w64) (V := Unit) go.int64 (go.GoType.StructType [])) as %csm' Hcsm'
          (try wp_auto)
          wp_for_post
          iexists bo', γs', sent.length, n + 1, _, Dn', cd2, rc', γrc', csm'
          simp only [named]
          rw [show n + 2 = n + 1 + 1 from rfl]
          iframe closeErr cur backoff wc cancelSet Hrc Hrcb Hcws2 Hspec2
          iapply Hfin $$ Hcsm'
        | ok ei3 =>
          wp_auto
          wp_apply wp_zapError as %f3 -
          wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f3]
          isplitr
          · ipureintro; rfl
          iintro %fsl ⟨-, -⟩
          wp_auto
          wp_apply wp_Debug V.lg _ _ $$ []
          · iframe #; ipureintro; exact Hlg
          (try wp_auto)
          wp_apply (wp_map_make1 (K := w64) (V := Unit) go.int64 (go.GoType.StructType [])) as %csm' Hcsm'
          (try wp_auto)
          wp_for_post
          iexists bo', γs', sent.length, n + 1, _, Dn', cd2, rc', γrc', csm'
          simp only [named]
          rw [show n + 2 = n + 1 + 1 from rfl]
          iframe closeErr cur backoff wc cancelSet Hrc Hrcb Hcws2 Hspec2
          iapply Hfin $$ Hcsm'
      wp_auto
      wp_for_post
      isplitr
      · ipureintro; rfl
      iapply client.runExit_of_core V G γs b n clm csm closeErr_ptr err
      iframe
      iframe #
    -- ctx.Done
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, dγ
      isplit
      · ipureintro; rfl
      isplit
      · iapply context.isContextDone_is_chan $$ Hdone
      iapply context.isContextDone_receive _ _ _ _ $$ Hdone
      iintro -
      wp_auto
      wp_for_post
      isplitr
      · ipureintro; rfl
      ihave #Hnil := statusErrOk_nil (GF := GF)
      iapply client.runExit_of_core V G γs b n clm csm closeErr_ptr GoInterface.nil
      iframe
      iframe #
    -- closingc
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, G.closingc,
        G.γclosing
      isplit
      · ipureintro; rfl
      isplit
      · iapply is_bag_is_chan $$ Hclb
      iapply bag_recv_au G.γclosing G.closingc (closingP V G) _ $$ [$Hlc1 $Hlc2] Hclb
      inext
      iintro %wsr Hel
      iunfold closingP at Hel
      iunfold client.runCore at Hcore
      icases Hcore with ⟨%S, %U, %rcv, %mref, %s, %e, Hclm, Hcsm, Hsub, Hm, Hres, Hs, HcF, #He,
        Hstok, Hrcons, %Hrcv, Hepst, #HDlb, %HgOk, Hans, Hids, #Hinfo, Hwsa, Hels, Had, Htt, Hdn, Hgen⟩
      ihave %HU := ghost_map_lookup $$ Hwsa Hel
      icases (BigSepM.bigSepM_delete HU).1 $$ Hels with ⟨Hw, Hels⟩
      iunfold client.wsElem at Hw
      icases Hw with ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest, #Hnc, Hlife⟩
      -- (D24) what the goroutine left in its lifetime's invariant
      iunfold client.wsLife at Hlife
      icases Hlife with ⟨%L, -, #Hli, Htk, -⟩
      iapply fupd_wp
      imod client.take_stop V G n P L wsr HPws $$ [Hlc3 Htk Hel Hgen] with ⟨Hsb, Hel, Hgen⟩
      · iframe; iframe #
      ihave Hbody : iprop(closingBody V wsr) $$ [Hsb]
      · unfold closingBody; iexists P; iframe HP Hsb; ipureintro; exact HPws
      imod ghost_map_delete $$ Hwsa Hel with Hwsa
      imodintro
      subst HPws
      obtain ⟨Hg', Hph'⟩ := client.closeWs_ok HgOk HU Hph
      ihave Hels := BigSepM.bigSepM_impl
          (Ψ := fun ws (_ : Unit) => client.wsElem V G n γs (S.closeWs P.ws ph) ws) $$ Hels []
      · iintro !> %ws' %u %Hws' Hw'
        have Hws'' : (GMap.delete P.ws U) !! ws' = some u := Hws'
        have hne : ws' ≠ P.ws := by
          intro e; subst e; rw [GMap.lookup_delete] at Hws''; cases Hws''
        have hU' : U !! ws' = some () := by
          rw [GMap.lookup_delete_ne _ (Ne.symm hne)] at Hws''; exact Hws''
        iapply (client.wsElem_mono V G n γs (S := S) (S' := S.closeWs P.ws ph) ws' rfl
          (fun ph' h => Hph' ws' ph' hne hU' h) (fun _ _ _ hi => hi)) $$ Hw'
      iunfold sliceOwn at Hs
      icases Hs with ⟨Hs, Hscap⟩
      wp_auto
      wp_apply wp_closeSub V G.wgs P.ws ph.id e (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) mref S.M s S.l
        $$ [Hbody Hid HcF Hsub Hm Hres Hs] as ⟨Hid, HcF, Hsub, Hres, Hrest2⟩
      · iframe; iframe #
      ihave ⟨Hm, Hs⟩ : iprop(ownMap mref (DFrac.own 1) (S.closeWs P.ws ph).M ∗
          s ↦* (S.closeWs P.ws ph).l) $$ [Hrest2]
      · unfold client.RunSt.closeWs
        by_cases hid : ph.id = W64 (-1)
        · irevert Hrest2
          simp only [hid, _root_.decide_true, ↓reduceIte]
          iintro H; iexact H
        · irevert Hrest2
          simp only [hid, decide_false, ↓reduceIte, Bool.false_eq_true]
          iintro H; iexact H
      ihave Hs : iprop(sliceOwn s (S.closeWs P.ws ph).l) $$ [Hs Hscap]
      · unfold sliceOwn; iframe
      wp_apply wp_mapDelete $$ Hclm as Hclm
      wp_apply wp_map_len $$ Hm as Hm
      wp_if_destruct
      · wp_for_post
        isplitr
        · ipureintro; rfl
        ihave #Hnil := statusErrOk_nil (GF := GF)
        iapply client.runExit_of_core V G γs b n clm csm closeErr_ptr GoInterface.nil
        iframe closeErr Hnil
        unfold client.runCore
        iexists S.closeWs P.ws ph, GMap.delete P.ws U, rcv, mref, s, e
        have h1 : (S.closeWs P.ws ph).Dm = S.Dm := rfl
        have h2 : (S.closeWs P.ws ph).L = S.L := rfl
        have h3 : (S.closeWs P.ws ph).ansd = S.ansd := rfl
        have h4 : (S.closeWs P.ws ph).regs = S.regs := rfl
        have h5 : (S.closeWs P.ws ph).CS = S.CS := rfl
        rw [h1, h2, h3, h4, h5]
        iframe
        iframe #
        isplitr
        · ipureintro; exact Hrcv
        ipureintro; exact Hg'
      by_cases hid : ph.id = W64 (-1)
      · simp only [show decide (ph.id = W64 (-1)) = true by simp [hid], Bool.not_true]
        wp_auto
        wp_for_post
        iexists bo, γs, b, n, _, Dn, cd', rc, γrc, csm
        simp only [named]
        iframe closeErr cur backoff wc cancelSet Hrc Hrcb Hcws Hspec
        unfold client.runCore
        iexists S.closeWs P.ws ph, GMap.delete P.ws U, rcv, mref, s, e
        have h1 : (S.closeWs P.ws ph).Dm = S.Dm := rfl
        have h2 : (S.closeWs P.ws ph).L = S.L := rfl
        have h3 : (S.closeWs P.ws ph).ansd = S.ansd := rfl
        have h4 : (S.closeWs P.ws ph).regs = S.regs := rfl
        have h5 : (S.closeWs P.ws ph).CS = S.CS := rfl
        rw [h1, h2, h3, h4, h5]
        iframe
        iframe #
        ipureintro; exact ⟨Hrcv, Hg'⟩
      simp only [show decide (ph.id = W64 (-1)) = false by simp [hid], Bool.not_false]
      wp_auto
      wp_apply wp_mapInsert $$ Hcsm as Hcsm
      rename_i crp
      irename : (crp ↦ (_ : etcdserverpb.WatchRequest_CancelRequest) : IProp GF) => Hcr
      imod client.cancelReq_send «$v0_ptr» crp «$r0_ptr» ph.id
        $$ [«$v0» Hcr «$r0»] with Hsend
      · iframe
      wp_apply wp_zapInt64 as %f1 -
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      wp_auto
      wp_apply wp_Debug V.lg _ _ $$ []
      · iframe #; ipureintro; exact Hlg
      wp_apply HSend $$ %S.L %«$r0_ptr» %(.cancel ph.id) [Hstok Hsend] as %err ⟨-, Hres⟩
      · iframe
        unfold v3rpc.watchUp v3rpc.watchReqOk
        isplitr <;> itrivial
      ihave ⟨%L', %HL', Hstok⟩ : iprop(∃ L' : List v3rpc.WatchReqM,
          ⌜L' = S.L ∨ L' = S.L ++ [.cancel ph.id]⌝ ∗ cliSendTok (Req := v3rpc.pbWatchRequest) γs L')
          $$ [Hres]
      · icases Hres with (⟨-, Htok⟩ | ⟨-, %L', %HL', Htok⟩)
        · iexists _; iframe; ipureintro; right; rfl
        · iexists L'; iframe; ipureintro; exact HL'
      cases err with
      | nil =>
        wp_auto
        wp_for_post
        iexists bo, γs, b, n, _, Dn, cd', rc, γrc, csm
        simp only [named]
        iframe closeErr cur backoff wc cancelSet Hrc Hrcb Hcws Hspec
        have hXr : ph.id ∈ S.regs := by
          cases ph with
          | queued si => exact absurd rfl hid
          | reg X => exact Hph.2.2.2.1
          | closedRun X => exact absurd rfl hid
          | orphan => exact absurd rfl hid
          | closed => exact absurd rfl hid
        have hM1 : (S.closeWs P.ws ph).M !! ph.id = none := by
          unfold client.RunSt.closeWs; simp only [hid, ↓reduceIte]; exact GMap.lookup_delete _ _
        have hC1 : (S.closeWs P.ws ph).CI !! ph.id = none := by
          have hcid : ph.cid = ph.id := by
            cases ph with
            | reg X => rfl
            | _ => exact absurd rfl hid
          unfold client.RunSt.closeWs; simp only [hcid, hid, ↓reduceIte]; exact GMap.lookup_delete _ _
        obtain ⟨Hg2, Hph2⟩ := client.cancel_ok (S := S.closeWs P.ws ph) (U := GMap.delete P.ws U)
          Hg' hXr HL'
        ihave Hels := BigSepM.bigSepM_impl
            (Ψ := fun ws (_ : Unit) =>
              client.wsElem V G n γs ((S.closeWs P.ws ph).sentCancel ph.id L') ws) $$ Hels []
        · iintro !> %ws' %u %Hws' Hw'
          iapply (client.wsElem_mono V G n γs (S := S.closeWs P.ws ph)
            (S' := (S.closeWs P.ws ph).sentCancel ph.id L') ws' rfl
            (fun ph' h => Hph2 ws' ph' h
              (fun X' e => by
                subst e; intro eX; subst eX; have h1 := h.1.2.2; rw [hC1] at h1; cases h1)
              (fun e => by subst e; have h1 := h.1; rw [hM1] at h1; cases h1))
            (fun X hph => client.cancels_of_snoc (.cancel ph.id) X (fun e => by
              cases e; have h1 := hph.1; rw [hM1] at h1; cases h1) HL')) $$ Hw'
        unfold client.runCore
        iexists (S.closeWs P.ws ph).sentCancel ph.id L', GMap.delete P.ws U, rcv, mref, s, e
        have e1 : ((S.closeWs P.ws ph).sentCancel ph.id L').M = (S.closeWs P.ws ph).M := rfl
        have e2 : ((S.closeWs P.ws ph).sentCancel ph.id L').l = (S.closeWs P.ws ph).l := rfl
        have e3 : ((S.closeWs P.ws ph).sentCancel ph.id L').CL = (S.closeWs P.ws ph).CL := rfl
        have e4 : ((S.closeWs P.ws ph).sentCancel ph.id L').Dm = S.Dm := rfl
        have e5 : ((S.closeWs P.ws ph).sentCancel ph.id L').L = L' := rfl
        have e6 : ((S.closeWs P.ws ph).sentCancel ph.id L').ansd = S.ansd := rfl
        have e7 : ((S.closeWs P.ws ph).sentCancel ph.id L').regs = S.regs := rfl
        have e8 : ((S.closeWs P.ws ph).sentCancel ph.id L').CS = GMap.insert ph.id () S.CS := rfl
        rw [e1, e2, e3, e4, e5, e6, e7, e8]
        iframe
        iframe #
        ipureintro; exact ⟨Hrcv, Hg2⟩
      | ok ei =>
        wp_auto
        wp_apply wp_zapInt64 as %f1 -
        wp_apply wp_zapError as %f2 -
        wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
        isplitr
        · ipureintro; rfl
        iintro %fsl ⟨-, -⟩
        wp_auto
        wp_apply wp_Debug V.lg _ _ $$ []
        · iframe #; ipureintro; exact Hlg
        wp_for_post
        iexists bo, γs, b, n, _, Dn, cd', rc, γrc, csm
        simp only [named]
        iframe closeErr cur backoff wc cancelSet Hrc Hrcb Hcws Hspec
        have hXr : ph.id ∈ S.regs := by
          cases ph with
          | queued si => exact absurd rfl hid
          | reg X => exact Hph.2.2.2.1
          | closedRun X => exact absurd rfl hid
          | orphan => exact absurd rfl hid
          | closed => exact absurd rfl hid
        have hM1 : (S.closeWs P.ws ph).M !! ph.id = none := by
          unfold client.RunSt.closeWs; simp only [hid, ↓reduceIte]; exact GMap.lookup_delete _ _
        have hC1 : (S.closeWs P.ws ph).CI !! ph.id = none := by
          have hcid : ph.cid = ph.id := by
            cases ph with
            | reg X => rfl
            | _ => exact absurd rfl hid
          unfold client.RunSt.closeWs; simp only [hcid, hid, ↓reduceIte]; exact GMap.lookup_delete _ _
        obtain ⟨Hg2, Hph2⟩ := client.cancel_ok (S := S.closeWs P.ws ph) (U := GMap.delete P.ws U)
          Hg' hXr HL'
        ihave Hels := BigSepM.bigSepM_impl
            (Ψ := fun ws (_ : Unit) =>
              client.wsElem V G n γs ((S.closeWs P.ws ph).sentCancel ph.id L') ws) $$ Hels []
        · iintro !> %ws' %u %Hws' Hw'
          iapply (client.wsElem_mono V G n γs (S := S.closeWs P.ws ph)
            (S' := (S.closeWs P.ws ph).sentCancel ph.id L') ws' rfl
            (fun ph' h => Hph2 ws' ph' h
              (fun X' e => by
                subst e; intro eX; subst eX; have h1 := h.1.2.2; rw [hC1] at h1; cases h1)
              (fun e => by subst e; have h1 := h.1; rw [hM1] at h1; cases h1))
            (fun X hph => client.cancels_of_snoc (.cancel ph.id) X (fun e => by
              cases e; have h1 := hph.1; rw [hM1] at h1; cases h1) HL')) $$ Hw'
        unfold client.runCore
        iexists (S.closeWs P.ws ph).sentCancel ph.id L', GMap.delete P.ws U, rcv, mref, s, e
        have e1 : ((S.closeWs P.ws ph).sentCancel ph.id L').M = (S.closeWs P.ws ph).M := rfl
        have e2 : ((S.closeWs P.ws ph).sentCancel ph.id L').l = (S.closeWs P.ws ph).l := rfl
        have e3 : ((S.closeWs P.ws ph).sentCancel ph.id L').CL = (S.closeWs P.ws ph).CL := rfl
        have e4 : ((S.closeWs P.ws ph).sentCancel ph.id L').Dm = S.Dm := rfl
        have e5 : ((S.closeWs P.ws ph).sentCancel ph.id L').L = L' := rfl
        have e6 : ((S.closeWs P.ws ph).sentCancel ph.id L').ansd = S.ansd := rfl
        have e7 : ((S.closeWs P.ws ph).sentCancel ph.id L').regs = S.regs := rfl
        have e8 : ((S.closeWs P.ws ph).sentCancel ph.id L').CS = GMap.insert ph.id () S.CS := rfl
        rw [e1, e2, e3, e4, e5, e6, e7, e8]
        iframe
        iframe #
        ipureintro; exact ⟨Hrcv, Hg2⟩
    iapply BigAndL.bigAndL_nil.2
    itrivial
  iintro %v ⟨%Hv, Hexit⟩
  subst Hv
  iunfold client.runExit at Hexit
  icases Hexit with ⟨%γs, %S, %U, %ce, %e, %mref, %s, %ng, HcE, #Hce, Hclm, Hsub, Hm, Hres, Hs, HcF,
    #He, %HgOk, Hwsa, Hels, Had, Htt, Hdn, Hgen⟩
  wp_auto
  ipersist HcF
  ihave ⟨Hids, Hcls, Hlfs⟩ := client.wsElems_split V G ng γs S U $$ Hels
  -- (D24) the substreams' current lifetimes
  ihave Hlfs : iprop([∗map] ws ↦ _u ∈ U, ∃ a : WsPrm GF × LifePrm,
      (⌜a.1.ws = ws⌝ ∗ wsIs V a.1 ∗ lifeInvIs V G a.1 a.2 ∗ client.lifeTk V a.1 a.2) ∗
      donecAt ws (lifeDn V G a.1 a.2)) $$ [Hlfs]
  · iapply BigSepM.bigSepM_mono ?_ $$ Hlfs
    intro k x _
    unfold client.lifeE
    iintro ⟨%P, %L, %H, #HP, Hdc, #Hli, Htk⟩
    iexists (P, L)
    iframe HP Hdc Hli Htk
    ipureintro; exact H
  icases client.bigSepM_choice_keys (client.dummyWsPrm G G.γr, (⟨null, G.γreq, G.γws, G.γws, 0⟩ : LifePrm))
    (fun ws a => iprop((⌜a.1.ws = ws⌝ ∗ wsIs V a.1 ∗ lifeInvIs V G a.1 a.2 ∗
      client.lifeTk V a.1 a.2) ∗ donecAt ws (lifeDn V G a.1 a.2))) U $$ Hlfs with ⟨%f, Hlfs⟩
  rw [BigSepM.bigSepM_sep_eq]
  icases Hlfs with ⟨Hlts, Hdcs⟩
  -- the substreams' loop: close the `recvc` of each not yet closing
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (_ : List w64) (_ : Int) => iprop(∃ (CL' U1 : GMap Loc Unit) (wv : Loc),
      ws_ptr ↦ wv ∗ ownMap clm (DFrac.own 1) CL' ∗ ([∗map] ws ↦ _u ∈ U1, client.closerE V S ws) ∗
      ⌜client.tdOk S U CL' U1⌝)) $$ Hm
  iintro %keys ⟨%Hk1, %Hk2, %Hk3⟩
  isplitl [ws Hclm Hcls]
  · iexists S.CL, U, _
    iframe
    ipureintro; exact client.tdOk_init S U
  isplitr
  · imodintro
    iintro %ik %X %wsv ⟨%HkX, %HMX⟩ ⟨%CL', %U1, %wv, Hwsp, Hclm, Hcls, %Htd⟩
    wp_auto
    wp_apply wp_map_lookup2 $$ Hclm as Hclm
    cases hcl : CL' !! wsv with
    | some u =>
      simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
      wp_auto
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists CL', U1, wsv
      iframe
      ipureintro; exact Htd
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Bool.not_false, Option.getD_none]
      have hU : U !! wsv = some () := HgOk.1 X wsv HMX
      have hU1 : U1 !! wsv = some () := Htd.2.1 wsv hU hcl
      icases (BigSepM.bigSepM_delete hU1).1 $$ Hcls with ⟨Hc, Hcls⟩
      iunfold client.closerE at Hc
      icases Hc with ⟨%ph, %Hph, Hc⟩
      have hreg : ∃ X', ph = .reg X' := by
        cases ph with
        | queued si => exact absurd HMX (Hph.1 X)
        | reg X' => exact ⟨X', rfl⟩
        | closedRun X' => rw [Htd.2.2 wsv Hph.2.2.1] at hcl; cases hcl
        | orphan => exact absurd HMX (Hph.1 X)
        | closed => exact absurd HMX (Hph.1 X)
      obtain ⟨X', rfl⟩ := hreg
      iunfold client.closerRes at Hc
      iunfold recvcCloser at Hc
      icases Hc with ⟨%P, %sent, %HPws, #HP, Hprod⟩
      subst HPws
      ihave #HP' := HP
      iunfold wsIs at HP'
      icases HP' with ⟨-, #Frecvc, -, #Hrecvc, -⟩
      wp_pures
      wp_auto
      wp_apply wp_sspsc_close P.γr P.recvc (client.recvElem V P) (fun _ => iprop(True)) sent
        $$ [Hprod]
      · iframe Hrecvc Hprod
      wp_pures
      wp_apply wp_mapInsert $$ Hclm as Hclm
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _, _, P.ws
      iframe
      ipureintro; exact client.tdOk_close Htd P.ws
  iintro ⟨%CL', %U1, %wv, Hwsp, Hclm, Hcls, %Htd⟩ Hm
  iunfold sliceOwn at Hs
  icases Hs with ⟨Hs, Hscap⟩
  ihave %Hslen := ownSlice_len $$ Hs
  wp_auto
  ihave IH2 : iprop(∃ (n : w64) (wv : Loc) (CL' U1 : GMap Loc Unit),
      "i" ∷ i_ptr ↦ n ∗ "ws" ∷ ws_ptr ↦ wv ∗ "Hclm" ∷ ownMap clm (DFrac.own 1) CL' ∗
      "Hcls" ∷ ([∗map] ws ↦ _u ∈ U1, client.closerE V S ws) ∗ "Hs" ∷ s ↦* S.l ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (S.l.length : Int) ∧ client.tdOk S U CL' U1⌝)
      $$ [i ws Hclm Hcls Hs]
  · iexists W64 0, _, CL', U1
    simp only [named]
    iframe
    ipureintro; refine ⟨by word, by word, Htd⟩
  wp_for IH2
  wp_if_destruct
  · have Hif' : sint.Z n < sint.Z s.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    have Hlt : sint.nat n < S.l.length := by word
    obtain ⟨wsv, Hwsv⟩ : ∃ wsv, S.l[sint.nat n]? = some wsv := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z s.len := ⟨Hn.1, Hif'⟩
    rw [ite_eq_left Hbnd]
    icases ownSlice_elem_acc (sint.Z n) wsv s (DFrac.own 1) S.l Hn.1 (by simpa using Hwsv) $$ Hs
      with ⟨Hel, Hs⟩
    wp_auto
    ihave Hs := Hs $$ Hel
    have Hset : S.l.set (sint.Z n).toNat wsv = S.l := by
      apply List.ext_getElem?
      intro j
      rw [List.getElem?_set]
      by_cases hj : (sint.Z n).toNat = j
      · subst hj
        have : (sint.Z n).toNat < S.l.length := by word
        simp only [if_pos rfl, this, ↓reduceIte]
        rw [show (sint.Z n).toNat = sint.nat n by rfl] at *
        exact Hwsv.symm
      · simp [hj]
    rw [Hset]
    wp_apply wp_map_lookup2 $$ Hclm as Hclm
    wp_pures
    by_cases hnull : wsv = null
    · simp only [hnull, _root_.decide_true, Bool.not_true]
      wp_pures
      wp_for_post
      iframe
      iexists _, _, CL', U1
      simp only [named]
      iframe
      ipureintro; refine ⟨by word, by word, Hn.2.2⟩
    simp only [hnull, decide_false, Bool.not_false]
    have hmem : wsv ∈ S.l := List.mem_of_getElem? Hwsv
    cases hcl : CL' !! wsv with
    | some u =>
      simp only [Option.isSome_some, _root_.decide_true, Bool.not_true]
      wp_auto
      wp_for_post
      iframe
      iexists _, _, CL', U1
      simp only [named]
      iframe
      ipureintro; refine ⟨by word, by word, Hn.2.2⟩
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Bool.not_false]
      have hU : U !! wsv = some () := HgOk.2.2.1 wsv hmem hnull
      have hU1 : U1 !! wsv = some () := Hn.2.2.2.1 wsv hU hcl
      icases (BigSepM.bigSepM_delete hU1).1 $$ Hcls with ⟨Hc, Hcls⟩
      iunfold client.closerE at Hc
      icases Hc with ⟨%ph, %Hph, Hc⟩
      have hq : ∃ si, ph = .queued si := by
        cases ph with
        | queued si => exact ⟨si, rfl⟩
        | reg X' => exact absurd hmem Hph.2.1
        | closedRun X' => exact absurd hmem Hph.2.1
        | orphan => exact absurd hmem Hph.2.1
        | closed => exact absurd hmem Hph.2.1
      obtain ⟨si, rfl⟩ := hq
      iunfold client.closerRes at Hc
      iunfold recvcCloser at Hc
      icases Hc with ⟨%P, %sent, %HPws, #HP, Hprod⟩
      subst HPws
      ihave #HP' := HP
      iunfold wsIs at HP'
      icases HP' with ⟨-, #Frecvc, -, #Hrecvc, -⟩
      wp_pures
      wp_auto
      wp_apply wp_sspsc_close P.γr P.recvc (client.recvElem V P) (fun _ => iprop(True)) sent
        $$ [Hprod]
      · iframe Hrecvc Hprod
      wp_pures
      wp_apply wp_mapInsert $$ Hclm as Hclm
      wp_pures
      wp_for_post
      iframe
      iexists _, _, _, _
      simp only [named]
      iframe
      ipureintro; refine ⟨by word, by word, client.tdOk_close Hn.2.2 P.ws⟩
  have Hnot : ¬ (sint.Z n < sint.Z s.len) := by
    first | exact Hif | exact (fun h => Hif (by simp [h]))
  (try simp only [Hnot, decide_false])
  (try cleanup_bool_decide)
  (try rw [if_pos (by simp)])
  (try wp_auto)
  -- the loop's end: join, then wait for the closing substreams
  wp_apply wp_join G.wgs mref S.M s S.l (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) (DFrac.own 1)
    U (fun ws => lifeDn V G (f ws).1 (f ws).2) $$ [Hsub Hm Hres Hs Hdcs] as
    ⟨Hsub, Hm, Hres, Hs, -, -, -⟩
  · iframe
    ipureintro; exact ⟨HgOk.1, fun ws h hn => HgOk.2.2.1 ws h hn⟩
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (_ : List Loc) (_ : Int) => iprop(∃ (M' : GMap w64 Loc)
      (l' : List Loc) (U' : GMap Loc Unit),
      ownMap mref (DFrac.own 1) M' ∗ s ↦* l' ∗ ghostMapAuth G.γws 1 U' ∗
      ([∗map] ws ↦ _u ∈ U', client.idE ws) ∗ wgsF G.wgs go!"substreams" ↦ mref ∗
      wgsF G.wgs go!"resuming" ↦ s ∗ monoNatAuthOwn G.γend 1 ng ∗
      ([∗map] ws ↦ _u ∈ U', ⌜(f ws).1.ws = ws⌝ ∗ wsIs V (f ws).1 ∗
        lifeInvIs V G (f ws).1 (f ws).2 ∗ client.lifeTk V (f ws).1 (f ws).2))) $$ Hclm
  iintro %keys ⟨%Hk1, %Hk2, %Hk3⟩
  isplitl [Hm Hs Hwsa Hids Hsub Hres Hgen Hlts]
  · iexists _, _, _
    iframe
  isplitr
  · imodintro
    iintro %ik %wk %u ⟨%Hkw, %Hu⟩ ⟨%M', %l', %U', Hm, Hs, Hwsa, Hids, Hsub, Hres, Hgen, Hlts⟩
    wp_auto
    wp_apply +noauto wp_bag_receive G.γclosing G.closingc (closingP V G) $$ Hclb as %wsr Hel
    iunfold closingP at Hel
    ihave %HU' := ghost_map_lookup $$ Hwsa Hel
    icases (BigSepM.bigSepM_delete HU').1 $$ Hids with ⟨Hid, Hids⟩
    icases (BigSepM.bigSepM_delete HU').1 $$ Hlts with ⟨⟨%Hfw, #HPf, #Hli, Htk⟩, Hlts⟩
    iunfold client.idE at Hid
    icases Hid with ⟨%idv, Hid⟩
    wp_auto_lc 1
    -- (D24) what the goroutine left
    iapply fupd_wp
    imod client.take_stop V G ng (f wsr).1 (f wsr).2 wsr Hfw $$ [Hlc1 Htk Hel Hgen]
      with ⟨Hsb, Hel, Hgen⟩
    · iframe; iframe #
    ihave Hbody : iprop(closingBody V wsr) $$ [Hsb]
    · unfold closingBody
      iexists (f wsr).1
      iframe HPf Hsb
      ipureintro; exact Hfw
    imod ghost_map_delete $$ Hwsa Hel with Hwsa
    imodintro
    wp_apply wp_closeSub V G.wgs wsr idv ce DFrac.discard (DFrac.own 1) (DFrac.own 1) mref M' s l'
      $$ [Hbody Hid Hsub Hm Hres Hs] as ⟨Hid, -, Hsub, Hres, Hrest⟩
    · iframe; iframe #
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    by_cases hid : idv = W64 (-1)
    · irevert Hrest
      simp only [hid, _root_.decide_true, ↓reduceIte]
      iintro ⟨Hm, Hs⟩
      iexists _, _, _
      iframe
    · irevert Hrest
      simp only [hid, decide_false, ↓reduceIte, Bool.false_eq_true]
      iintro ⟨Hm, Hs⟩
      iexists _, _, _
      iframe
  iintro ⟨%M', %l', %U', Hm, Hs, Hwsa, Hids, Hsub, Hres, Hgen, Hlts⟩ Hclm
  wp_auto
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold wgAdder at Had
  wp_apply wp_wgsWg_Wait $$ [Had]
  · iframe
  wp_apply wp_closeStream V G callSl $$ [Hdn]
  · iframe #
    iframe
    unfold closeErrPub
    iexists ce
    iframe #
  iapply HΦ
  iexact Htt

end proof

end EtcdGrove
end Perennial
