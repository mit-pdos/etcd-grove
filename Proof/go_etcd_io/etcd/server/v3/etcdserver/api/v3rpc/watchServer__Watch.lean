/-
Proof of the spec of the same name (the watch slice's unit W-S): the run of a watch stream, its two
goroutines and the shutdown. Lean-first (no Rocq counterpart). Over mvcc's API (2026-11-05):
`NewWatchStream`'s contract at the watchable store (`shapes.law`), the run's invariant allocated
from its `wsState ι wsStart` (`WatchApi.wsInvG_alloc`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer__Watch
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverWatchStream__recvLoop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverWatchStream__sendLoop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverWatchStream__close
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.isClientCtxErr
public import Spec.errors.IsCtxErr
public import Spec.errors.Is
public import Spec.errors.IsStatusErr
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.SrvCtxWeakLaws
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.Error
public import Spec.github_com.prometheus.client_golang.prometheus.CounterVec__WithLabelValues
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

set_option hygiene false in
/-- `Watch`'s end, after the `select`: `sws.close()`, then `return err`. -/
local macro "watch_tail" : tactic => `(tactic| (
  iapply wp_fupd
  wp_apply hClose sws_ptr r Up Dn _ ci cd (W32 0 + W32 1)
    iprop(True ∗ mvcc.api.mvccReaders W.γm 1) $$ [Hcl Hcc Hadd] as HP
  · iframe #; iframe
  icases HP with ⟨-, HrdS⟩
  imodintro
  iapply HΦ
  iframe Hspec HrdS Hl4
  first | iexact HsvW | iexact HsvE | iexact HsvC))

set_option hygiene false in
/-- `errors.Is(err, context.Canceled)` on a context's error `err` (`context.isCtxErr`), then the
assignment of `ErrGRPCWatchCanceled` when it holds. -/
local macro "canceled_check" e:term : tactic => `(tactic| (
  wp_apply hIs $e (GoInterface.ok eC) $$ [] as %bC -
  · iframe #; try (ileft; iexact HeC)
  wp_if_destruct
  rotate_left
  all_goals try wp_auto))

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

set_option maxHeartbeats 0 in
theorem v3rpc.watchServer.Watch.wp_proof
    (hShapes : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hP : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hRS : mvcc.api.mvccReaders_split.law (GF := GF) (hG := hG))
    (hRecv : v3rpc.serverWatchStream.recvLoop.spec (GF := GF) (hG := hG))
    (hSend : v3rpc.serverWatchStream.sendLoop.spec (GF := GF) (hG := hG))
    (hClose : v3rpc.serverWatchStream.close.spec (GF := GF) (hG := hG))
    (hICE : v3rpc.isClientCtxErr.spec (GF := GF) (hG := hG))
    (hIs : errors.IsCtxErr.spec (GF := GF) (hG := hG))
    (hIsT : errors.Is.spec (GF := GF) (hG := hG))
    (hIsS : errors.IsStatusErr.spec (GF := GF) (hG := hG))
    (hZD : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (hZW : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG))
    (hCV : prometheus.CounterVec.WithLabelValues.spec (GF := GF) (hG := hG)) :
    v3rpc.watchServer.Watch.spec (GF := GF) (hG := hG) := by
  intro p R W st γs Up Dn ci cd N₂ N₃ γ₂ γ₃ F₂ F₃
  have : ∀ ws γ ι, Persistent (mvcc.api.isMvccWatchStream (GF := GF) ws γ ι) := hP.2.1
  have : ∀ kv γ, Persistent (mvcc.api.isMvcc (GF := GF) kv γ) := hP.1
  have := v3rpc.srvWOk_persistent hP W R.wsl v3rpc.wsN
  have := v3rpc.swsIs_persistent (GF := GF) hP
  have : ∀ γ n, Timeless (mvcc.api.mvccReaders (GF := GF) γ n) := hP.2.2.2.2.2.2.2.1
  wp_start as ⟨#HWS, #HW, #Hstream, #Hspec, #Hup, Hrt, Hst, HAux, %Htb4, #Hp2, #Hp3, HrdS, Hl4⟩
  obtain ⟨Htb, HT4⟩ := Htb4
  ihave #HWS' := HWS
  iunfold v3rpc.isWatchServer at HWS'
  icases HWS' with ⟨%Hnn, #Hzl, #Plg, #Pcid, #Pmid, #Pmrb, #Psg, #Pwa, #Pag, #Hsrv⟩
  ihave #Hsrv' := Hsrv
  iunfold v3rpc.watchSrvOk at Hsrv'
  icases Hsrv' with ⟨-, -, #Hvars, -⟩
  ihave #HW' := HW
  iunfold v3rpc.srvWOk at HW'
  icases HW' with ⟨%Hkv, #Hmv, -⟩
  rw [Hkv]
  have hNWS := (hShapes.2.1 R.wsl).2
  ihave #Pmvcc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply (hNWS W.γm) $$ [] as %ws ⟨%ι, #Hwstream, HS, Hrcv⟩
  · iframe #
  -- the run's invariant, its received list, its answer tokens, and the stream's auxiliary name
  imod v3rpc.wsInvG_alloc (v3rpc.cancelQ γs) ι $$ HS with ⟨%γreg, %γtok, %γpk, %γcl, #Hinv, Hcl⟩
  imod mono_list_own_alloc (GF := GF) ([] : List mvcc.api.WResp) with ⟨%γr, HA, -⟩
  imod v3rpc.ansPool_alloc (GF := GF) with ⟨%γa, HPool⟩
  imod v3rpc.streamAux_set γs [γreg, γtok, γr, γa, γpk] $$ HAux with #HauxIs
  wp_apply chan.wp_make2 (V := Loc) (W64 16) as %ctrl %γch ⟨#Hctrl, %Hcap, Hoc⟩
  · ipureintro; decide
  wp_apply (wp_map_make1 (K := w64) (V := Bool) go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty go.bool)
    as %pm Hpm
  wp_apply (wp_map_make1 (K := w64) (V := Bool) go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty go.bool)
    as %vm Hvm
  wp_apply (wp_map_make1 (K := w64) (V := Bool) go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty go.bool)
    as %fm Hfm
  wp_apply chan.wp_make1 (V := Unit) as %cc %γcc ⟨#Hccc, %-, Hcco⟩
  ihave %Hswsn := typedPointsto_not_null _ _ _ $$ sws
  iStructNamed sws
  ipersist lg
  ipersist clusterID
  ipersist memberID
  ipersist maxRequestBytes
  ipersist sg
  ipersist watchable
  ipersist ag
  ipersist gRPCStream
  ipersist watchStream
  ipersist ctrlStream
  ipersist progress
  ipersist prevKV
  ipersist fragment
  ipersist closec
  -- the control stream: an SPSC channel of control responses (its predicate reads none of the
  -- run's control-stream names, so a stand-in for them states it before they exist)
  let r0 : v3rpc.WRun GF := ⟨R, W, γs, ws, ι, γreg, γtok, γpk, γr, γcl, γa, ctrl, ⟨γch, γa, γa⟩, pm, vm,
    fm, cc, γch⟩
  let P' : Int → Loc → IProp GF := v3rpc.ctrlP r0 ci
  imod start_spsc ctrl P' (fun _ => iprop(True)) γch $$ Hctrl [Hoc] with ⟨%γctrl, #Hspsc, Hprod, Hcons'⟩
  · iright; iexact Hoc
  -- `closec`: a broadcast channel
  imod alloc_broadcast_chan (E := ⊤) iprop(True) γcc cc $$ Hccc Hcco with Hcc
  ihave #HccU := ownBroadcastChan_Unknown _ _ _ _ $$ Hcc
  -- the lock over the maps
  imod sync.init_RWMutex (v3rpc.swsMu pm vm fm γpk) (E := ⊤) (v3rpc.swsF sws_ptr go!"mu") $$ [Hpm Hvm Hfm] mu
    with Htoks
  · inext
    iunfold v3rpc.swsMu
    iexists ∅, ∅, ∅
    iframe
    isplitr
    · ipureintro; intro id; simp
    iintro !> %id %b %h
    simp at h
  have hN : 1 ≤ Int.toNat sync.rwmutex.actualMaxReaders := by
    rw [sync.rwmutex.actualMaxReaders_unseal]; decide
  obtain ⟨k, hk⟩ : ∃ k, Int.toNat sync.rwmutex.actualMaxReaders = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hN).symm⟩
  rw [hk, List.replicate_succ] at *
  icases BigSepL.bigSepL_cons.1 $$ Htoks with ⟨Hmutok, -⟩
  ihave ⟨Hmutok, #Hguard⟩ := sync.ownRWMutex_guard _ _ $$ Hmutok
  -- the wait group
  imod sync.init_WaitGroup (sync.join.wgjN.@"wg") (v3rpc.swsF sws_ptr go!"wg") $$ wg
    with ⟨%γwg, #HisWg, Hctr, Hwaiters⟩
  imod sync.join.init (v3rpc.swsF sws_ptr go!"wg") γwg $$ [$HisWg $Hctr $Hwaiters] with Hadd
  let r : v3rpc.WRun GF := ⟨R, W, γs, ws, ι, γreg, γtok, γpk, γr, γcl, γa, ctrl, γctrl, pm, vm, fm, cc, γcc⟩
  have hP : v3rpc.ctrlP r ci = P' := by funext k l; rfl
  ihave #Hsws : v3rpc.swsIs sws_ptr r Up Dn st ci cd $$ []
  · iunfold v3rpc.swsIs
    rw [hP]
    iframe #
    isplitr
    · ipureintro; exact Hswsn
    simp only [r, v3rpc.auxOf]; iexact HauxIs
  wp_apply sync.join.WaitGroup.wp_Add (mvcc.api.mvccReaders W.γm 1) (v3rpc.swsF sws_ptr go!"wg")
    iprop(True) (W32 0) $$ [$Hadd] as ⟨Hadd, Hdone⟩
  · iframe #; ipureintro; decide
  -- (2026-10-20, watchkv) the send loop's goroutine with its thread token, which
  -- `GetProgressReportInterval` lends to the interval's pool
  wp_apply wp_fork_tok_body $$ [Hst Hcons' Hrcv HA Hmutok Hdone HrdS]
  · iintro Htt
    wp_apply hSend sws_ptr r Up Dn st ci cd $$ [$Hst $Hcons' $Hrcv $HA $Hmutok $Htt $HrdS]
      as ⟨Htt, HrdS⟩
    · iframe #; ipureintro; exact ⟨Htb, HT4⟩
    wp_apply sync.join.WaitGroup.wp_Done (mvcc.api.mvccReaders W.γm 1) (v3rpc.swsF sws_ptr go!"wg")
      $$ [$Hdone $HrdS]
    · iframe #; try iexact Htt
  -- the stream's methods and its context
  ihave #Hstream' := Hstream
  iunfold v3rpc.srvStreamIs at Hstream'
  icases Hstream' with ⟨%si, %Hsi, #HRecv, #HSend, #HCtx, #Hctxw, #Hlibc, #Hspanc, -⟩
  ihave #Hctx2 := Hctxw
  iunfold srvCtxWeak at Hctx2
  iNamed Hctx2
  ipersist stream
  iunfold v3rpc.watchVars at Hvars
  icases Hvars with ⟨#Heof, #Hwpv⟩
  iunfold v3rpc.watchPkgVars at Hwpv
  icases Hwpv with ⟨#HeInv, #HeOld, #HeEmpty, #HeDenied, #HeEWR, #HeDup, #HmCompacted,
    #HmInv, #HmOld, #HmEmpty, #HmDenied, #HmWC, #HstreamF, #Hh1, #Hh2, #Hh3, #Hh4, #Htracer,
    #Hcanc, #Hguard'⟩
  icases HstreamF with ⟨%cvF, #HcvF, %HcvFl⟩
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Pprom : isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus $$ []
  · iPkgInit
  ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  -- `errc`: the receive loop's error, with its control-stream producer
  wp_apply chan.wp_make2 (V := GoInterface) (W64 1) as %errc %γe ⟨#Herrc, %-, Hoe⟩
  · ipureintro; decide
  let PE : Int → GoInterface → IProp GF := fun _ e =>
    iprop(v3rpc.streamErr e ∗ go_etcd_io.etcd.cache.v3.statusErrOk e ∗
      ∃ sent : List Loc, spscProducer γctrl sent)
  imod start_spsc errc PE (fun _ => iprop(False)) γe $$ Herrc [Hoe]
    with ⟨%γerr, #HspscE, HprodE, HconsE⟩
  · iright; iexact Hoe
  ipersist errc
  -- the receive loop's goroutine borrows the auth reader (level 2) and a store reader token
  -- (level 3) with its own thread token, and gives them back when the loop returns
  wp_apply wp_fork_tok_upd
  iintro Htt Hlc1r
  icases (threadTok_level0 (GF := GF)).1 $$ Htt with ⟨Ht0, Htt⟩
  icases (threadTokFrom_succ (GF := GF) 1 (by omega)).1 $$ Htt with ⟨Ht1, Htt⟩
  icases (threadTokFrom_succ (GF := GF) 2 (by omega)).1 $$ Htt with ⟨Ht2, Htt⟩
  icases (threadTokFrom_succ (GF := GF) 3 (by omega)).1 $$ Htt with ⟨Ht3, Ht4⟩
  imod threadPool.borrowL N₂ 2 γ₂ iprop(F₂ ∗ R.E.RD) ⊤ (fun _ _ => CoPset.mem_full) $$ [Hp2 Ht2]
    with ⟨HB2, Hl2⟩
  · iframe; iframe #
  imod threadPool.borrowL N₃ 3 γ₃ iprop(mvcc.api.mvccReaders W.γm 1 ∗ F₃) ⊤
    (fun _ _ => CoPset.mem_full) $$ [Hp3 Ht3] with ⟨HB3, Hl3⟩
  · iframe; iframe #
  ihave HB : iprop(▷ ((F₂ ∗ R.E.RD) ∗ (mvcc.api.mvccReaders W.γm 1 ∗ F₃))) $$ [HB2 HB3]
  · inext; iframe
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc1r HB with ⟨⟨HF2, HRD⟩, ⟨HrdR, HF3⟩⟩
  imodintro
  isplitl [Hrt Hprod HPool HprodE HF2 HRD HrdR HF3 Hl2 Hl3 Ht0 Ht1 Ht4]
  · iapply wp_fupd
    wp_apply hRecv sws_ptr r Up Dn st ci cd [] [] $$ [$Hrt $Hprod $HPool $HRD $HrdR]
      as %rerr ⟨#Hrerr, HrdR, HRD, %sent', Hprod⟩
    · iframe #
    imod threadPool.giveBackL N₂ 2 γ₂ iprop(F₂ ∗ R.E.RD) ⊤ (fun _ _ => CoPset.mem_full)
      $$ [Hp2 Hl2 HF2 HRD] with Ht2
    · iframe; iframe #
    imod threadPool.giveBackL N₃ 3 γ₃ iprop(mvcc.api.mvccReaders W.γm 1 ∗ F₃) ⊤
      (fun _ _ => CoPset.mem_full) $$ [Hp3 Hl3 HrdR HF3] with Ht3
    · iframe; iframe #
    ihave Htt : iprop(threadTok) $$ [Ht0 Ht1 Ht2 Ht3 Ht4]
    · iapply (threadTok_level0 (GF := GF)).2
      iframe Ht0
      iapply (threadTokFrom_succ (GF := GF) 1 (by omega)).2
      iframe Ht1
      iapply (threadTokFrom_succ (GF := GF) 2 (by omega)).2
      iframe Ht2
      iapply (threadTokFrom_succ (GF := GF) 3 (by omega)).2
      iframe
    rcases rerr with ei | _
    · icases Hrerr with (%h | ⟨#Hse, #Hso⟩)
      · cases h
      wp_auto
      rw [Hsi]
      wp_auto
      wp_bind (App (Val #(methods si.ty go!"Context" si.v)) (Val #()))
      iapply HCtx
      · itrivial
      iintro !> -
      wp_auto
      icases (threadTok_lend4 (GF := GF) HT4) $$ Htt with ⟨Hl4r, Hback⟩
      wp_apply +noauto HErr $$ [$Hl4r] as %cerr Hl4r
      ihave Htt := Hback $$ Hl4r
      wp_auto
      wp_apply hICE as %b -
      wp_if_destruct
      · wp_apply hZE as %f -
        wp_apply wp_slice_literal (l := [f])
        isplitr
        · ipureintro; rfl
        iintro %fs -
        wp_auto
        wp_apply hZW R.lg _ _ $$ []
        · iframe #
        wp_apply wp_slice_literal (V := GoString) [go!"receive", go!"watch"]
        isplitr
        · ipureintro; rfl
        iintro %lsl ⟨Hlsl, -⟩
        wp_auto
        wp_apply hCV cvF _ [go!"Type", go!"API"] _ _ $$ [Hlsl] as %c ⟨%ci', %Hc, #Hcs, -⟩
        · iframe #; iframe Hlsl; ipureintro
          exact ⟨HcvFl, prometheus.labelValuesOk_two _ _ _ _ (by decide) (by decide)⟩
        subst Hc
        iunfold prometheus.counterSpec at Hcs
        icases Hcs with ⟨#Hcs, -⟩
        wp_apply Hcs
        wp_apply wp_spsc_send γerr errc PE (fun _ => iprop(False)) [] (GoInterface.ok ei) $$ [$HprodE Hprod]
          as -
        · iframe #
          isplitr
          · iexact Hse
          isplitr
          · iexact Hso
          iexists _; iexact Hprod
        iframe Htt; imodintro; ipureintro; exact isPanic_intoVal _
      · wp_apply hZE as %f -
        wp_apply wp_slice_literal (l := [f])
        isplitr
        · ipureintro; rfl
        iintro %fs -
        wp_auto
        wp_apply hZD R.lg _ _ $$ []
        · iframe #
        wp_apply wp_spsc_send γerr errc PE (fun _ => iprop(False)) [] (GoInterface.ok ei) $$ [$HprodE Hprod]
          as -
        · iframe #
          isplitr
          · iexact Hse
          isplitr
          · iexact Hso
          iexists _; iexact Hprod
        iframe Htt; imodintro; ipureintro; exact isPanic_intoVal _
    · wp_auto
      iframe Htt; imodintro; ipureintro; exact isPanic_intoVal _
  iunfold v3rpc.ctxCanceledPtr at Hcanc
  icases Hcanc with ⟨%eC, #HeC, %HeCp⟩
  iunfold v3rpc.statusMsgErrVar at HmWC
  icases HmWC with ⟨%eWC, #HeWC, #HeWCm, #HeWCs⟩
  ihave #HsvW := go_etcd_io.etcd.cache.v3.srvErrOk_of_statusErrOk (GF := GF) _ $$ HeWCs
  ihave #Pes : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #HCtxE := applyErrIs_of_isCtxErr $$ Pes
  rw [Hsi]
  wp_auto
  wp_bind (App (Val #(methods si.ty go!"Context" si.v)) (Val #()))
  iapply HCtx
  · itrivial
  iintro !> -
  wp_auto
  wp_apply +noauto HDone as %chD %γD #HcD
  wp_auto_lc 2
  ihave #HerrcC : isChan errc γerr.chanName GoInterface $$ [HspscE]
  · unfold isSpsc; icases HspscE with ⟨$, -⟩
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `err = <-errc`: the receive loop's error
    simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, errc, γerr.chanName
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact HerrcC
    iapply spsc_rcv_au γerr errc PE (fun _ => iprop(False)) [] _ $$ HspscE [$Hlc1 $Hlc2] HconsE
    inext
    iintro %ve %okE Hv
    cases okE <;> simp only [Bool.false_eq_true, if_true, if_false]
    · icases Hv with ⟨Hf, -⟩
      iexfalso; iexact Hf
    icases Hv with ⟨⟨#HseE, #HsoE, %sentE, HprodC⟩, -⟩
    ihave #HsvE := go_etcd_io.etcd.cache.v3.srvErrOk_of_statusErrOk $$ HsoE
    wp_auto
    -- `errors.Is(err, context.Canceled)` over the stream error's tree (`streamErr`; `Canceled`'s
    -- value is a pointer error), then the assignment of `ErrGRPCWatchCanceled` when it holds
    iunfold v3rpc.streamErr at HseE
    icases HseE with ⟨-, #HseT⟩
    ihave ⟨%S, %M, #Ht, %HS⟩ := HseT $$ %(GoInterface.ok eC)
    wp_apply hIsT S M ve (GoInterface.ok eC) (fun tii h => by cases h; exact HeCp)
      (HS.2 (fun tii h => by cases h; exact HeCp)) $$ [] as %bC -
    · iframe #; ipureintro; exact HS.1
    wp_if_destruct
    rotate_left
    all_goals try wp_auto
    all_goals (
      wp_apply wp_spsc_close γctrl ctrl P' (fun _ => iprop(True)) sentE $$ [$HprodC]
      · iframe #
      watch_tail)
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `<-stream.Context().Done()`
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, chD, γD
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply context.isContextDone_is_chan $$ HcD
    iapply context.isContextDone_receive _ _ _ _ $$ HcD
    iintro ⟨#HPD, #HCC⟩
    wp_auto
    wp_bind (App (Val #(methods si.ty go!"Context" si.v)) (Val #()))
    iapply HCtx
    · itrivial
    iintro !> -
    wp_auto
    wp_apply +noauto HErrDone $$ [$HCC] [$Hl4] as %cerr %- #HcE Hl4
    ihave #HsvC := v3rpc.srvErrOk_of_weakErr $$ [] %cerr HcE
    · iframe #
    wp_auto
    icases HcE with (#HcE | #HcE)
    · canceled_check cerr
      all_goals watch_tail
    -- etcd's no-leader error: `errors.Is` on a status error
    ihave #HcS := v3rpc.statusErrOk_of_noLeaderErr $$ [] %cerr HcE
    · iframe #
    wp_apply hIsS cerr (GoInterface.ok eC) (Or.inr (Or.inl ⟨eC, rfl, HeCp⟩)) $$ [] as %bC -
    · iframe #
    wp_if_destruct
    rotate_left
    all_goals try wp_auto
    all_goals watch_tail
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
