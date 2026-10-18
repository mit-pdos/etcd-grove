/-
Proof of the spec of the same name (the watch slice's unit W-S): the run of a watch stream, its two
goroutines and the shutdown. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer__Watch
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverWatchStream__recvLoop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverWatchStream__sendLoop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverWatchStream__close
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.isClientCtxErr
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__NewWatchStream
public import Spec.errors.IsCtxErr
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.Error
public import Spec.github_com.prometheus.client_golang.prometheus.CounterVec__WithLabelValues

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
  wp_apply hClose sws_ptr r (W32 0 + W32 1) iprop(True ∗ True) $$ [Hopen Hcc Hadd]
  · iframe #; iframe
  iapply HΦ
  iexact Hspec))

set_option hygiene false in
/-- `errors.Is(err, context.Canceled)` on a typed `err`, then the assignment of
`ErrGRPCWatchCanceled` when it holds. -/
local macro "canceled_check" e:term : tactic => `(tactic| (
  wp_apply hIs $e (GoInterface.ok eC) (by assumption) $$ [] as %bC -
  · iframe #; try (ileft; iexact HeC)
  wp_if_destruct
  rotate_left
  all_goals try wp_auto))

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

set_option maxHeartbeats 0 in
theorem v3rpc.watchServer.Watch.wp_proof
    (hNWS : mvcc.watchableStore.NewWatchStream.spec (GF := GF) (hG := hG))
    (hRecv : v3rpc.serverWatchStream.recvLoop.spec (GF := GF) (hG := hG))
    (hSend : v3rpc.serverWatchStream.sendLoop.spec (GF := GF) (hG := hG))
    (hClose : v3rpc.serverWatchStream.close.spec (GF := GF) (hG := hG))
    (hICE : v3rpc.isClientCtxErr.spec (GF := GF) (hG := hG))
    (hIs : errors.IsCtxErr.spec (GF := GF) (hG := hG))
    (hZD : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (hZW : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG))
    (hCV : prometheus.CounterVec.WithLabelValues.spec (GF := GF) (hG := hG)) :
    v3rpc.watchServer.Watch.spec (GF := GF) (hG := hG) := by
  intro p R st γs Up Dn ci cd
  wp_start as ⟨#HWS, #Hstream, #Hspec, #Hup, Hrt, Hst, HAux, Hslot⟩
  ihave #HWS' := HWS
  iunfold v3rpc.isWatchServer at HWS'
  icases HWS' with ⟨%Hnn, #Plg, #Pcid, #Pmid, #Pmrb, #Psg, #Pwa, #Pag, #Hsrv⟩
  ihave #Hsrv' := Hsrv
  iunfold v3rpc.watchSrvOk at Hsrv'
  icases Hsrv' with ⟨#Hwsto, %Hγst, #Hrso, #Hauth, #Hvars, -⟩
  ihave #Pmvcc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply hNWS R.wsl R.E.s R.γ (v3rpc.progQ γs) (v3rpc.cancelQ γs) $$ [] as %wsp
    ⟨%γo, %ch, %γc, #Hwstream, #Hwch, #Hch, #Hchinv, Hopen, Hcons, %Hγoc5, #Hsp, #Hcq⟩
  · iframe #
  -- the run's answer tokens, and the stream's auxiliary name (the watch slice's unit W-C)
  imod v3rpc.ansPool_alloc (GF := GF) with ⟨%γa, HPool⟩
  imod v3rpc.streamAux_set γs (v3rpc.auxOf γo γa) $$ HAux with #HauxIs
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
  -- the control stream: an SPSC channel of control responses
  let P' : Int → Loc → IProp GF := fun _ l => iprop(∃ m : v3rpc.WatchRespM, v3rpc.watchRespMsg l m ∗
    ⌜m.hdr.clusterId = R.cid ∧ m.hdr.memberId = R.mid ∧ m.src = none⌝ ∗ v3rpc.ctrlOk γs R.γ m)
  imod start_spsc ctrl P' (fun _ => iprop(True)) γch $$ Hctrl [Hoc] with ⟨%γctrl, #Hspsc, Hprod, Hcons'⟩
  · iright; iexact Hoc
  -- `closec`: a broadcast channel
  imod alloc_broadcast_chan (E := ⊤) iprop(True) γcc cc $$ Hccc Hcco with Hcc
  ihave #HccU := ownBroadcastChan_Unknown _ _ _ _ $$ Hcc
  -- the lock over the maps
  imod sync.init_RWMutex (v3rpc.swsMu pm vm fm) (E := ⊤) (v3rpc.swsF sws_ptr go!"mu") $$ [Hpm Hvm Hfm] mu
    with Htoks
  · inext
    iunfold v3rpc.swsMu
    iexists ∅, ∅, ∅
    iframe
    ipureintro; intro id; simp
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
  have Hγoc : γo.ids = γc.ids ∧ γo.prog = γc.prog ∧ γo.sentl = γc.sentl ∧
      0 < sint.Z γc.ch.chanCap := ⟨Hγoc5.1, Hγoc5.2.1, Hγoc5.2.2.1, Hγoc5.2.2.2.2.2⟩
  let r : v3rpc.WRun GF := ⟨R, st, γs, Up, Dn, ci, cd, wsp, γo, γa, ch, γc, ctrl, γctrl, pm, vm, fm, cc, γcc⟩
  ihave #Hsws : v3rpc.swsIs sws_ptr r $$ []
  · iunfold v3rpc.swsIs
    iframe #
    isplitr
    · ipureintro; exact ⟨Hswsn, Hnn.2⟩
    have hP : v3rpc.ctrlP r = P' := by funext k l; rfl
    rw [hP]
    iframe Hspsc
    isplitr
    · ipureintro; exact Hγoc
    ipureintro; exact ⟨Hγoc5.2.2.2.2.1, Hγoc5.2.2.2.1⟩
  iunfold v3rpc.watchRunSlot at Hslot
  icases Hslot with ⟨Hrres, Hsres⟩
  wp_apply sync.join.WaitGroup.wp_Add iprop(True) (v3rpc.swsF sws_ptr go!"wg") iprop(True) (W32 0)
    $$ [$Hadd] as ⟨Hadd, Hdone⟩
  · iframe #; ipureintro; decide
  wp_apply wp_fork $$ [Hst Hcons' Hcons Hsres Hmutok Hdone]
  · wp_apply hSend sws_ptr r $$ [$Hst $Hcons' $Hcons $Hsres $Hmutok]
    · iframe #
    wp_apply sync.join.WaitGroup.wp_Done iprop(True) (v3rpc.swsF sws_ptr go!"wg") $$ [$Hdone]
    · iframe #; itrivial
  -- the stream's methods and its context
  ihave #Hstream' := Hstream
  iunfold v3rpc.srvStreamIs at Hstream'
  icases Hstream' with ⟨%si, %Hsi, #HRecv, #HSend, #HCtx, #Hctxis, #Hrunctx⟩
  ihave #Hctx2 := Hctxis
  iNamed Hctx2
  ihave #HErrU := HErr $$ %Broadcast.Unknown
  ipersist stream
  iunfold v3rpc.watchVars at Hvars
  icases Hvars with ⟨#Heof, #Hwpv⟩
  iunfold v3rpc.watchPkgVars at Hwpv
  icases Hwpv with ⟨#HeInv, #HeOld, #HeEmpty, #HeDenied, #HeEWR, #HeDup, #HmCompacted,
    #HmInv, #HmOld, #HmEmpty, #HmDenied, #HmWC, #HstreamF, #Hh1, #Hh2, #Hh3, #Hh4, #Htracer,
    #Hcanc, #Hguard'⟩
  icases HstreamF with ⟨%cvF, #HcvF⟩
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
    iprop(⌜context.isTypedErr e⌝ ∗ ∃ sent : List Loc, spscProducer γctrl sent)
  imod start_spsc errc PE (fun _ => iprop(False)) γe $$ Herrc [Hoe]
    with ⟨%γerr, #HspscE, HprodE, HconsE⟩
  · iright; iexact Hoe
  ipersist errc
  wp_apply wp_fork $$ [Hrt Hprod HPool Hrres HprodE]
  · wp_apply hRecv sws_ptr r [] [] $$ [$Hrt $Hprod $HPool $Hrres] as %rerr ⟨%Hrerr, %sent', Hprod⟩
    · iframe #
    rcases rerr with ei | _
    · have Hty : context.isTypedErr (GoInterface.ok ei) := by
        rcases Hrerr with h | h
        · cases h
        · exact h
      wp_auto
      rw [Hsi]
      wp_auto
      wp_bind (App (Val #(methods si.ty go!"Context" si.v)) (Val #()))
      iapply HCtx
      · itrivial
      iintro !> -
      wp_auto
      wp_apply +noauto HErrU $$ [] as %cerr -
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
        · iframe #; ipureintro; exact Hnn.2
        wp_apply wp_slice_literal (V := GoString) [go!"receive", go!"watch"]
        isplitr
        · ipureintro; rfl
        iintro %lsl -
        wp_auto
        wp_apply hCV cvF _ as %c ⟨%ci', %Hc, #Hcs⟩
        subst Hc
        iunfold prometheus.counterSpec at Hcs
        wp_apply Hcs
        wp_apply wp_spsc_send γerr errc PE (fun _ => iprop(False)) [] (GoInterface.ok ei) $$ [$HprodE Hprod]
          as -
        · iframe #
          isplitr
          · ipureintro; exact Hty
          iexists _; iexact Hprod
        itrivial
      · wp_apply hZE as %f -
        wp_apply wp_slice_literal (l := [f])
        isplitr
        · ipureintro; rfl
        iintro %fs -
        wp_auto
        wp_apply hZD R.lg _ _ $$ []
        · iframe #; ipureintro; exact Hnn.2
        wp_apply wp_spsc_send γerr errc PE (fun _ => iprop(False)) [] (GoInterface.ok ei) $$ [$HprodE Hprod]
          as -
        · iframe #
          isplitr
          · ipureintro; exact Hty
          iexists _; iexact Hprod
        itrivial
    · wp_auto
      itrivial
  iunfold v3rpc.ctxCanceledPtr at Hcanc
  icases Hcanc with ⟨%eC, #HeC, %HeCp⟩
  iunfold v3rpc.msgErrVar at HmWC
  icases HmWC with ⟨%eWC, #HeWC, #HeWCm⟩
  have Hctrlc : ∀ (k : Int) (l : Loc), v3rpc.ctrlP r k l = P' k l := fun _ _ => rfl
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
    icases Hv with ⟨⟨%HtyE, %sentE, HprodC⟩, -⟩
    wp_auto
    canceled_check ve
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
    wp_apply +noauto HErrDone $$ [$HCC] as %cerr %HtyC
    wp_auto
    canceled_check cerr
    all_goals watch_tail
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
