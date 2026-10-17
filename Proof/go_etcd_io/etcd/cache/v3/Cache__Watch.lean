/-
Proof of `Spec/Cache__Watch.lean`: the end-to-end `Watch` theorem. Lean-first (no Rocq
counterpart).

Every channel `Watch` returns is an SPSC channel of `cacheWatchElem`s (`cacheWatch_alloc`), with
the log of what is sent on it (`fwd`). The goroutine's loop keeps the watcher's consumer, the SPSC
producer and `fwd` in step (`vs.length = rcv.length`, `fwd` holds `rcv`): it forwards each
response it receives from the watcher (`watcher_recv_au`, whose publication `demuxPub` is the
response's `cacheWatchLog`), then the compaction's cancel response after the close, if any. The
wait group's `Add`/`Done` are `wp_cacheWg_Add`/`wp_cacheWg_Done`; the deferred calls are joined
over the `IsProgressNotify` branch as `watchDeferOk`, the timer as `watchTimerOk`.

The rejected request's cancel response calls `err.Error()` on `validateWatch`'s error:
`validateResult` gives `errorStringSpec` for `fmt.Errorf`'s error (Perennial's `wp_Errorf`), and
the package facts give it for `ErrKeyRangeInvalid` (`validateErrorString_holds`).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Cache__Watch
public import Spec.go_etcd_io.etcd.cache.v3.Cache__WaitReady
public import Spec.go_etcd_io.etcd.client.v3.OpWatch
public import Spec.go_etcd_io.etcd.client.v3.Op__Rev
public import Spec.go_etcd_io.etcd.client.v3.Op__IsProgressNotify
public import Spec.go_etcd_io.etcd.client.v3.Op__IsPrevKV
public import Spec.go_etcd_io.etcd.cache.v3.Cache__attachPrevKV
public import Spec.context.AfterFunc
public import Perennial.Proof.context.Results
public import Spec.go_etcd_io.etcd.cache.v3.Cache__validateWatch
public import Spec.go_etcd_io.etcd.cache.v3.newWatcher
public import Spec.go_etcd_io.etcd.cache.v3.demux__Register
public import Spec.go_etcd_io.etcd.cache.v3.demux__Unregister
public import Spec.go_etcd_io.etcd.cache.v3.demux__BroadcastProgressTo

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

-- `wp_load` from a persistent struct points-to (see `Cache__waitTillRevision.lean`).
attribute [-instance] Config.Config_access_store_PerWatcherBufferSize
  Config.Config_access_store_ProgressNotifyInterval

/-- A new channel as `Cache.Watch`'s: an SPSC channel of `cacheWatchElem`s, the log of what is sent
on it (`fwd`) empty, with the producer's and the consumer's views. -/
theorem cacheWatch_alloc (ch : Loc) (γch : ChanNames) (C : DemuxCert GF)
    (pred : Option (GoString → Bool)) (sr : w64) (pk : Option GoString) :
    ⊢ isChan ch γch go_etcd_io.etcd.client.v3.WatchResponse -∗
      (ownChan γch go_etcd_io.etcd.client.v3.WatchResponse .Idle ∨
        ownChan γch go_etcd_io.etcd.client.v3.WatchResponse (.Buffered [])) ={⊤}=∗
      ∃ γ : CacheWatchNames, isCacheWatchChan ch γ C pred sr pk ∗
        spscProducer γ.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
        monoListAuthOwn γ.fwd 1 ([] : List RespModel) ∗ cacheWatchConsumer γ C pred sr pk [] := by
  iintro #Hch Hoc
  imod mono_list_own_alloc (GF := GF) ([] : List RespModel) with ⟨%γf, Hauth, #Hlb⟩
  imod start_spsc (V := go_etcd_io.etcd.client.v3.WatchResponse) ch
    (fun i v => cacheWatchElem (GF := GF) ⟨⟨γch, γf, γf⟩, γf⟩ C pred sr pk i v) (fun _ => iprop(True))
    γch $$ Hch Hoc with ⟨%γs, #Hspsc, Hprod, Hcons⟩
  imodintro
  iexists ⟨γs, γf⟩
  iframe Hprod Hauth
  isplitr
  · unfold isCacheWatchChan
    rw [show cacheWatchElem (GF := GF) ⟨γs, γf⟩ C pred sr pk =
      (fun i v => cacheWatchElem (GF := GF) ⟨⟨γch, γf, γf⟩, γf⟩ C pred sr pk i v) from rfl]
    iexact Hspsc
  unfold cacheWatchConsumer
  iexists []
  iframe Hcons Hlb
  isplitr
  · ipureintro; rfl
  ileft; ipureintro; rfl

/-- The cancel response `Cache.Watch` sends for a request `validateWatch` rejects: canceled, no
events, an empty header. -/
def rejectModel : RespModel :=
  { events := [], compactRev := W64 0, canceled := true, created := false, hdrRev := W64 0 }

/-- What `Cache.Watch` needs of `validateWatch`'s errors and its spec (`validateResult`) does not
say: `Error()` on a non-nil error it returns (`ErrKeyRangeInvalid`, or `fmt.Errorf`'s wrapping
of `ErrUnsupportedRequest`) returns some string. Not provable from the current vocabulary. -/
def validateErrorString : Prop :=
  ∀ (u : Bool) (pfx key re : GoString) (f : GoFunc) (e : GoInterfaceOk),
    (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      validateResult u pfx key re f (GoInterface.ok e)) ⊢ errorStringSpec e

theorem validateErrorString_holds : validateErrorString (GF := GF) (hG := hG) := by
  intro u pfx key re f e
  iintro ⟨#Hpkg, #Hval⟩
  ihave Hci : (cacheInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hci with ⟨-, -, -, -, #HKR, -⟩
  unfold validateResult
  split
  · icases Hval with ⟨-, %e', %He', #HS⟩
    cases He'
    iexact HS
  · split
    · icases Hval with ⟨%Hv, -⟩
      cases Hv.1
    · icases Hval with ⟨-, #Hp⟩
      iapply HKR $$ Hp

/-- The deferred calls of `Watch`'s goroutine (`c.demux.Unregister(w)`, `close(responseChan)`,
`c.waitGroup.Done()`, and `progressTimer.Stop()` if there is a timer): run with the goroutine's
running token, its demux token and registration, and the channel's producer; the `Done` hands
back the thread token the goroutine exits with. -/
def watchDeferOk (cf : CacheFields) (γd : DemuxNames) (cap : Nat) (w : Loc) (γw : WatcherNames)
    (pred : Option (GoString → Bool)) (sR : w64) (γs : SpscNames) (d : GoFunc) : IProp GF :=
  iprop({{ cacheWgRunning cf ∗ demuxHandle cf.demux γd cap (cacheCert cf) ∗
      demuxRegistered γd w γw pred sR ∗
      (∃ sent : List go_etcd_io.etcd.client.v3.WatchResponse, spscProducer γs sent) }}
    (App (Val #d) (Val #()))
    {{ RET #(); threadTok }})

instance watchDeferOk_persistent (cf : CacheFields) (γd : DemuxNames) (cap : Nat) (w : Loc)
    (γw : WatcherNames) (pred : Option (GoString → Bool)) (sR : w64) (γs : SpscNames) (d : GoFunc) :
    Persistent (watchDeferOk (GF := GF) cf γd cap w γw pred sR γs d) := by
  unfold watchDeferOk; infer_instance

/-- `progressTimer` and `progressChan` of `Watch`'s goroutine: nil (no progress notifications), or a
timer and its channel. -/
def watchTimerOk (pt : GoInterface) (pc : Loc) : IProp GF :=
  iprop(⌜pt = GoInterface.nil ∧ pc = chan.nil⌝ ∨
    ∃ (t : GoInterfaceOk) (γt : ChanNames), ⌜pt = GoInterface.ok t⌝ ∗ isTimer t ∗
      isChanBag γt pc (V := time.Time) (fun _ => iprop(True)))

instance watchTimerOk_persistent (pt : GoInterface) (pc : Loc) :
    Persistent (watchTimerOk (GF := GF) pt pc) := by
  unfold watchTimerOk; infer_instance

theorem demuxPub_pub (C : DemuxCert GF) (pred : Option (GoString → Bool)) (sr : w64) :
    (demuxPub C pred sr).pub = demuxPubBody C pred sr := rfl

/-- The next response on `Cache.Watch`'s channel, after `vs` (modelled by `L`): `r`, which extends
the log to `L ++ [r]`. -/
theorem cacheWatchElem_intro (γ : CacheWatchNames) (C : DemuxCert GF)
    (pred : Option (GoString → Bool)) (sr : w64) (pk : Option GoString)
    (vs : List go_etcd_io.etcd.client.v3.WatchResponse)
    (L : List RespModel) (r : RespModel) (v : go_etcd_io.etcd.client.v3.WatchResponse)
    (h : vs.length = L.length) :
    respAt v r ∗ respPK pk v r ∗ monoListLbOwn γ.fwd (L ++ [r]) ∗ cacheWatchLog C pred sr pk (L ++ [r]) ⊢
      cacheWatchElem γ C pred sr pk vs.length v := by
  iintro ⟨#Hr, #Hpk, #Hlb, #Hlog⟩
  unfold cacheWatchElem
  iexists L ++ [r], r
  iframe Hr Hpk Hlb Hlog
  ipureintro
  rw [h]
  simp

/-- A response whose events slice is `nil` and whose model has no events has every event's
`PrevKv` (`respPK`). -/
theorem respPK_nil_events (pk : Option GoString) (v : go_etcd_io.etcd.client.v3.WatchResponse)
    (r : RespModel) (hv : v.Events' = slice.nil) (hr : r.events = []) :
    ⊢ respPK (GF := GF) pk v r := by
  cases pk with
  | none => unfold respPK; iintro; itrivial
  | some pfx =>
    unfold respPK respPrevKvs
    iintro
    iexists []
    rw [hv]
    isplitl
    · iapply ownSlice_nil
    isplitl
    · ipureintro; rw [hr]; rfl
    imodintro
    iintro %i %ev %e %Hi
    simp at Hi

set_option hygiene false in
/-- `Watch`'s goroutine sends the response `rv` (modelled by `r`, the next one of the watcher's
log, `Hra`, with its `PrevKv`s `Hpk`) on `responseChan`, or returns once `mergedCtx` is done;
after the send, the loop invariant with `rv` sent. -/
local macro "watch_send" rv:term : tactic => `(tactic| (
  wp_apply +noauto HDoneM as %ch3 %γ3 #Hdone3
  wp_auto_lc 3
  imod monoListAuthOwn_update_app (GF := GF) [r] $$ Hauth with ⟨Hauth, #Hlb⟩
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `<-mergedCtx.Done()`: return
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch3, γ3
    isplit
    · ipureintro; rfl
    isplit
    · iapply context.isContextDone_is_chan $$ Hdone3
    iapply context.isContextDone_receive _ _ _ _ $$ Hdone3
    iintro -
    (try wp_auto)
    wp_for_post
    wp_apply Hd $$ [Hrtok Hh Hreg Hprod] as Htok
    · iframe Hrtok Hh Hreg; iexists vs; iexact Hprod
    iexact Htok
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `responseChan <- resp`, and the timer reset
    simp only [chan.blockingClausePre]
    iexists go_etcd_io.etcd.client.v3.WatchResponse, inferInstance, inferInstance, inferInstance,
      inferInstance, ch, γ.spsc.chanName, $rv
    isplit
    · ipureintro; exact ⟨rfl, rfl⟩
    isplit
    · iexact HrcCh
    iapply spsc_send_au γ.spsc ch _ _ vs $rv _ $$ HrcS [Hlc1 Hlc2 Hlc3] [Hprod]
    · iframe Hlc1 Hlc2 Hlc3
    · iframe Hprod
      iapply cacheWatchElem_intro γ _ _ _ _ vs rcv r $rv Hlen
      iframe Hra Hpk Hlb
      unfold cacheWatchLog
      ileft
      iapply demuxPubBody_cacheCert cf
      rw [← demuxPub_pub]
      iexact Hpub
    inext
    iintro Hprod
    icases Htm with (⟨%Hpt, %Hpc⟩ | ⟨%t, %γt, %Hpt, #Ht, #Hbag⟩)
    · subst Hpt
      (try wp_auto)
      wp_for_post
      iframe
      iexists rcv ++ [r], vs ++ [$rv]
      iframe
      ipureintro; simp [Hlen]
    · subst Hpt
      (try wp_auto)
      ihave #Ht' := Ht
      iunfold isTimer at Ht'
      icases Ht' with ⟨-, #HtReset, -⟩
      wp_apply HtReset as %b -
      wp_for_post
      iframe
      iexists rcv ++ [r], vs ++ [$rv]
      iframe
      ipureintro; simp [Hlen]
  iapply BigAndL.bigAndL_nil.2
  itrivial))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem Cache.Watch.wp_proof
    (wp_WaitReady : Cache.WaitReady.spec (GF := GF) (hG := hG))
    (wp_OpWatch : OpWatch.spec (GF := GF) (hG := hG))
    (wp_Rev : Op.Rev.spec (GF := GF) (hG := hG))
    (wp_validateWatch : Cache.validateWatch.spec (GF := GF) (hG := hG))
    (wp_newWatcher : newWatcher.spec (GF := GF) (hG := hG))
    (wp_Register : demux.Register.spec (GF := GF) (hG := hG))
    (wp_IsProgressNotify : Op.IsProgressNotify.spec (GF := GF) (hG := hG))
    (wp_BroadcastProgressTo : demux.BroadcastProgressTo.spec (GF := GF) (hG := hG))
    (wp_Unregister : demux.Unregister.spec (GF := GF) (hG := hG))
    (wp_IsPrevKV : Op.IsPrevKV.spec (GF := GF) (hG := hG))
    (wp_attachPrevKV : Cache.attachPrevKV.spec (GF := GF) (hG := hG))
    (wp_AfterFunc : context.AfterFunc.spec (GF := GF) (hG := hG)) :
    Cache.Watch.spec (GF := GF) (hG := hG) := by
  intro c cf γr γd cap ctx s key sl gs q
  wp_start as ⟨#Hc, #Hctx, #Hopts, %Hnp, Hslot, Hrdr, Hopen, Htok⟩
  ihave #Hcl : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hc' := Hc
  iunfold isCacheFields at Hc'
  iNamed Hc'
  iclear Hstop HisStop
  imod monoNatLbOwn_0 (GF := GF) γr.epoch with #Hep0
  wp_auto
  wp_apply wp_WaitReady c cf γr γd cap 0 ctx s $$ [$Hc $Hctx] as %err Herr
  · unfold readyEpochLb; iexact Hep0
  iunfold readyWaitResult at Herr
  icases Herr with (⟨%Hnil, -⟩ | ⟨%Hne, -, -⟩)
  rotate_left
  · -- not ready, the context is done: an empty, closed channel
    obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    wp_apply chan.wp_make1 (V := go_etcd_io.etcd.client.v3.WatchResponse) as %ch %γch ⟨#Hch, %_, Hoc⟩
    imod cacheWatch_alloc ch γch (etcdStepCert cf.pfx)
      (some (keyPredForRange key (opWatchModel key gs).base.rangeEnd)) (opWatchModel key gs).base.rev
      (watchPK (opWatchModel key gs).base cf.pfx) $$ Hch [Hoc] with ⟨%γ, #Hrc, Hprod, -, Hcons⟩
    · ileft; iexact Hoc
    wp_apply wp_spsc_close γ.spsc ch (cacheWatchElem γ (etcdStepCert cf.pfx)
        (some (keyPredForRange key (opWatchModel key gs).base.rangeEnd)) (opWatchModel key gs).base.rev
        (watchPK (opWatchModel key gs).base cf.pfx))
        (fun _ => iprop(True)) [] $$ [Hprod]
    · iunfold isCacheWatchChan at Hrc
      iframe Hrc Hprod
    try wp_auto
    iapply HΦ
    iframe Hopen Htok
    iexists γ
    iframe Hrc Hcons
  subst Hnil
  wp_auto
  wp_apply wp_OpWatch key sl gs $$ [$Hopts] as %op #HopF
  · ipureintro; exact Hnp
  generalize Ho : (opWatchModel key gs) = of at *
  iunfold opFullAt at HopF
  icases HopF with ⟨#HopAt, -, -⟩
  wp_apply wp_Rev op_ptr op of.base (DFrac.own 1) $$ [$op $HopAt] as op
  wp_apply wp_validateWatch c cf γr γd cap key op of.base $$ [$Hc $HopAt] as %f %verr #Hval
  by_cases hvn : verr = GoInterface.nil
  focus
    subst hvn
    ihave #Hpred : iprop(⌜f ≠ func.nil⌝ ∗ keyPredSpec f (keyPredForRange key of.base.rangeEnd)) $$ []
    · iunfold validateResult at Hval
      cases hu : of.base.watchUnsupported
      · simp only [Bool.false_eq_true, ↓reduceIte] at *
        cases hv : validRange cf.pfx key of.base.rangeEnd
        · simp only [Bool.false_eq_true, ↓reduceIte] at *
          icases Hval with ⟨-, #HeKR'⟩
          ihave Hci : (cacheInit : IProp GF) $$ []
          · iapply isPkgInit_access $$ Hpkg
          icases Hci with ⟨-, -, ⟨%eKR, #HeKR⟩, -⟩
          icombine HeKR HeKR' gives %Heq
          cases Heq
        · simp only [↓reduceIte] at *
          icases Hval with ⟨%Hf, #Hks⟩
          iframe Hks
          ipureintro; exact Hf.2
      · simp only [↓reduceIte] at *
        icases Hval with ⟨-, %e, %he, -⟩
        cases he
    icases Hpred with ⟨%Hfnn, #Hks⟩
    ihave #Hcfg' := Hcfg
    iStructNamedPrefix Hcfg' "Cfg"
    wp_auto
    wp_apply wp_IsPrevKV op_ptr op of.base (DFrac.own 1) $$ [$op $HopAt] as op
    wp_apply wp_newWatcher cf.cfg.PerWatcherBufferSize' f (some (keyPredForRange key of.base.rangeEnd))
      (demuxPub (cacheCert cf) (some (keyPredForRange key of.base.rangeEnd)) of.base.rev)
      as %w %γw ⟨#Hw, Hwopen, Hwcons, Hwuniq⟩
    · isplitr
      · ipureintro; exact Hbuf
      isplitr
      · unfold keyPredOk
        isplitr
        · ipureintro; exact Hfnn
        iexact Hks
      imodintro
      unfold demuxPub
      iapply demuxPubBody_nil
    unfold cacheWatchSlot
    icases Hslot with ⟨Hh, Hwgslot⟩
    wp_apply wp_Register cf.demux γd cap (cacheCert cf) w γw
      (some (keyPredForRange key of.base.rangeEnd)) of.base.rev
      $$ [$Hpkg $HisDemux $Hh $Hw $Hwopen $Hwuniq] as ⟨Hh, %sR, %M, Hreg, %HsR⟩
    wp_apply chan.wp_make1 (V := go_etcd_io.etcd.client.v3.WatchResponse) as %ch %γch ⟨#Hch, %_, Hoc⟩
    imod cacheWatch_alloc ch γch (etcdStepCert cf.pfx)
      (some (keyPredForRange key of.base.rangeEnd)) of.base.rev (watchPK of.base cf.pfx)
      $$ Hch [Hoc] with ⟨%γ, #Hrc, Hprod, Hauth, Hcons⟩
    · ileft; iexact Hoc
    wp_apply wp_cacheWg_Add c cf q Hthreads $$ [$Hsync $HisWg $HwgInv $Hwgslot $Hopen $Htok] as ⟨Hrtok, Hopen⟩
    ipersist c
    ipersist ctx
    ipersist op
    ipersist w
    ipersist responseChan
    ipersist needPrevKV
    wp_apply wp_fork_tok_self $$ [Hrtok Hh Hreg Hwcons Hprod Hauth Hrdr] as Htok
    · wp_auto
      wp_apply wp_with_defer as %defer defer
      ihave Hdef : iprop(∃ d, defer ↦ d ∗ watchDeferOk cf γd cap w γw
          (some (keyPredForRange key of.base.rangeEnd)) sR γ.spsc d) $$ [defer]
      · iexists _
        iframe defer
        unfold watchDeferOk
        imodintro
        iintro %Ψ ⟨Hrtok, Hh, Hreg, %sent, Hprod⟩ HΨ
        (try wp_auto)
        wp_apply wp_Unregister cf.demux γd cap (cacheCert cf) w γw
          (some (keyPredForRange key of.base.rangeEnd)) sR $$ [$Hpkg $HisDemux $Hh $Hreg] as ⟨Hh, -⟩
        wp_apply wp_spsc_close γ.spsc ch (cacheWatchElem γ (etcdStepCert cf.pfx)
            (some (keyPredForRange key of.base.rangeEnd)) of.base.rev (watchPK of.base cf.pfx))
            (fun _ => iprop(True)) sent $$ [Hprod]
        · iunfold isCacheWatchChan at Hrc
          iframe Hrc Hprod
        wp_apply wp_cacheWg_Done c cf $$ [$Hsync $HisWg $HwgInv $Hrtok] as Htok
        iapply HΨ
        iexact Htok
      icases Hdef with ⟨%d0, defer, #Hd0⟩
      -- `mergedCtx, mergedCancel := context.WithCancel(ctx)`; `defer mergedCancel()`
      ihave #Hcpkg : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
      · iPkgInit
      wp_apply context.wp_WithCancel_any ctx s $$ [$Hcpkg $Hctx] as %mctx %γm %mcancel ⟨#Hmc, #Hmctx⟩
      (try wp_auto)
      -- `stop := context.AfterFunc(c.internalCtx, mergedCancel)`; `defer stop()`
      icases HisICtx with ⟨%ics, #Hictx2, -⟩
      wp_apply wp_AfterFunc cf.ictx ics #mcancel $$ [$Hcpkg $Hictx2] as %stop #Hstop
      · imodintro
        iunfold _root_.Perennial.context.cancelSpec at Hmc
        wp_apply Hmc
        · itrivial
        iintro -
        itrivial
      (try wp_auto)
      ihave Hdef : iprop(∃ d, defer ↦ d ∗ watchDeferOk cf γd cap w γw
          (some (keyPredForRange key of.base.rangeEnd)) sR γ.spsc d) $$ [defer]
      · iexists _
        iframe defer
        unfold watchDeferOk
        imodintro
        iintro %Ψ Hpre HΨ
        (try wp_auto)
        wp_apply Hstop as %b
        iunfold _root_.Perennial.context.cancelSpec at Hmc
        wp_apply Hmc
        · itrivial
        iintro -
        wp_apply Hd0 $$ [$Hpre] as Htok
        iapply HΨ
        iexact Htok
      icases Hdef with ⟨%d1, defer, #Hd1⟩
      wp_join iprop(∃ (pt : GoInterface) (pc : Loc) (d : GoFunc), progressTimer_ptr ↦ pt ∗
          progressChan_ptr ↦ pc ∗ defer ↦ d ∗ watchTimerOk pt pc ∗
          watchDeferOk cf γd cap w γw (some (keyPredForRange key of.base.rangeEnd)) sR γ.spsc d)
        at next with [progressTimer progressChan defer]
        as ⟨%pt, %pc, %d, progressTimer, progressChan, defer, #Htm, #Hd⟩
      · wp_apply wp_IsProgressNotify op_ptr op of.base DFrac.discard $$ [$op $HopAt] as op'
        cases hpn : of.base.progressNotify
        rotate_left
        · -- `progressTimer = c.clock.NewTimer(...)`, `defer progressTimer.Stop()`, its channel
          ihave #Hclk := HisClock
          iunfold isClock at Hclk
          (try wp_auto)
          wp_apply Hclk as %t #Ht
          ihave #Ht' := Ht
          iunfold isTimer at Ht'
          icases Ht' with ⟨#HtChan, #HtReset, #HtStop⟩
          wp_apply HtChan as %tc %γt #Hbag
          isplitr
          · ipureintro; rfl
          iexists GoInterface.ok t, tc, _
          iframe progressTimer progressChan defer
          isplitr
          · unfold watchTimerOk
            iright
            iexists t, γt
            iframe Ht Hbag
            ipureintro; rfl
          unfold watchDeferOk
          imodintro
          iintro %Ψ Hpre HΨ
          (try wp_auto)
          wp_apply HtStop as %b -
          wp_apply Hd1 $$ [$Hpre] as Htok
          iapply HΨ
          iexact Htok
        · wp_auto
          isplitr
          · ipureintro; rfl
          iexists GoInterface.nil, zero_val GoChan, d1
          iframe progressTimer defer Hd1
          isplitl [progressChan]
          · iexact progressChan
          unfold watchTimerOk
          ileft
          ipureintro; exact ⟨rfl, rfl⟩
      ipersist progressTimer
      ipersist progressChan
      ipersist defer
      iunfold watchDeferOk at Hd
      iunfold watchTimerOk at Htm
      ihave #HrcS := Hrc
      iunfold isCacheWatchChan at HrcS
      ihave #HrcCh : isChan ch γ.spsc.chanName go_etcd_io.etcd.client.v3.WatchResponse $$ []
      · ihave #H := HrcS
        unfold isSpsc
        icases H with ⟨$, -⟩
      ihave #Hw' := Hw
      iunfold isWatcher at Hw'
      icases Hw' with ⟨%wch, %wf, #HrespCh, -⟩
      ihave #Hm1 := Hmctx
      iunfold context.isContext at Hm1
      iunfold context.isContextDef at Hm1
      icases Hm1 with ⟨-, #HDoneM, -, -⟩
      ihave HI : iprop(∃ (rcv : List RespModel) (vs : List go_etcd_io.etcd.client.v3.WatchResponse),
          watcherConsumer γw rcv ∗ spscProducer γ.spsc vs ∗ ⌜vs.length = rcv.length⌝ ∗
          monoListAuthOwn γ.fwd 1 rcv ∗ demuxHandle cf.demux γd cap (cacheCert cf) ∗
          demuxRegistered γd w γw (some (keyPredForRange key of.base.rangeEnd)) sR ∗ cacheWgRunning cf ∗
          watchReader cf of.base)
        $$ [Hwcons Hprod Hauth Hh Hreg Hrtok Hrdr]
      · iexists [], []
        iframe
        ipureintro; rfl
      wp_for HI
      icases HI with ⟨Hwcons, Hprod, %Hlen, Hauth, Hh, Hreg, Hrtok, Hrdr⟩
      wp_apply +noauto HDoneM as %ch1 %γ1 #Hdone1
      wp_auto_lc 2
      wp_apply_core chan.wp_select_blocking_nil
      iapply BigAndL.bigAndL_cons.2
      isplit
      · -- `<-mergedCtx.Done()`: return
        ileft
        simp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch1, γ1
        isplit
        · ipureintro; rfl
        isplit
        · iapply context.isContextDone_is_chan $$ Hdone1
        iapply context.isContextDone_receive _ _ _ _ $$ Hdone1
        iintro -
        (try wp_auto)
        wp_for_post
        wp_apply Hd $$ [$Hrtok $Hh $Hreg Hprod] as Htok
        · iexists vs; iexact Hprod
        iexact Htok
      iapply BigAndL.bigAndL_cons.2
      isplit
      · -- `<-progressChan`: a progress notification to `w`, and the timer reset
        icases Htm with (⟨%Hpt, %Hpc⟩ | ⟨%t, %γt, %Hpt, #Ht, #Hbag⟩)
        · iright
          iapply chan.nilClausePre_recv time.Time _ _ Hpc
        ileft
        simp only [chan.blockingClausePre]
        iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, pc, γt
        isplit
        · ipureintro; rfl
        isplit
        · iapply is_bag_is_chan $$ Hbag
        iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hbag
        inext
        iintro %tm -
        (try wp_auto)
        wp_apply wp_BroadcastProgressTo cf.demux γd cap (cacheCert cf) w γw
          (some (keyPredForRange key of.base.rangeEnd)) sR $$ [$Hpkg $HisDemux $Hh $Hreg] as ⟨Hh, Hreg⟩
        subst Hpt
        ihave #Ht' := Ht
        iunfold isTimer at Ht'
        icases Ht' with ⟨-, #HtReset, -⟩
        wp_apply HtReset as %b -
        wp_for_post
        iframe
        iexists rcv, vs
        iframe
        ipureintro; exact Hlen
      iapply BigAndL.bigAndL_cons.2
      isplit
      · -- `resp, ok := <-w.respCh`
        ileft
        simp only [chan.blockingClausePre]
        iexists go_etcd_io.etcd.client.v3.WatchResponse, inferInstance, inferInstance, inferInstance,
          inferInstance, wch, γw.ch
        isplit
        · ipureintro; rfl
        isplit
        · iapply isWatcher_isChan w wch γw _ _ $$ [$Hw $HrespCh]
        iapply watcher_recv_au w wch γw _ _ rcv $$ Hw HrespCh Hwcons
        iintro %resp %ok Hres
        unfold watcherRecvResult
        cases ok
        · -- closed: forward the compaction's cancel response, if any, and return
          simp only [Bool.false_eq_true, ↓reduceIte]
          icases Hres with ⟨%cl, Hwcons, #Hclosed, #Hpubc⟩
          (try wp_auto)
          wp_apply wp_watcher_cancelResp w γw _ _ rcv cl $$ Hw Hclosed as %p #Hp
          wp_if_destruct
          · -- no cancel response (`Stop`)
            wp_for_post
            wp_apply Hd $$ [$Hrtok $Hh $Hreg Hprod] as Htok
            · iexists vs; iexact Hprod
            iexact Htok
          -- the compaction's cancel response
          rcases cl with _ | n
          · iunfold cancelAt at Hp
            icases Hp with %Hpn
            subst Hpn
            exfalso; simp_all
          iunfold cancelAt at Hp
          icases Hp with ⟨%cv, #Hpv, #Hcv⟩
          wp_apply HDoneM as %ch3 %γ3 #Hdone3
          wp_apply +noauto wp_watcher_cancelResp w γw _ _ rcv (some n) $$ Hw Hclosed as %p' #Hp'
          iunfold cancelAt at Hp'
          icases Hp' with ⟨%cv', #Hpv', #Hcv'⟩
          wp_auto_lc 3
          imod monoListAuthOwn_update_app (GF := GF) [cancelModel n] $$ Hauth with ⟨Hauth, #Hlb⟩
          wp_apply_core chan.wp_select_blocking
          iapply BigAndL.bigAndL_cons.2
          isplit
          · -- `<-mergedCtx.Done()`
            simp only [chan.blockingClausePre]
            iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch3, γ3
            isplit
            · ipureintro; rfl
            isplit
            · iapply context.isContextDone_is_chan $$ Hdone3
            iapply context.isContextDone_receive _ _ _ _ $$ Hdone3
            iintro -
            (try wp_auto)
            wp_for_post
            wp_apply Hd $$ [$Hrtok $Hh $Hreg Hprod] as Htok
            · iexists vs; iexact Hprod
            iexact Htok
          iapply BigAndL.bigAndL_cons.2
          isplit
          · -- `responseChan <- *w.cancelResp`
            simp only [chan.blockingClausePre]
            iexists go_etcd_io.etcd.client.v3.WatchResponse, inferInstance, inferInstance, inferInstance,
              inferInstance, ch, γ.spsc.chanName, cv'
            isplit
            · ipureintro; exact ⟨rfl, rfl⟩
            isplit
            · iexact HrcCh
            iapply spsc_send_au γ.spsc ch _ _ vs cv' _ $$ HrcS [$Hlc1 $Hlc2 $Hlc3] [Hprod]
            · iframe Hprod
              iapply cacheWatchElem_intro γ _ _ _ _ vs rcv (cancelModel n) cv' Hlen
              unfold respSent
              icases Hcv' with ⟨#Hcv', -⟩
              iframe Hcv' Hlb
              isplitr
              · iapply respPK_of_no_events _ _ _ rfl $$ Hcv'
              unfold cacheWatchLog
              iright; ileft
              iexists rcv, n
              isplitr
              · ipureintro; rfl
              iapply demuxPubBody_cacheCert cf
              rw [← demuxPub_pub]
              iexact Hpubc
            inext
            iintro Hprod
            (try wp_auto)
            wp_for_post
            wp_apply Hd $$ [$Hrtok $Hh $Hreg Hprod] as Htok
            · iexists vs ++ [cv']; iexact Hprod
            iexact Htok
          iapply BigAndL.bigAndL_nil.2
          itrivial
        · simp only [↓reduceIte]
          icases Hres with ⟨%r, #Hr, Hwcons, #Hpub⟩
          ihave #Hr' := Hr
          unfold respSent
          icases Hr' with ⟨#Hra, -⟩
          (try wp_auto)
          cases hpk : of.base.prevKV
          · -- no `WithPrevKV`: forward the response as it is
            ihave #Hpk : respPK (watchPK of.base cf.pfx) resp r $$ []
            · unfold watchPK respPK; rw [hpk]; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
            (try wp_auto)
            watch_send resp
          · -- `WithPrevKV`: `c.attachPrevKV(mergedCtx, &resp)`
            have hpk' : watchPK of.base cf.pfx = some cf.pfx := by simp [watchPK, hpk]
            have hrd : watchReader (GF := GF) (hG := hG) cf of.base = cacheReader cf := by
              simp [watchReader, hpk]
            rw [hrd]
            (try wp_auto)
            ihave #Hcr : eventsCreateRevAt resp.Events' r.events $$ []
            · -- **Unfinished** (`sorry`): the `CreateRevision` of the delivered events. The events
              -- come from etcd's watch stream through the demux, but `eventAt` (`InvStore.lean`),
              -- which the stream model (`InvEtcd.lean`, `WatchContent.lean`) and the demux carry, has
              -- only the fields the store reads (`Type`, `Kv`, its `Key` and `ModRevision`); the
              -- server's `kvPtrFixed` has the whole `KeyValue`, so extending `eventAt` with
              -- `CreateRevision` would discharge this.
              sorry
            wp_apply wp_attachPrevKV c cf γr γd cap mctx _ resp_ptr resp r
              $$ [$Hpkg $Hc $Hmctx $Hrdr $resp $Hra $Hcr] as %aerr ⟨Hrdr, %resp', resp, Hares⟩
            icases Hares with (⟨%Haerr, #Hra2, #Hpv⟩ | ⟨%ae, %Haerr, #HaeS⟩)
            · subst Haerr
              (try wp_auto)
              ihave #Hpk : respPK (watchPK of.base cf.pfx) resp' r $$ []
              · rw [hpk']; unfold respPK; iexact Hpv
              iclear Hra
              ihave #Hra := Hra2
              watch_send resp'
            · -- the lookup failed: a cancel response with its error, and return
              subst Haerr
              (try wp_auto)
              wp_apply HDoneM as %ch3 %γ3 #Hdone3
              iunfold errorStringSpec at HaeS
              wp_apply +noauto HaeS as %reason
              wp_auto_lc 3
              imod monoListAuthOwn_update_app (GF := GF) [rejectModel] $$ Hauth with ⟨Hauth, #Hlb⟩
              wp_apply_core chan.wp_select_blocking
              iapply BigAndL.bigAndL_cons.2
              isplit
              · -- `<-mergedCtx.Done()`
                simp only [chan.blockingClausePre]
                iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch3, γ3
                isplit
                · ipureintro; rfl
                isplit
                · iapply context.isContextDone_is_chan $$ Hdone3
                iapply context.isContextDone_receive _ _ _ _ $$ Hdone3
                iintro -
                (try wp_auto)
                wp_for_post
                wp_apply Hd $$ [$Hrtok $Hh $Hreg Hprod] as Htok
                · iexists vs; iexact Hprod
                iexact Htok
              iapply BigAndL.bigAndL_cons.2
              isplit
              · -- `responseChan <- WatchResponse{Canceled: true, CancelReason: err.Error()}`
                simp only [chan.blockingClausePre]
                iexists go_etcd_io.etcd.client.v3.WatchResponse, inferInstance, inferInstance,
                  inferInstance, inferInstance, ch, γ.spsc.chanName, _
                isplit
                · ipureintro; exact ⟨rfl, rfl⟩
                isplit
                · iexact HrcCh
                iapply spsc_send_au γ.spsc ch _ _ vs _ _ $$ HrcS [$Hlc1 $Hlc2 $Hlc3] [Hprod]
                · iframe Hprod
                  iapply cacheWatchElem_intro γ _ _ _ _ vs rcv rejectModel _ Hlen
                  iframe Hlb
                  isplitr
                  · unfold respAt eventsAt hdrAt
                    isplitl
                    · iexists []
                      isplitl
                      · iapply ownSlice_nil
                      isplitl
                      · ipureintro; rfl
                      imodintro
                      iintro %i %ev %e %Hev
                      simp at Hev
                    isplitl
                    · ileft; ipureintro; exact ⟨rfl, rfl⟩
                    ipureintro
                    exact ⟨rfl, rfl, rfl⟩
                  isplitr
                  · iapply (respPK_nil_events _ _ _ rfl rfl)
                  unfold cacheWatchLog
                  iright; iright; iright
                  iexists rcv, r, rejectModel
                  isplitr
                  · ipureintro; exact ⟨by rw [hpk']; simp, rfl, rfl, rfl⟩
                  iapply demuxPubBody_cacheCert cf
                  rw [← demuxPub_pub]
                  iexact Hpub
                inext
                iintro Hprod
                (try wp_auto)
                wp_for_post
                wp_apply Hd $$ [$Hrtok $Hh $Hreg Hprod] as Htok
                · iexists vs ++ [_]; iexact Hprod
                iexact Htok
              iapply BigAndL.bigAndL_nil.2
              itrivial
      iapply BigAndL.bigAndL_nil.2
      itrivial
    iapply HΦ
    iframe Hopen Htok
    iexists γ
    iframe Hrc Hcons
  obtain ⟨e, rfl⟩ : ∃ e, verr = GoInterface.ok e := by
    cases verr with
    | nil => exact absurd rfl hvn
    | ok e => exact ⟨e, rfl⟩
  ihave #HeS := validateErrorString_holds _ _ _ _ _ e $$ [$Hpkg $Hval]
  (try wp_auto)
  wp_apply chan.wp_make2 (V := go_etcd_io.etcd.client.v3.WatchResponse) (W64 1) as
    %ch %γch ⟨#Hch, %_, Hoc⟩
  · ipureintro; decide
  imod cacheWatch_alloc ch γch (etcdStepCert cf.pfx)
    (some (keyPredForRange key of.base.rangeEnd)) of.base.rev (watchPK of.base cf.pfx)
    $$ Hch [Hoc] with ⟨%γ, #Hrc, Hprod, Hauth, Hcons⟩
  · iright; iexact Hoc
  ihave %Hhnn := typedPointsto_not_null $$ «$v0»
  iStructNamed «$v0»
  ipersist Revision
  iunfold errorStringSpec at HeS
  wp_apply HeS as %reason
  imod monoListAuthOwn_update_app (GF := GF)
    [rejectModel] $$ Hauth with ⟨Hauth, #Hlb⟩
  wp_apply wp_spsc_send γ.spsc ch (cacheWatchElem γ (etcdStepCert cf.pfx)
      (some (keyPredForRange key of.base.rangeEnd)) of.base.rev (watchPK of.base cf.pfx))
      (fun _ => iprop(True)) [] _ $$ [Hprod] as Hprod
  · iunfold isCacheWatchChan at Hrc
    iframe Hrc Hprod
    unfold cacheWatchElem
    iexists [] ++ [rejectModel], rejectModel
    isplitl
    · unfold respAt eventsAt hdrAt
      isplitl
      · iexists []
        isplitl
        · iapply ownSlice_nil
        isplitl
        · ipureintro; rfl
        imodintro
        iintro %i %ev %e %Hev
        simp at Hev
      isplitl
      · iright
        isplitl
        · ipureintro; exact Hhnn
        rw [show rejectModel.hdrRev = (zero_val go_etcd_io.etcd.api.v3.etcdserverpb.ResponseHeader).Revision' from rfl]
        iexact Revision
      ipureintro
      exact ⟨rfl, rfl, rfl⟩
    isplitr
    · iapply (respPK_nil_events _ _ _ rfl rfl)
    isplitr
    · ipureintro; simp
    iframe Hlb
    unfold cacheWatchLog
    iright; iright; ileft
    ipureintro; exact ⟨_, rfl, rfl, rfl⟩
  wp_apply wp_spsc_close γ.spsc ch (cacheWatchElem γ (etcdStepCert cf.pfx)
      (some (keyPredForRange key of.base.rangeEnd)) of.base.rev (watchPK of.base cf.pfx))
      (fun _ => iprop(True)) _ $$ [Hprod]
  · iunfold isCacheWatchChan at Hrc
    iframe Hrc Hprod
  iapply HΦ
  iframe Hopen Htok
  iexists γ
  iframe Hrc Hcons

end proof

end EtcdGrove
end Perennial
