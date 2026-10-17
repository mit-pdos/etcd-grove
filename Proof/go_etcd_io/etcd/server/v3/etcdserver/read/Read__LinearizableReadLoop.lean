/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/read/Read__LinearizableReadLoop.lean`.
Lean-first (no Rocq counterpart); the request path's unit 4a.

etcd PR #22242 (2026-10-17, branch `pr-verify/etcd-22242`): the loop logs a slow iteration's trace
from a logger goroutine it starts, over a one-slot channel `traceC`, with a nonblocking send (the
trace dropped, `droppedReadLoopTraces.Inc()`, if the slot is taken), and closes `traceC` on return
(`defer`). The channel is Perennial's SPSC idiom (`isSpsc`), the loop its producer and the logger its
consumer: each value sent carries its trace's ownership (`traceSent`), which `Trace.Log` consumes,
and the loop keeps the producer's token across iterations (the loop invariant) for the deferred
`close`. The spec is unchanged.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.read.Read__LinearizableReadLoop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.read.Read__requestCurrentIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.read.newNotifier
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.read.notifier__notify
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.read.isStopped
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.EnsureTrace
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__Step
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__AddField
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__Log
public import Spec.strconv.FormatUint
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.read.SpscNonblocking

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.read

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.read.Assumptions]

/-- What a value sent on `traceC` carries: its trace, owned (the loop does not touch a trace after
handing it off). -/
abbrev traceSent (_ : Int) (t : Loc) : IProp GF :=
  iprop(∃ e : Bool, traceutil.ownTrace t e)

set_option hygiene false in
/-- After the applied index reached `ci` (`Hai'`, `Hle'`): `nr.notify(nil)`, the trace's last step,
the trace handed to the logger if the iteration was slow (the nonblocking send, or the drop), the
next iteration. -/
local macro "loop_tail" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply hNotify nc γn γr GoInterface.nil $$ [Hown]
  · iframe #; iframe Hown
    iintro -
    iunfold frozenOk
    iexists n, ci, _, gs
    iframe Hfz Hlf Hai' Hwit
    ipureintro; constructor <;> word
  (try wp_auto)
  wp_apply hStep t false _ slice.nil $$ [Htrc] as Htrc
  · iframe Htrc; iapply traceutil.ownFields_nil
  (try wp_auto)
  wp_apply (lc := 2) _root_.Perennial.time.wp_Since as %el -
  (try wp_auto)
  wp_if_destruct
  · (try wp_auto)
    wp_apply_core chan.wp_select_nonblocking
    isplit
    · iapply BigAndL.bigAndL_singleton.2
      simp only [chan.nonblockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, tc, γs.chanName, t
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iexact HtcCh
      unfold nonblockingSendAu
      isplit
      · ihave Hlcs : (£ 1 ∗ £ 1 : IProp GF) $$ [Hlc1 Hlc2]
        · iframe
        ihave Hsnd : (spscProducer γs sent ∗ traceSent sent.length t : IProp GF) $$ [Hprod Htrc]
        · iframe Hprod; iexists false; iexact Htrc
        iapply spsc_nonblocking_send_au γs tc traceSent (fun _ => iprop(True)) sent t _ $$ Hspsc
          Hlcs Hsnd
        inext
        iintro Hprod
        (try wp_auto)
        wp_for_post
        iframe
        iexists _
        iexact Hprod
      · itrivial
    · (try wp_auto)
      wp_apply HIncD
      (try wp_auto)
      wp_for_post
      iframe
      iexists _
      iexact Hprod
  · wp_for_post
    iframe
    iexists _
    iexact Hprod))

set_option hygiene false in
/-- A return: the deferred `close(traceC)` with the producer's token. -/
local macro "loop_ret" : tactic => `(tactic| (
  (try wp_auto)
  (try wp_for_post)
  wp_apply wp_spsc_close (t := go.GoType.PointerType go_etcd_io.etcd.pkg.v3.traceutil.Trace.ty)
    γs tc traceSent (fun _ => iprop(True)) sent $$ [Hprod]
  · iframe #; iframe Hprod
  (try wp_auto)
  iapply HΦ
  itrivial))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem read.Read.LinearizableReadLoop.wp_proof
    (hET : traceutil.EnsureTrace.spec (GF := GF) (hG := hG))
    (hNN : read.newNotifier.spec (GF := GF) (hG := hG))
    (hRCI : read.Read.requestCurrentIndex.spec (GF := GF) (hG := hG))
    (hStopped : read.isStopped.spec (GF := GF) (hG := hG))
    (hNotify : read.notifier.notify.spec (GF := GF) (hG := hG))
    (hStep : traceutil.Trace.Step.spec (GF := GF) (hG := hG))
    (hAdd : traceutil.Trace.AddField.spec (GF := GF) (hG := hG))
    (hFU : strconv.FormatUint.spec (GF := GF) (hG := hG))
    (hLog : traceutil.Trace.Log.spec (GF := GF) (hG := hG)) :
    read.Read.LinearizableReadLoop.spec (GF := GF) (hG := hG) := by
  intro r γr RQ LR NR
  wp_start as ⟨#Hpre, HLR, #HNRu⟩
  ihave #Hpre' := Hpre
  iunfold isReadLoopPre at Hpre'
  icases Hpre' with ⟨%srv, %rf, %wc, %γw, #Hsf, #Hsrv, #Hrf, #Hraft, #Hwcf, #Hbag, #Hinv, #Hguard,
    #Hcci, #Hcomp, -⟩
  iunfold isReadServer at Hsrv
  icases Hsrv with ⟨-, %si, %Hsi, #HStopping, #HLC, -, #HLg, #HAI, #HAW, -, -⟩
  subst Hsi
  iunfold srvStopOk at HStopping
  iunfold srvChanOkR at HLC
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Ptu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  ihave #Pstr : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  ihave #Ptime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave Hinit : (go_etcd_io.etcd.server.v3.etcdserver.read.readInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, -, -, -, -, -, -, -, -, ⟨%cD, #HcD, #HcDs⟩⟩
  iunfold go_etcd_io.etcd.server.v3.storage.mvcc.counterSpec at HcDs
  icases HcDs with ⟨#HIncD, -⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  -- `traceC := make(chan *traceutil.Trace, 1)`: an SPSC channel of owned traces
  wp_apply chan.wp_make2 (V := Loc) (W64 1) $$ [] as %tc %γc ⟨#HtcCh, %Hcap, Hown⟩
  · ipureintro; decide
  imod start_spsc tc traceSent (fun _ => iprop(True)) γc $$ HtcCh [Hown]
    with ⟨%γs, #Hspsc, Hprod, Hcons⟩
  · iright; iexact Hown
  ihave #HtcCh' : isChan tc γs.chanName Loc $$ [Hspsc]
  · unfold isSpsc; icases Hspsc with ⟨$, -⟩
  iclear HtcCh
  irename HtcCh' => HtcCh
  (try wp_auto)
  ipersist traceC
  -- the logger goroutine: `for t := range traceC { t.Log() }`
  wp_apply wp_fork $$ [Hcons]
  · wp_auto
    ihave HIc : (∃ (recv : List Loc) (tv : Loc),
        "Hcons" ∷ spscConsumer γs recv ∗ "t" ∷ t_ptr ↦ tv : IProp GF) $$ [Hcons t]
    · iexists [], _
      iframe
    wp_for HIc
    wp_apply wp_spsc_receive (t := go.GoType.PointerType go_etcd_io.etcd.pkg.v3.traceutil.Trace.ty)
      γs tc traceSent (fun _ => iprop(True)) recv $$ [Hcons] as %v %ok H
    · iframe # ∗
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases H with ⟨-, %Hv⟩
      wp_auto
      wp_for_post
      itrivial
    · simp only [↓reduceIte]
      icases H with ⟨⟨%e, Htv⟩, Hcons⟩
      wp_auto
      wp_apply hLog v e $$ [Htv]
      · iframe #; iexact Htv
      (try wp_auto)
      wp_for_post
      iframe
      iexists _, _
      iframe
  (try wp_auto)
  ihave HI : (∃ sent : List Loc, "Hprod" ∷ spscProducer γs sent : IProp GF) $$ [Hprod]
  · iexists []
    iexact Hprod
  wp_for HI
  wp_apply (lc := 3) HLC $$ [$HLR] as %lcn ⟨#Hlcn, HLR⟩
  wp_apply HStopping as %stc #Hstc
  ihave #Hlcnc := Hlcn
  ihave #Hstcc := Hstc
  iunfold bcastChan at Hlcnc
  iunfold stopChan at Hstcc
  icases Hlcnc with ⟨%γlc, #Hlcn'⟩
  icases Hstcc with ⟨%γst, #Hstc'⟩
  wp_apply_core chan.wp_select_blocking
  -- `<-leaderChangedNotifier`: continue
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, lcn, γlc
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ Hlcn'
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hlcn'
    iintro ⟨-, -⟩
    wp_auto
    wp_for_post
    iframe
    iexists _
    iexact Hprod
  -- `<-r.waitC`: a client waits
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, wc, γw
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hbag
    iapply bag_recv_au γw wc _ _ $$ [$Hlc1 $Hlc2] Hbag
    inext
    iintro %u -
    wp_auto
    wp_apply _root_.Perennial.time.wp_Now as %tnow -
    (try wp_auto)
    wp_apply context.wp_Background
    wp_apply HLg $$ [$HLR] as %lg ⟨%Hlg, HLR⟩
    wp_apply hET context.backgroundCtxVal mvcc.neverCd none false lg _ slice.nil $$ []
      as %ctx' %t ⟨⟨%Ht, -⟩, Htrc, -⟩
    · iframe #
      isplitl []
      · iunfold mvcc.txnCtx
        ileft
        iunfold mvcc.doneNil
        iintro !> %Φ' !> - HΦ'
        iapply context.wp_background_Done $$ [] HΦ'
        itrivial
      isplitl []
      · iapply traceutil.ctxTraceIs_background
      isplitl []
      · simp only [traceutil.ownTraceOpt]; itrivial
      iapply traceutil.ownFields_nil
    wp_apply hNN γr as %nc' ⟨%γn', #Hnis', Hown', Hauth', Hlist'⟩
    wp_apply sync.RWMutex.wp_Lock_guard (readMuAddr r) (readMuP r γr) $$ [] as ⟨Hwl, HP⟩
    · iframe #
    iunfold readMuP at HP
    icases HP with ⟨%nc, %γn, Hpt, Hg⟩
    wp_auto
    imod read_swap γr nc γn nc' γn' $$ Hinv Hlc3 Hg Hnis' Hown' Hauth' Hlist'
      with ⟨Hg, Hown, %n, %gs, #Hfz, #Hcn, #Hlf, #Hregs⟩
    ihave #Hcomp' := Hcomp
    iunfold readCompose at Hcomp'
    ihave #HRA := Hcomp' $$ %gs Hregs
    wp_apply sync.RWMutex.wp_Unlock_guard (readMuAddr r) (readMuP r γr) $$ [Hwl Hpt Hg]
    · iframe #; iframe Hwl; iunfold readMuP; iexists nc', γn'; iframe Hpt Hg
    wp_apply hRCI r γr RQ LR NR lcn n (readQs gs) $$ [HLR] as %ci %err ⟨HLR, #HaE, Hci⟩
    · iframe #; iframe HLR
    wp_apply hStopped err $$ [] as %bst -
    · iframe #
    cases bst
    rotate_left
    · loop_ret
    cases err with
    | ok ei =>
      wp_auto
      wp_apply hNotify nc γn γr (GoInterface.ok ei) $$ [Hown]
      · iframe #; iframe Hown; iintro %h; cases h
      wp_for_post
      iframe
      iexists _
      iexact Hprod
    | nil =>
    ihave ⟨%Hci', #Hwit⟩ := Hci $$ %rfl
    wp_auto
    wp_apply hStep t false _ slice.nil $$ [$Htrc] as Htrc
    · iapply traceutil.ownFields_nil
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fs1 ⟨Hfs1, -⟩
    (try wp_auto)
    wp_apply hAdd t false _ _ _ $$ [$Htrc $Hfs1] as ⟨Htrc, -⟩
    · ipureintro; exact traceutil.fieldsWf_cons_int _ _ _ (.uint64 _) _ traceutil.fieldsWf_nil
    (try wp_auto)
    wp_apply HAI as %ai #Hai
    wp_apply hFU as %str -
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fs2 ⟨Hfs2, -⟩
    (try wp_auto)
    wp_apply hAdd t false _ _ _ $$ [$Htrc $Hfs2] as ⟨Htrc, -⟩
    · ipureintro; exact traceutil.fieldsWf_cons_string _ _ _ traceutil.fieldsWf_nil
    (try wp_auto)
    wp_if_destruct
    · wp_apply HAW $$ %ci as %awc ⟨%Qaw, #Hawc, #Hawq⟩
      wp_apply HStopping as %stc2 #Hstc2
      iunfold bcastChan at Hawc
      iunfold stopChan at Hstc2
      icases Hawc with ⟨%γaw, #Hawc⟩
      icases Hstc2 with ⟨%γst2, #Hstc2⟩
      wp_apply_core chan.wp_select_blocking
      iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, awc, γaw
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply ownBroadcastChan_is_chan $$ Hawc
        iapply broadcast_chan_receive _ _ _ _ _ $$ Hawc
        iintro ⟨#HQaw, -⟩
        ihave #Hai' := Hawq $$ HQaw
        have Hle' : uint.Z ci ≤ uint.Z ci := Int.le_refl _
        loop_tail
      iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stc2, γst2
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply ownStopChan_is_chan $$ Hstc2
        iapply stop_chan_receive _ _ _ _ _ $$ Hstc2
        iintro ⟨-, -⟩
        loop_ret
      iapply BigAndL.bigAndL_nil.2
      itrivial
    · ihave #Hai' := Hai
      loop_tail
  -- `<-r.server.Stopping()`: return
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stc, γst
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownStopChan_is_chan $$ Hstc'
    iapply stop_chan_receive _ _ _ _ _ $$ Hstc'
    iintro ⟨-, -⟩
    loop_ret
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
