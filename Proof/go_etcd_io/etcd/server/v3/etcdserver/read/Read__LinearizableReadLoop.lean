/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/read/Read__LinearizableReadLoop.lean`.
Lean-first (no Rocq counterpart); the request path's unit 4a.
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
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__LogAllStepsIfLong
public import Spec.strconv.FormatUint

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

set_option hygiene false in
/-- After the applied index reached `ci` (`Hai'`, `Hle'`): `nr.notify(nil)`, the trace, the next
iteration. -/
local macro "loop_tail" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply hNotify nc γn γr GoInterface.nil $$ [Hown]
  · iframe #; iframe Hown
    iintro -
    iunfold frozenOk
    iexists n, _
    iframe Hfz Hai'
    ipureintro; word
  (try wp_auto)
  wp_apply hStep t _ _ $$ []
  · iframe #; ipureintro; exact Ht
  (try wp_auto)
  wp_apply hLog t _ $$ []
  · iframe #; ipureintro; exact Ht
  (try wp_auto)
  wp_for_post
  iframe))

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
    (hLog : traceutil.Trace.LogAllStepsIfLong.spec (GF := GF) (hG := hG)) :
    read.Read.LinearizableReadLoop.spec (GF := GF) (hG := hG) := by
  intro r γr RQ LR NR
  wp_start as ⟨#Hpre, HLR, #HNRu⟩
  ihave #Hpre' := Hpre
  iunfold isReadLoopPre at Hpre'
  icases Hpre' with ⟨%srv, %rf, %wc, %γw, #Hsf, #Hsrv, #Hrf, #Hraft, #Hwcf, #Hbag, #Hinv, #Hguard,
    #Hcci⟩
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
  wp_auto
  wp_for
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
    wp_apply context.wp_Background
    wp_apply HLg $$ [$HLR] as %lg ⟨%Hlg, HLR⟩
    wp_apply hET context.backgroundCtxVal mvcc.neverCd lg _ _ $$ [] as %ctx' %t ⟨%Ht, -⟩
    · iframe #
      iunfold mvcc.txnCtx
      ileft
      iunfold mvcc.doneNil
      iintro !> %Φ' !> - HΦ'
      iapply context.wp_background_Done $$ [] HΦ'
      itrivial
    wp_apply hNN γr as %nc' ⟨%γn', #Hnis', Hown', Hauth'⟩
    wp_apply sync.RWMutex.wp_Lock_guard (readMuAddr r) (readMuP r γr) $$ [] as ⟨Hwl, HP⟩
    · iframe #
    iunfold readMuP at HP
    icases HP with ⟨%nc, %γn, Hpt, Hg⟩
    wp_auto
    imod read_swap γr nc γn nc' γn' $$ Hinv Hlc3 Hg Hnis' Hown' Hauth' with ⟨Hg, Hown, %n, #Hfz, #Hcn⟩
    wp_apply sync.RWMutex.wp_Unlock_guard (readMuAddr r) (readMuP r γr) $$ [Hwl Hpt Hg]
    · iframe #; iframe Hwl; iunfold readMuP; iexists nc', γn'; iframe Hpt Hg
    wp_apply hRCI r γr RQ LR NR lcn n $$ [HLR] as %ci %err ⟨HLR, #HaE, %Hci⟩
    · iframe #; iframe HLR
    wp_apply hStopped err $$ [] as %bst -
    · iframe #
    cases bst
    rotate_left
    · wp_auto
      wp_for_post
      iapply HΦ
      itrivial
    cases err with
    | ok ei =>
      wp_auto
      wp_apply hNotify nc γn γr (GoInterface.ok ei) $$ [Hown]
      · iframe #; iframe Hown; iintro %h; cases h
      wp_for_post
      iframe
    | nil =>
    have Hci' := Hci rfl
    wp_auto
    wp_apply hStep t _ _ $$ []
    · iframe #; ipureintro; exact Ht
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fs1 ⟨-, -⟩
    (try wp_auto)
    wp_apply hAdd t _ $$ []
    · iframe #; ipureintro; exact Ht
    (try wp_auto)
    wp_apply HAI as %ai #Hai
    wp_apply hFU as %str -
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fs2 ⟨-, -⟩
    (try wp_auto)
    wp_apply hAdd t _ $$ []
    · iframe #; ipureintro; exact Ht
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
        wp_auto
        wp_for_post
        iapply HΦ
        itrivial
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
    wp_auto
    wp_for_post
    iapply HΦ
    itrivial
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
