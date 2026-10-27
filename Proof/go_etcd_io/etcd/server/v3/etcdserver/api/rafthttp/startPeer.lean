/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/startPeer.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.startPeer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newPeerStatus
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newURLPicker
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newSnapshotSender
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.pipeline__start
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.startStreamWriter
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamReader__start
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.golang_org.x.time.rate.NewLimiter
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Error
public import Spec.context.WithCancelBackground
public import Perennial.Spec.context.Background

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

/-- The descriptor of a cancellable context of `Background()` (`WithCancelBackground`'s). -/
abbrev cancelCd (γ : context.ContextNames) : context.ContextDesc (IProp GF) :=
  { Values := ∅, Deadline := none, Done_gn := γ, PDone := iprop(True) }

set_option hygiene false in
/-- A log call: its fields' strings (`peerID.String()`), the call. -/
local macro "sp_log" : tactic => `(tactic| (
  repeat' (first
    | (wp_apply hIDStringPtr _ _ _ $$ [peerID] as %_ ⟨peerID, -⟩; iexact peerID)
    | (wp_apply hZString as %_ -)
    | (wp_apply hZError as %_ -)
    | (wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field); isplitr; (ipureintro; rfl);
       iintro %_ ⟨-, -⟩)
    | (wp_apply hInfo lg _ _ $$ []; (iframe #; ipureintro; exact Hlgnn))
    | (wp_apply hWarn lg _ _ $$ []; (iframe #; ipureintro; exact Hlgnn))
    | wp_auto)))

set_option hygiene false in
/-- A peer's receiving goroutine: `for { select { case mm := <-ch: r.Process(ctx, mm) ...;
case <-p.stopc: return } }`, holding a resource for its calls; `Hbag` the channel's bag. -/
local macro "proc_loop" ch:term "," γ:term : tactic => `(tactic| (
  (try wp_auto)
  wp_for_core
  (try wp_auto)
  cleanup_bool_decide
  wp_auto_lc 2
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, $ch, $γ
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hbag
    iapply bag_recv_au $$ [Hlc1 Hlc2] Hbag
    · iframe
    inext
    iintro %ml Hm
    (try wp_auto)
    ihave #HP1 := HProc $$ %ctx' %(cancelCd γc) %ml
    wp_bind (App (App (Val #(methods ri.ty go!"Process" ri.v)) (Val #(GoInterface.ok ctx')))
      (Val #ml))
    iapply HP1 $$ [HR7 Hm]
    · iframe HR7 Hm
      iunfold nodeCtx; iright; iexact Hctx
    inext
    iintro %err ⟨-, HR7⟩
    (try wp_auto)
    cases err with
    | ok ei =>
      (try wp_auto)
      rw [_root_.decide_eq_false Hlgnn]
      sp_log
      wp_for_post
      iframe
    | nil =>
      (try wp_auto)
      wp_for_post
      iframe
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sc, γs
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ Hsunk
    iapply broadcast_chan_receive $$ Hsunk
    iintro ⟨-, -⟩
    (try wp_auto)
    wp_for_post
    (try wp_auto)
    first | itrivial | (ipureintro; exact isPanic_intoVal _)
  iapply BigAndL.bigAndL_nil.2
  itrivial))

set_option hygiene false in
/-- A stream reader `$cr` of type `$ty` (its struct `Hcr`, its limiter `rl`/`Hrl`): its fields
read-only, its mutex over `srLockInv`, then `start`, giving `Hsr` and `Hstop`. -/
local macro "sp_reader" cr:term "," ty:term "," rl:term : tactic => `(tactic| (
  iStructNamedSuffix Hcr "R"
  ipersist lgR; ipersist peerIDR; ipersist typR; ipersist trR; ipersist pickerR; ipersist statusR
  ipersist recvcR; ipersist propcR; ipersist rlR
  imod sync.init_Mutex (srLockInv $cr) ⊤ ($cr.[rafthttp.streamReader, go!"mu"]) $$ muR
    [pausedR closerR] with #Hmu
  · inext; iunfold srLockInv; iexists _, _; iframe; ileft; ipureintro; rfl
  (try wp_auto)
  wp_apply hReaderStart Rh lid pid γd $cr $ty _ _ Hmem Hnp $$ [doneR errorcR ctxR cancelR]
    as ⟨#Hsr, #Hstop⟩
  · iframe
    iframe #
    isplitr
    · iunfold srFixed0
      iexists lg, t, ps, rcc, pcc, γr, γp
      iframe #
      ipureintro; exact Hlgnn
    ihave #Hidu : iprop(∃ lidT : w64, t.[rafthttp.Transport, go!"ID"] ↦□ lidT ∗
        ⌜trURLsOk Rh lidT tuvs⌝) $$ []
    · iexists lid; iframe #; ipureintro; exact Hturls
    iunfold srCfg
    iexists $rl, pk, t, turls, tuvs, cid, srt, ec
    iframe #
    (try iapply Hpreg)
  (try wp_auto)))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
theorem rafthttp.startPeer.wp_proof
    (hNewStatus : rafthttp.newPeerStatus.spec (GF := GF) (hG := hG))
    (hNewPicker : rafthttp.newURLPicker.spec (GF := GF) (hG := hG))
    (hNewSnap : rafthttp.newSnapshotSender.spec (GF := GF) (hG := hG))
    (hPipeStart : rafthttp.pipeline.start.spec (GF := GF) (hG := hG))
    (hStartSW : rafthttp.startStreamWriter.spec (GF := GF) (hG := hG))
    (hReaderStart : rafthttp.streamReader.start.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hNewLimiter : rate.NewLimiter.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (hZError : zap.Error.spec (GF := GF) (hG := hG))
    (hWithCancel : context.WithCancelBackground.spec (GF := GF) (hG := hG))
    (hBackground : context.Background.spec (GF := GF) (hG := hG)) :
    rafthttp.startPeer.spec (GF := GF) (hG := hG) := by
  intro Rh t lid γd R urls uvs pid fs Hne Hurls Hfs Hmem Hnp Hpm
  rw [show List.replicate 8 () = [(), (), (), (), (), (), (), ()] from rfl]
  wp_start as ⟨#Htr, #Hus, HRs⟩
  icases BigSepL.bigSepL_cons.1 $$ HRs with ⟨HR1, HRs⟩
  icases BigSepL.bigSepL_cons.1 $$ HRs with ⟨HR2, HRs⟩
  icases BigSepL.bigSepL_cons.1 $$ HRs with ⟨HR3, HRs⟩
  icases BigSepL.bigSepL_cons.1 $$ HRs with ⟨HR4, HRs⟩
  icases BigSepL.bigSepL_cons.1 $$ HRs with ⟨HR5, HRs⟩
  icases BigSepL.bigSepL_cons.1 $$ HRs with ⟨HR6, HRs⟩
  icases BigSepL.bigSepL_cons.1 $$ HRs with ⟨HR7, HRs⟩
  icases BigSepL.bigSepL_cons.1 $$ HRs with ⟨HR8, -⟩
  ihave #Htr' := Htr
  iunfold trFixed at Htr'
  icases Htr' with ⟨%lg, %ls, %ss, %turls, %tuvs, %cid, %r, %ec, %srt, %prt, %drf, %ppr, %spr, #Hlg, %Hlgnn,
    #Hlid, #HtURLs, #Htuvs, #Hcid, #Hr, #Hraft, #Hec, #Hsrt, #Hsrtok, #Hprt, #Hprtok, #Hdrf, #Hls,
    %Hlsnn, #Hss, %Hssnn, #Hppr, #Hspr, #Hreg, #Hpreg0, #HPfx, %HmemU⟩
  obtain ⟨Hmem, Hturls⟩ := HmemU
  have Hpp : Rh.member pid ∧ pid ≠ lid := ⟨Hpm, fun h => Hnp h.symm⟩
  ihave #Hpreg := Hpreg0 $$ %pid %Hpp
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  rw [_root_.decide_eq_false Hlgnn]
  sp_log
  wp_apply hNewStatus lg lid pid Hlgnn as %ps #Hps
  (try wp_auto)
  wp_apply hNewPicker urls uvs (peerURL Rh pid) Hne Hurls $$ [] as %pk #Hpk
  · iframe #
  (try wp_auto)
  -- the pipeline, started with four of the resources
  iStructNamedSuffix «$r0» "P"
  ipersist peerIDP; ipersist trP; ipersist pickerP; ipersist statusP; ipersist raftP
  ipersist errorcP; ipersist followerStatsP
  imod sync.init_WaitGroup (sync.join.wgjN.@"wg") («$r0_ptr».[rafthttp.pipeline, go!"wg"]) $$ wgP
    with ⟨%γwg, Hwg⟩
  imod sync.join.init _ γwg $$ Hwg with Hwg
  wp_apply hPipeStart Rh «$r0_ptr» pid R $$ [msgcP stopcP Hwg HR1 HR2 HR3 HR4] as Hpl
  · iframe
    iunfold pipeFixed
    iexists t, pk, ec, lg, turls, tuvs, lid, cid, prt, ps, fs, r, lid, γd
    iframe #
    isplitr
    · ipureintro; exact Hlgnn
    isplitr
    · ipureintro; exact ⟨Hmem, Hnp⟩
    ipureintro; exact Hturls
  (try wp_auto)
  obtain ⟨pl, hpl⟩ : ∃ pl : Loc, pl = «$r0_ptr» := ⟨_, rfl⟩
  subst hpl
  -- the two stream writers, each with a resource; the snapshot sender
  wp_apply hStartSW Rh .msgAppV2 lid pid R lg ps fs r γd $$ [HR5] as %cw2 ⟨#Hcw2, Hcw2s⟩
  · iframe #; iframe HR5; ipureintro; exact ⟨Hlgnn, Hfs⟩
  (try wp_auto)
  wp_apply hStartSW Rh .message lid pid R lg ps fs r γd $$ [HR6] as %cw1 ⟨#Hcw1, Hcw1s⟩
  · iframe #; iframe HR6; ipureintro; exact ⟨Hlgnn, Hfs⟩
  (try wp_auto)
  wp_apply hNewSnap Rh t lid γd R pk pid ps Hpm (fun h => Hnp h.symm) $$ [] as %sns ⟨#Hsns, Hsnstop⟩
  · iframe #
  (try wp_auto)
  -- the receive channels (bags of received messages) and the stop channel
  wp_apply (chan.wp_make2 (V := Loc) (W64 4096))
  · ipureintro; exact ⟨by decide, by decide⟩
  iintro %rcc %γr ⟨#Hrcc, %-, Hro⟩
  simp only [show ¬ (W64 4096 = W64 0) by decide, ↓reduceIte]
  imod start_bag (netRecv Rh.γn lid γd) _ rcc γr (by trivial) $$ Hrcc Hro with #Hrbag
  (try wp_auto)
  wp_apply (chan.wp_make2 (V := Loc) (W64 4096))
  · ipureintro; exact ⟨by decide, by decide⟩
  iintro %pcc %γp ⟨#Hpcc, %-, Hpo⟩
  simp only [show ¬ (W64 4096 = W64 0) by decide, ↓reduceIte]
  imod start_bag (netRecv Rh.γn lid γd) _ pcc γp (by trivial) $$ Hpcc Hpo with #Hpbag
  (try wp_auto)
  wp_apply chan.wp_make1 (V := Unit) as %sc %γs ⟨#Hscc, %-, Hsco⟩
  imod alloc_broadcast_chan (E := ⊤) iprop(True) γs sc $$ Hscc Hsco with Hsb
  icases ownBroadcastChan_open _ _ _ _ $$ Hsb with ⟨%γsch, #Hsint, Hsown⟩
  ihave #Hsunk : ownBroadcastChan sc γs iprop(True) .Unknown $$ []
  · iapply ownBroadcastChan_close _ _ _ _ γsch
    iframe #
  ihave Hsb := ownBroadcastChan_close sc γs iprop(True) .Pending γsch $$ [$Hsint $Hsown]
  (try wp_auto)
  obtain ⟨pp, hpp⟩ : ∃ pp : Loc, pp = «$r0_ptr» := ⟨_, rfl⟩
  subst hpp
  iStructNamedSuffix «$r0» "Q"
  ipersist lgQ; ipersist localIDQ; ipersist idQ; ipersist rQ; ipersist statusQ; ipersist pickerQ
  ipersist msgAppV2WriterQ; ipersist writerQ; ipersist pipelineQ; ipersist snapSenderQ
  ipersist recvcQ; ipersist propcQ; ipersist stopcQ
  -- the goroutines' context
  ihave #Hctxp : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_apply hBackground
  wp_apply hWithCancel as %ctx' %γc %cancel ⟨#Hcancel, #Hctx⟩
  (try wp_auto)
  ipersist cancelQ
  ihave #Hraft0 := Hraft
  iunfold netRaftOk at Hraft
  icases Hraft with ⟨%ri, %Hri, #HProc, -, -, -⟩
  subst Hri
  ipersist p; ipersist ctx; ipersist r; ipersist t
  wp_apply wp_fork $$ [HR7]
  · ihave #Hbag := Hrbag
    proc_loop rcc, γr
  (try wp_auto)
  wp_apply wp_fork $$ [HR8]
  · irename HR8 => HR7
    ihave #Hbag := Hpbag
    proc_loop pcc, γp
  (try wp_auto)
  -- the stream readers
  ihave #Hratep : isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.time.rate $$ []
  · iPkgInit
  have e2 : rafthttp.streamTypeMsgAppV2 = #(StreamTy.msgAppV2.str) := rfl
  have e1 : rafthttp.streamTypeMessage = #(StreamTy.message.str) := rfl
  simp only [e1, e2]
  wp_apply hNewLimiter drf (W64 1) as %rl2 #Hrl2
  (try wp_auto)
  obtain ⟨cr2, hcr2⟩ : ∃ cr2 : Loc, cr2 = «$r0_ptr» := ⟨_, rfl⟩
  subst hcr2
  irename «$r0» => Hcr2
  ipersist msgAppV2ReaderQ
  (try wp_auto)
  wp_apply hNewLimiter drf (W64 1) as %rl1 #Hrl1
  (try wp_auto)
  obtain ⟨cr1, hcr1⟩ : ∃ cr1 : Loc, cr1 = «$r0_ptr» := ⟨_, rfl⟩
  subst hcr1
  irename «$r0» => Hcr1
  ipersist msgAppReaderQ
  irename Hcr2 => Hcr
  sp_reader cr2, StreamTy.msgAppV2, rl2
  irename Hsr => Hsr2; irename Hstop => Hstop2; irename Hmu => Hmu2
  irename Hcr1 => Hcr
  sp_reader cr1, StreamTy.message, rl1
  imod sync.init_Mutex (peerLockInv pp) ⊤ (pp.[rafthttp.peer, go!"mu"]) $$ muQ [pausedQ]
    with #Hpmu
  · inext; iunfold peerLockInv; iexists _; iframe
  ihave #Hph : pipeHandleOk Rh pl pid R $$ [Hpl]
  · iunfold pipeStarted at Hpl
    icases Hpl with ⟨#Hph, -⟩
    iexact Hph
  rw [_root_.decide_eq_false Hlgnn]
  sp_log
  iapply HΦ
  isplitr
  · iunfold peerOk
    iexists lg, ps, pk, cw2, cw1, pl, sns, cr2, cr1, GoInterface.ok ri, rcc, pcc
    iframe #
    ipureintro; exact Hlgnn
  iunfold peerStop
  iexists cw2, cw1, pl, sns, sc, γs, cancel, γc
  iframe
  iframe #

end proof

end EtcdGrove
end Perennial
