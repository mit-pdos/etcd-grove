/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/watchChan__run.lean` (k8s 7f-5b). `alive` is split in
halves, one for the producer (startWatching), one for the processing side (processEvents); both come
back through `resultChanWG` (`rwg`: the producer's slot added here, the processing side's by
processEvents), and the whole of it closes `resultChan` (`kRes_close_au`). `watchClosedCh` is a
broadcast of `kProdExited`, so either arm of the select gives `kCancelPD` for `wc.cancel()`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__run
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__startWatching
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__processEvents
public import Perennial.Spec.sync.WaitGroup__Add
public import Perennial.Spec.sync.WaitGroup__Done
public import Perennial.Spec.sync.WaitGroup__Wait
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

set_option maxHeartbeats 1600000 in
theorem watchChan.run.wp_proof
    (wp_startWatching : watchChan.startWatching.spec (GF := GF) (hG := hG))
    (wp_processEvents : watchChan.processEvents.spec (GF := GF) (hG := hG))
    (wp_Add : sync.WaitGroup.Add.spec (GF := GF) (hG := hG))
    (wp_Done : sync.WaitGroup.Done.spec (GF := GF) (hG := hG))
    (wp_Wait : sync.WaitGroup.Wait.spec (GF := GF) (hG := hG)) :
    watchChan.run.spec (GF := GF) (hG := hG) := by
  intro _ Obj _ _ wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp recur r0 HQok Hhist Hnr Hbm
    Hlen
  wp_start as ⟨#Hrs, #Hst, #Hcons, Hir, Hsp, Hra, #Hre, Hps, Hpe, Hproc, %Htb, Htok⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply chan.wp_make1 (V := Unit) as %sc %γs ⟨#Hsch, %_, Hsoc⟩
  (try wp_auto)
  imod alloc_broadcast_chan (E := ⊤) (kProdExited (GF := GF) γ) γs sc $$ Hsch Hsoc with Hpend
  ihave #Hunk := ownBroadcastChan_Unknown _ _ _ _ $$ Hpend
  -- the wait group
  imod sync.init_WaitGroup (rwgN.@"wg") _ $$ resultChanWG with ⟨%γwg, #Hwg, Hwctr, Hwwait⟩
  imod rwg.init rwgN 3 resultChanWG_ptr γwg ⊤ (by omega) $$ [Hwctr Hwwait] with Had
  · iframe #; iframe
  wp_apply (rwg.wp_Add_top wp_Add (kResAlive alive (1 : Qp).half) rwgN 3 resultChanWG_ptr 0
    iprop(True) (by omega)) $$ [$Had] as ⟨Had, Hdone⟩
  (try wp_auto)
  -- `alive` in halves
  iunfold kProcSt at Hproc
  icases Hproc with ⟨Hci, Hpd, Hpx, Hal⟩
  iunfold kResAlive at Hal
  icases dghostVar_split alive false (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half) $$ [Hal]
    with ⟨Hal1, Hal2⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hal
  have HQ4 : ∀ lb σ, Q lb σ ⊢ ⌜lb ≤ σ.rev ∧ kvWf c σ ∧ kvWfHist c σ ∧ kvKeysShort σ⌝ := by
    intro lb σ
    refine (HQok lb σ).trans (BI.pure_mono ?_)
    intro h; exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  have HQ3 : ∀ lb σ, Q lb σ ⊢ ⌜kvWfHist c σ ∧ kvWritesDec c σ ∧ kvRevFits σ.rev⌝ := by
    intro lb σ
    refine (HQok lb σ).trans (BI.pure_mono ?_)
    intro h; exact ⟨h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  ihave #Hcons' := Hcons
  iunfold kWcCons at Hcons'
  icases Hcons' with ⟨#Hprod, %p, %lg, -, -, -, -, #Hsw, -, -, -⟩
  ipersist wc
  ipersist watchClosedCh
  ipersist forceInitialEvents
  ipersist initialEventsEndBookmarkRequired
  wp_apply wp_fork_tok
  iintro Htok2
  isplitl [Hdone Hal1 Htok2 Hpend Hir Hsp Hra Hps Hpe]
  · (try wp_auto)
    wp_apply wp_with_defer as %defer defer
    (try wp_auto)
    wp_apply (wp_startWatching Obj wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp recur r0
      (1 : Qp).half sc γs HQ4 Hhist Hnr Hbm Hlen) $$ [Hal1 Htok2 Hpend Hir Hsp Hra Hps Hpe]
      as ⟨Hal1, Htok2⟩
    · iframe #
      unfold kResAlive
      iframe
    (try wp_auto)
    wp_apply (rwg.wp_Done_top wp_Done rwgN 3 resultChanWG_ptr (kResAlive alive (1 : Qp).half))
      $$ [$Hdone $Hal1]
    (try wp_auto)
    iframe Htok2
  (try wp_auto)
  iunfold kWcProd at Hprod
  icases Hprod with ⟨%wp, %chI, %chR, %lgI, %cf, %rse, %γc, -, -, -, -, -, -, #Hfctx, #Hfcf, #Hcs, -, -,
    -, -, -, -, #HfR, #Hrc, #Hctx, -, -, -⟩
  iunfold context.cancelSpec at Hcs
  ihave #Hrc' := Hrc
  iunfold kResChan at Hrc'
  icases Hrc' with ⟨#HchR, -⟩
  wp_apply (wp_processEvents Obj wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp recur
    (1 : Qp).half resultChanWG_ptr 1 iprop(True ∗ kResAlive alive (1 : Qp).half) HQ3 Hhist (by omega))
    $$ [Hci Hpd Hpx Hal2 Had] as ⟨%n', Had⟩
  · iframe #
    unfold kProcSt kResAlive
    iframe
  (try wp_auto)
  wp_apply context.isContext_Done ctx (kCdw γ cd) $$ Hctx as %dch %γd #Hcdone
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sc, γs
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact Hsch
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hunk
    iintro ⟨#Hpx, -⟩
    ihave #Hcpd : □ kCancelPD (GF := GF) γ cd $$ []
    · imodintro; unfold kCancelPD; iright; ileft; iexact Hpx
    (try wp_auto)
    wp_bind (App (Val #cf) (Val #()))
    iapply Hcs
    · iexact Hcpd
    inext
    iintro -
    (try wp_auto)
    wp_apply (rwg.wp_Wait wp_Wait rwgN 3 resultChanWG_ptr n' _) $$ [$Had] as ⟨HP, -⟩
    (try wp_auto)
    wp_bind (App (Val #(functions go.close
      [go.GoType.ChannelType go.ChanDir.sendrecv k8s_io.apimachinery.pkg.watch.Event.ty])) (Val #chR))
    iapply chan.wp_close (V := k8s_io.apimachinery.pkg.watch.Event) chR γ.res.chanName $$ HchR
    iintro ⟨Hlc1, -, -, -⟩
    icases HP with ⟨⟨-, Ha1⟩, Ha2⟩
    ihave Ha : kResAlive (GF := GF) alive 1 $$ [Ha1 Ha2]
    · unfold kResAlive
      rw [← Qp.half_add_half (1 : Qp)]
      icombine Ha1 Ha2 as H
      iexact H
    iapply kRes_close_au c W γ cd sel emp inS m Q procd alive chR _ $$ Hrc Hlc1 Ha
    inext
    (try wp_auto)
    iapply HΦ $$ Htok
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, γd
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply context.isContextDone_is_chan $$ Hcdone
    iapply context.isContextDone_receive _ _ _ _ $$ Hcdone
    iintro ⟨#Hpd', -⟩
    ihave #Hcpd : □ kCancelPD (GF := GF) γ cd $$ []
    · imodintro
      simp only [kCdw]
      icases Hpd' with (#H | #H)
      · unfold kCancelPD; iright; iright; iright; iexact H
      · iexact H
    (try wp_auto)
    wp_bind (App (Val #cf) (Val #()))
    iapply Hcs
    · iexact Hcpd
    inext
    iintro -
    (try wp_auto)
    wp_apply (rwg.wp_Wait wp_Wait rwgN 3 resultChanWG_ptr n' _) $$ [$Had] as ⟨HP, -⟩
    (try wp_auto)
    wp_bind (App (Val #(functions go.close
      [go.GoType.ChannelType go.ChanDir.sendrecv k8s_io.apimachinery.pkg.watch.Event.ty])) (Val #chR))
    iapply chan.wp_close (V := k8s_io.apimachinery.pkg.watch.Event) chR γ.res.chanName $$ HchR
    iintro ⟨Hlc1, -, -, -⟩
    icases HP with ⟨⟨-, Ha1⟩, Ha2⟩
    ihave Ha : kResAlive (GF := GF) alive 1 $$ [Ha1 Ha2]
    · unfold kResAlive
      rw [← Qp.half_add_half (1 : Qp)]
      icombine Ha1 Ha2 as H
      iexact H
    iapply kRes_close_au c W γ cd sel emp inS m Q procd alive chR _ $$ Hrc Hlc1 Ha
    inext
    (try wp_auto)
    iapply HΦ $$ Htok
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end k8s
end EtcdGrove
end Perennial
