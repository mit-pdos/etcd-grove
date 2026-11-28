/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/watchChan__concurrentProcessEvents.lean` (k8s 7f-5b). The
queue `processingQueue` is an SPSC of response channels (`kQElem`, never closed); the struct `p`'s `wc` and
`processingQueue` are read-only after its store; the incoming channel's consumer half goes to the
scheduler, `procd`'s half, `procEx` and the alive fraction to the collector. Two top-level slots of
`run`'s wait group: the scheduler's (`Done` proposition `True`, its level-`1` token lent to its members),
the collector's (the alive fraction). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__concurrentProcessEvents
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.concurrentOrderedEventProcessing__scheduleEventProcessing
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.concurrentOrderedEventProcessing__collectEventProcessing
public import Perennial.Spec.sync.WaitGroup__Add
public import Perennial.Spec.sync.WaitGroup__Done
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
theorem watchChan.concurrentProcessEvents.wp_proof
    (wp_schedule : concurrentOrderedEventProcessing.scheduleEventProcessing.spec (GF := GF) (hG := hG))
    (wp_collect : concurrentOrderedEventProcessing.collectEventProcessing.spec (GF := GF) (hG := hG))
    (wp_Add : sync.WaitGroup.Add.spec (GF := GF) (hG := hG))
    (wp_Done : sync.WaitGroup.Done.spec (GF := GF) (hG := hG)) :
    watchChan.concurrentProcessEvents.spec (GF := GF) (hG := hG) := by
  intro _ Obj _ _ wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp recur q wg n P HQok Hhist hn
  wp_start as ⟨#Hcons, Hproc, Had⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hcons' := Hcons
  iunfold kWcCons at Hcons'
  icases Hcons' with ⟨#Hprod, %p, %lg, -, -, -, -, #Hsw, -, -, -⟩
  ihave #Hprod' := Hprod
  iunfold kWcProd at Hprod'
  icases Hprod' with ⟨%wp, %chI, %chR, %lgI, %cf, %rse, %γc, #Hfw, #Hsw1, -, -, -, -,
    #Hfctx, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩
  ihave #Hsw' := Hsw
  iunfold storeWatchOk at Hsw'
  icases Hsw' with ⟨%wp', %nf, %crv, %rse', #Hsw2, -, -, -, #Hwgr, -, -, -, -, -, -, -, -, -,
    %ot, #Hwot⟩
  ihave %Hwp := typedPointsto_agree_wand _ _ _ _ _ $$ Hsw1 Hsw2
  subst Hwp
  iunfold kProcSt at Hproc
  icases Hproc with ⟨Hci, Hpd, Hpe, Hal⟩
  wp_auto
  wp_apply chan.wp_make2 (V := Loc) (W64 9) as %chQ %γcQ ⟨#HcQ, -, HoQ⟩
  · ipureintro; decide
  imod start_spsc chQ (kQElem c W γ cd sel emp inS m Q) (fun _ => iprop(False)) γcQ
    $$ HcQ [HoQ] with ⟨%γq, #HQs, Hqp, Hqc⟩
  · iright; iexact HoQ
  (try wp_auto)
  ipersist wc
  ipersist wg
  irename wc => Hwcv
  irename wg => Hwgv
  iStructNamed p
  ipersist wc
  ipersist processingQueue
  wp_apply (rwg.wp_Add_top wp_Add iprop(True) rwgN 3 wg n P (by omega)) $$ [$Had] as ⟨Had, Hd1⟩
  (try wp_auto)
  wp_apply wp_fork_tok
  iintro Htok
  isplitl [Hci Hqp Hd1 Htok]
  · ihave ⟨Htok, %HT⟩ := (persistent_entails_left (threadToks_lt (GF := GF) 1)) $$ Htok
    icases (threadTok_level0 (GF := GF)).1 $$ Htok with ⟨H0, Htok⟩
    icases (threadTokFrom_succ (GF := GF) 1 HT).1 $$ Htok with ⟨H1, H2⟩
    (try wp_auto)
    wp_apply wp_with_defer as %defer defer
    (try wp_auto)
    wp_apply (wp_schedule Obj p_ptr chQ γq wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp recur
      wg iprop(True) HQok) $$ [Hci Hqp Hd1 H1] as ⟨Hd1, H1⟩
    · iframe #
      iframe
    (try wp_auto)
    wp_apply (rwg.wp_Done_top wp_Done rwgN 3 wg iprop(True)) $$ [$Hd1]
    (try wp_auto)
    iapply (threadTok_level0 (GF := GF)).2
    iframe H0
    iapply (threadTokFrom_succ (GF := GF) 1 HT).2
    iframe
  (try wp_auto)
  wp_apply (rwg.wp_Add_top wp_Add (kResAlive alive q) rwgN 3 wg (n + 1) iprop(P ∗ True)
    (by omega)) $$ [$Had] as ⟨Had, Hd2⟩
  (try wp_auto)
  wp_apply wp_fork_tok
  iintro Htok
  isplitl [Hqc Hpd Hpe Hal Hd2 Htok]
  · (try wp_auto)
    wp_apply wp_with_defer as %defer defer
    (try wp_auto)
    wp_apply (wp_collect Obj p_ptr chQ γq wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp recur
      q Hhist) $$ [Hqc Hpd Hpe Hal] as Hal
    · iframe #
      iframe
    (try wp_auto)
    wp_apply (rwg.wp_Done_top wp_Done rwgN 3 wg (kResAlive alive q)) $$ [$Hd2 $Hal]
    (try wp_auto)
    iframe Htok
  (try wp_auto)
  iapply HΦ
  iapply rwg.rwgAdder_wand $$ [] Had
  iintro ⟨⟨HP, -⟩, Ha⟩
  iframe

end proof

end k8s
end EtcdGrove
end Perennial
