/-
Proof of `Spec/k8s_io/client_go/util/workqueue/newDelayingQueue.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.newDelayingQueue
public import Spec.k8s_io.client_go.util.workqueue.newRetryMetrics
public import Spec.k8s_io.client_go.util.workqueue.delayingType__waitingLoop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.workqueue

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

theorem newDelayingQueue.wp_proof
    (wp_newRetryMetrics : newRetryMetrics.spec (GF := GF) (hG := hG))
    (wp_waitingLoop : delayingType.waitingLoop.spec (GF := GF) (hG := hG)) :
    newDelayingQueue.spec (GF := GF) (hG := hG) := by
  intro K T _ logger c tq γq name provider Hpre
  wp_start as ⟨#Hc, #Htyped, Htok⟩
  ihave #Hc' := Hc
  iunfold isClock at Hc'
  icases Hc' with ⟨%ci, %Hci, -, -, #HNewTicker⟩
  subst Hci
  wp_auto
  wp_apply HNewTicker as %hb #Hhb
  · ipureintro; decide
  wp_apply chan.wp_make1 (V := Unit) as %sch %γs ⟨#Hsch, %_, Hsoc⟩
  wp_apply (chan.wp_make2 (V := Loc) (W64 1000)) as %wch %γw ⟨#Hwch, %_, Hwoc⟩
  · ipureintro; decide
  wp_apply (wp_newRetryMetrics name provider Hpre) as %rm #Hrm
  generalize «$r0_ptr» = q
  iStructNamed «$r0»
  imod alloc_broadcast_chan (E := ⊤) (shutdownLb γq) γs sch $$ Hsch Hsoc with Hbc
  icases ownBroadcastChan_open _ _ _ _ $$ Hbc with ⟨%γi, #Hint, Hpend⟩
  ihave #Hunk := ownBroadcastChan_close sch γs (shutdownLb γq) Broadcast.Unknown γi $$ [Hint]
  · iframe #
  ihave Hpend' := ownBroadcastChan_close sch γs (shutdownLb γq) Broadcast.Pending γi $$ [Hint Hpend]
  · iframe; iframe #
  imod start_bag (entryOk (K := K)) (ChanState.Buffered []) wch γw trivial $$ Hwch Hwoc with #Hbag
  imod sync.init_Once (structFieldRef (delayingType K) go!"stopOnce" q)
    (iprop(ownBroadcastChan sch γs (shutdownLb γq) .Pending ∗ shutdownToks γq 1)) (shutdownLb γq) ⊤
    $$ [stopOnce Hpend' Htok] with #Honce
  · iframe
  ipersist TypedInterface
  ipersist «clock»
  ipersist stopCh
  ipersist heartbeat
  ipersist waitingForAddCh
  ipersist metrics
  ihave #Hdq : isDelaying (K := K) q ⟨γq, γs, γw⟩ $$ []
  · unfold isDelaying
    iexists tq, _, sch, hb, wch, rm
    simp only [named]
    iframe #
  wp_apply wp_fork $$ []
  · wp_apply (wp_waitingLoop (K := K) (T := T) q ⟨γq, γs, γw⟩ logger) $$ [$Hdq]
    first | itrivial | (ipureintro; simp) | (ipureintro; decide)
  iapply HΦ
  iframe #
  ipureintro; rfl

end proof

end workqueue
end EtcdGrove
end Perennial
