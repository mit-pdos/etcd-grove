/-
Proof of `Spec/k8s_io/client_go/util/workqueue/NewTypedDelayingQueueWithConfig.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.NewTypedDelayingQueueWithConfig
public import Spec.k8s_io.client_go.util.workqueue.NewTypedWithConfig
public import Spec.k8s_io.client_go.util.workqueue.newDelayingQueue
public import Spec.k8s_io.klog.v2.Background
public import Proof.k8s_io.client_go.util.workqueue.ClockLemmas

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

theorem NewTypedDelayingQueueWithConfig.wp_proof
    (wp_Background : klog.Background.spec (GF := GF) (hG := hG))
    (wp_NewTypedWithConfig : NewTypedWithConfig.spec (GF := GF) (hG := hG))
    (wp_newDelayingQueue : newDelayingQueue.spec (GF := GF) (hG := hG))
    (wp_Now : clock.RealClock.Now.spec (GF := GF) (hG := hG))
    (wp_NewTimer : clock.RealClock.NewTimer.spec (GF := GF) (hG := hG))
    (wp_NewTicker : clock.RealClock.NewTicker.spec (GF := GF) (hG := hG))
    (wp_timerC : clock.realTimer.C.spec (GF := GF) (hG := hG))
    (wp_timerStop : clock.realTimer.Stop.spec (GF := GF) (hG := hG))
    (wp_tickerC : clock.realTicker.C.spec (GF := GF) (hG := hG))
    (wp_tickerStop : clock.realTicker.Stop.spec (GF := GF) (hG := hG)) :
    NewTypedDelayingQueueWithConfig.spec (GF := GF) (hG := hG) := by
  intro K T _ cfg Hcfg
  obtain ⟨hl, hc, hq, hn⟩ := Hcfg
  rcases cfg with ⟨lg, nm, mp, ck, qu⟩
  simp only at hl hc hq hn
  subst hl hc hq
  wp_start
  ihave #Hrc := realClock_isClock wp_Now wp_NewTimer wp_NewTicker wp_timerC wp_timerStop
    wp_tickerC wp_tickerStop $$ Hpkg
  ihave #Hklog : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 $$ []
  · iPkgInit
  wp_auto
  iStructNamed config
  wp_apply wp_Background as %logger -
  (try wp_auto)
  wp_apply (wp_NewTypedWithConfig (K := K) (T := T)
    (TypedQueueConfig.mk nm mp (interface.mkOk k8s_io.utils.clock.RealClock.ty
      #(zero_val k8s_io.utils.clock.RealClock)) GoInterface.nil) ⟨rfl, hn⟩) as %tq %γq ⟨#Htq, Htoks⟩
  unfold shutdownToks
  rw [show shutdownPool = (shutdownPool - 1) + 1 from rfl]
  icases ownToks_add_1 1 (shutdownPool - 1) γq.pool $$ Htoks with ⟨Htoks, Htok⟩
  wp_apply (wp_newDelayingQueue (K := K) (T := T) logger _ tq γq nm mp hn) $$ [$Htq Htok]
    as %q %γ ⟨%Hγ, #Hdq⟩
  · iframe #
    unfold shutdownToks; iexact Htok
  iapply HΦ
  iframe #
  rw [Hγ, show shutdownPool - 1 + 1 - 1 = shutdownPool - 1 from rfl]
  iexact Htoks

end proof

end workqueue
end EtcdGrove
end Perennial
