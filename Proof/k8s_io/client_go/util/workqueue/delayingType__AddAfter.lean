/-
Proof of `Spec/k8s_io/client_go/util/workqueue/delayingType__AddAfter.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.delayingType__AddAfter
public import Spec.k8s_io.client_go.util.workqueue.delayingType__ShuttingDown
public import Spec.k8s_io.client_go.util.workqueue.delayingType__Add

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.workqueue

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

theorem delayingType.AddAfter.wp_proof
    (wp_ShuttingDown : delayingType.ShuttingDown.spec (GF := GF) (hG := hG))
    (wp_Add : delayingType.Add.spec (GF := GF) (hG := hG)) :
    delayingType.AddAfter.spec (GF := GF) (hG := hG) := by
  intro K T _ q γ k d
  wp_start as #Hq
  ihave #Hq' := Hq
  iNamed Hq'
  wp_auto
  wp_apply wp_ShuttingDown $$ [$Hq] as %b -
  cases b
  · (try wp_auto)
    iunfold isRetryMetrics at Hrm
    icases Hrm with ⟨%ri, %Hri, #Hretry⟩
    subst Hri
    (try wp_auto)
    wp_apply Hretry
    wp_if_destruct
    · wp_apply wp_Add $$ [$Hq]
      wp_end
    · iunfold isClock at Hc
      icases Hc with ⟨%ci, %Hci, #HNow, -, -⟩
      subst Hci
      wp_auto
      wp_apply HNow as %now -
      wp_apply (lc := 2) time.Time.wp_Add as %t -
      wp_apply_core chan.wp_select_blocking
      iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γ.stop
        isplit
        · ipureintro; rfl
        isplit
        · iapply ownBroadcastChan_is_chan $$ Hstop
        iapply broadcast_chan_receive $$ Hstop
        iintro -
        wp_auto
        wp_end
      iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.blockingClausePre]
        iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, wch, γ.wch, «$v1_ptr»
        isplit
        · ipureintro; exact ⟨rfl, rfl⟩
        isplit
        · iapply is_bag_is_chan $$ Hbag
        iapply bag_send_au γ.wch wch (entryOk (K := K)) «$v1_ptr» _ $$ [$Hlc1 $Hlc2] Hbag [«$v1»]
        · iunfold entryOk; iexists _; iexact «$v1»
        inext
        wp_auto
        wp_end
      iapply BigAndL.bigAndL_nil.2
      itrivial
  · (try wp_auto)
    wp_end

end proof

end workqueue
end EtcdGrove
end Perennial
