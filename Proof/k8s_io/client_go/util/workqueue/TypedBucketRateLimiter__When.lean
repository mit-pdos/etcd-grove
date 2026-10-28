/-
Proof of `Spec/k8s_io/client_go/util/workqueue/TypedBucketRateLimiter__When.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.TypedBucketRateLimiter__When
public import Spec.golang_org.x.time.rate.Reservation__Delay

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

theorem TypedBucketRateLimiter.When.wp_proof
    (wp_Reserve : rate.Limiter.Reserve.spec (GF := GF) (hG := hG))
    (wp_Delay : rate.Reservation.Delay.spec (GF := GF) (hG := hG)) :
    TypedBucketRateLimiter.When.spec (GF := GF) (hG := hG) := by
  intro K T _ r k
  wp_start as #Hr
  ihave #Hrate : isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.time.rate $$ []
  · iPkgInit
  iunfold isBucketLimiter at Hr
  icases Hr with ⟨%rl, #Hl, #Hrl⟩
  wp_auto
  wp_apply wp_Reserve $$ [$Hrl] as %res #Hres
  wp_apply wp_Delay $$ [$Hres] as %d %Hd
  wp_end

end proof

end workqueue
end EtcdGrove
end Perennial
