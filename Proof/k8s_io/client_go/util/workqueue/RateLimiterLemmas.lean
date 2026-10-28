/-
The work queue's concrete rate limiters as `TypedRateLimiter[T]` interface values
(`isRateLimiter`), from their methods' specs (hypotheses, `_of`). Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.TypedItemExponentialFailureRateLimiter__When
public import Spec.k8s_io.client_go.util.workqueue.TypedItemExponentialFailureRateLimiter__Forget
public import Spec.k8s_io.client_go.util.workqueue.TypedItemExponentialFailureRateLimiter__NumRequeues
public import Spec.k8s_io.client_go.util.workqueue.TypedItemFastSlowRateLimiter__When
public import Spec.k8s_io.client_go.util.workqueue.TypedItemFastSlowRateLimiter__Forget
public import Spec.k8s_io.client_go.util.workqueue.TypedItemFastSlowRateLimiter__NumRequeues
public import Spec.k8s_io.client_go.util.workqueue.TypedBucketRateLimiter__When
public import Spec.k8s_io.client_go.util.workqueue.TypedBucketRateLimiter__Forget
public import Spec.k8s_io.client_go.util.workqueue.TypedBucketRateLimiter__NumRequeues
public import Spec.k8s_io.client_go.util.workqueue.TypedMaxOfRateLimiter__When
public import Spec.k8s_io.client_go.util.workqueue.TypedMaxOfRateLimiter__Forget
public import Spec.k8s_io.client_go.util.workqueue.TypedMaxOfRateLimiter__NumRequeues

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.workqueue

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]
variable {K : Type} {T : go.GoType} [QItem (GF := GF) K T]

theorem exp_isRateLimiter_of
    (wp_When : TypedItemExponentialFailureRateLimiter.When.spec (GF := GF) (hG := hG))
    (wp_Forget : TypedItemExponentialFailureRateLimiter.Forget.spec (GF := GF) (hG := hG))
    (wp_NumRequeues : TypedItemExponentialFailureRateLimiter.NumRequeues.spec (GF := GF) (hG := hG))
    (r : Loc) (max : time.Duration) :
    isExpLimiter (GF := GF) (K := K) r max ⊢
      isRateLimiter (K := K)
        (interface.mkOk (go.GoType.PointerType (TypedItemExponentialFailureRateLimiter.ty T)) #r)
        (fun d => sint.Z d ≤ sint.Z max) := by
  iintro #Hr
  unfold isRateLimiter
  iexists _
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro %k; iintro !> %Φ Hpkg HΦ
    iapply (wp_When (K := K) (T := T) r max k) $$ [$Hpkg $Hr] HΦ
  isplitr
  · iintro %k; iintro !> %Φ Hpkg HΦ
    iapply (wp_Forget (K := K) (T := T) r max k) $$ [$Hpkg $Hr] HΦ
  · iintro %k; iintro !> %Φ Hpkg HΦ
    iapply (wp_NumRequeues (K := K) (T := T) r max k) $$ [$Hpkg $Hr] HΦ

theorem fastSlow_isRateLimiter_of
    (wp_When : TypedItemFastSlowRateLimiter.When.spec (GF := GF) (hG := hG))
    (wp_Forget : TypedItemFastSlowRateLimiter.Forget.spec (GF := GF) (hG := hG))
    (wp_NumRequeues : TypedItemFastSlowRateLimiter.NumRequeues.spec (GF := GF) (hG := hG))
    (r : Loc) (fast slow : time.Duration) :
    isFastSlowLimiter (GF := GF) (K := K) r fast slow ⊢
      isRateLimiter (K := K)
        (interface.mkOk (go.GoType.PointerType (TypedItemFastSlowRateLimiter.ty T)) #r)
        (fun d => d = fast ∨ d = slow) := by
  iintro #Hr
  unfold isRateLimiter
  iexists _
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro %k; iintro !> %Φ Hpkg HΦ
    iapply (wp_When (K := K) (T := T) r fast slow k) $$ [$Hpkg $Hr] HΦ
  isplitr
  · iintro %k; iintro !> %Φ Hpkg HΦ
    iapply (wp_Forget (K := K) (T := T) r fast slow k) $$ [$Hpkg $Hr] HΦ
  · iintro %k; iintro !> %Φ Hpkg HΦ
    iapply (wp_NumRequeues (K := K) (T := T) r fast slow k) $$ [$Hpkg $Hr] HΦ

theorem bucket_isRateLimiter_of
    (wp_When : TypedBucketRateLimiter.When.spec (GF := GF) (hG := hG))
    (wp_Forget : TypedBucketRateLimiter.Forget.spec (GF := GF) (hG := hG))
    (wp_NumRequeues : TypedBucketRateLimiter.NumRequeues.spec (GF := GF) (hG := hG))
    (r : Loc) :
    isBucketLimiter (GF := GF) (K := K) r ⊢
      isRateLimiter (K := K)
        (interface.mkOk (go.GoType.PointerType (TypedBucketRateLimiter.ty T)) #r)
        (fun d => 0 ≤ sint.Z d) := by
  iintro #Hr
  unfold isRateLimiter
  iexists _
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro %k; iintro !> %Φ Hpkg HΦ
    iapply (wp_When (K := K) (T := T) r k) $$ [$Hpkg $Hr] HΦ
  isplitr
  · iintro %k; iintro !> %Φ Hpkg HΦ
    iapply (wp_Forget (K := K) (T := T) r k) $$ [$Hpkg $Hr] HΦ
  · iintro %k; iintro !> %Φ Hpkg HΦ
    iapply (wp_NumRequeues (K := K) (T := T) r k) $$ [$Hpkg $Hr]
    inext; iintro _; iapply HΦ; itrivial

theorem maxOf_isRateLimiter_of
    (wp_When : TypedMaxOfRateLimiter.When.spec (GF := GF) (hG := hG))
    (wp_Forget : TypedMaxOfRateLimiter.Forget.spec (GF := GF) (hG := hG))
    (wp_NumRequeues : TypedMaxOfRateLimiter.NumRequeues.spec (GF := GF) (hG := hG))
    (r : Loc) :
    isMaxOfLimiter (GF := GF) (K := K) r ⊢
      isRateLimiter (K := K)
        (interface.mkOk (go.GoType.PointerType (TypedMaxOfRateLimiter.ty T)) #r)
        (fun d => 0 ≤ sint.Z d) := by
  iintro #Hr
  unfold isRateLimiter
  iexists _
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro %k; iintro !> %Φ Hpkg HΦ
    iapply (wp_When (K := K) (T := T) r k) $$ [$Hpkg $Hr] HΦ
  isplitr
  · iintro %k; iintro !> %Φ Hpkg HΦ
    iapply (wp_Forget (K := K) (T := T) r k) $$ [$Hpkg $Hr] HΦ
  · iintro %k; iintro !> %Φ Hpkg HΦ
    iapply (wp_NumRequeues (K := K) (T := T) r k) $$ [$Hpkg $Hr] HΦ

end lemmas

end workqueue
end EtcdGrove
end Perennial
