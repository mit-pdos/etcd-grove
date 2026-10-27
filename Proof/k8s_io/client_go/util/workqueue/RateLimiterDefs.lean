/-
The work queue's rate limiters (`default_rate_limiters.go`). Lean-first; phase 2 of the DaemonSet
plan.

**A rate limiter** `isRateLimiter rl P` (persistent): the `TypedRateLimiter[T]` interface value
`rl` whose methods are safe to call concurrently and return: `When(item)` a duration satisfying
`P`, `Forget(item)`, `NumRequeues(item)` some `int`. The per-item failure counts the limiters keep
are internal (nothing the DaemonSet controller's safety needs reads them): the specs state memory
safety and the bound on `When`'s result, which is what `AddRateLimited` passes to `AddAfter`.

- `TypedItemExponentialFailureRateLimiter` (`isExpLimiter r max`): `When` returns at most
  `maxDelay` (not at least `0`: `issues/k8s-workqueue-exponential-backoff-2to63.md`); the counts
  are a map under the limiter's mutex.
- `TypedItemFastSlowRateLimiter` (`isFastSlowLimiter r fast slow`): `When` returns `fast` or `slow`.
- `TypedBucketRateLimiter` (`isBucketLimiter r`): `When` returns a non-negative delay
  (`rate.Reservation.Delay`'s trust-boundary spec).
- `TypedMaxOfRateLimiter` (`isMaxOfLimiter r`): `When` returns the maximum of `0` and its limiters'
  `When`s, so a non-negative delay whatever they return.
- `TypedWithMaxWaitRateLimiter`: `When` returns at most its `maxDelay`.

`DefaultTypedControllerRateLimiter` is the max of an exponential limiter (5 ms to 1000 s) and a
bucket (10 qps, burst 100): `isRateLimiter rl (0 ≤ ·)`.
-/
module

public import Proof.k8s_io.client_go.util.workqueue.Defs
public import Spec.golang_org.x.time.rate.Limiter__Reserve

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI k8s_io.client_go.util.workqueue

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable {K : Type} {T : go.GoType} [QItem (GF := GF) K T]

/-- **A rate limiter** (persistent): the interface value `rl`, whose `When` returns a duration
satisfying `P` (see the file header). -/
def isRateLimiter (rl : TypedRateLimiter K) (P : time.Duration → Prop) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜rl = interface.ok i⌝ ∗
    (∀ k : K, {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue }}
      (App (Val #(methods i.ty go!"When" i.v)) (Val #k))
      {{ (d : time.Duration), RET #d; ⌜P d⌝ }}) ∗
    (∀ k : K, {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue }}
      (App (Val #(methods i.ty go!"Forget" i.v)) (Val #k))
      {{ RET #(); True }}) ∗
    (∀ k : K, {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue }}
      (App (Val #(methods i.ty go!"NumRequeues" i.v)) (Val #k))
      {{ (n : w64), RET #n; True }}))

instance isRateLimiter_persistent (rl : TypedRateLimiter K) (P : time.Duration → Prop) :
    Persistent (isRateLimiter (GF := GF) (K := K) rl P) := by
  unfold isRateLimiter; infer_instance

/-- A weaker bound. -/
theorem isRateLimiter_mono (rl : TypedRateLimiter K) (P Q : time.Duration → Prop)
    (h : ∀ d, P d → Q d) :
    isRateLimiter (GF := GF) (K := K) rl P ⊢ isRateLimiter rl Q := by
  unfold isRateLimiter
  iintro ⟨%i, %Hi, #HW, #HF, #HN⟩
  iexists i
  isplitr
  · ipureintro; exact Hi
  isplitr
  · iintro %k
    iintro !> %Φ Hpkg HΦ
    iapply HW $$ %k Hpkg
    inext
    iintro %d %Hd
    iapply HΦ
    ipureintro; exact h d Hd
  iframe #

/-- The failure counts of a limiter with a mutex (`failuresLock`) over a map (`failures`). -/
def failuresInv (fm : Loc) : IProp GF :=
  iprop(∃ m : GMap K w64, fm ↦$ m)

/-- **An exponential failure limiter** (persistent) with maximal delay `max`. -/
def isExpLimiter (r : Loc) (max : time.Duration) : IProp GF :=
  iprop(∃ (fm : Loc) (base : time.Duration),
    structFieldRef (TypedItemExponentialFailureRateLimiter K) go!"failures" r ↦□ (fm : GoMap) ∗
    structFieldRef (TypedItemExponentialFailureRateLimiter K) go!"baseDelay" r ↦□ base ∗
    structFieldRef (TypedItemExponentialFailureRateLimiter K) go!"maxDelay" r ↦□ max ∗
    sync.isMutex (structFieldRef (TypedItemExponentialFailureRateLimiter K) go!"failuresLock" r)
      (failuresInv (K := K) fm))

instance isExpLimiter_persistent (r : Loc) (max : time.Duration) :
    Persistent (isExpLimiter (GF := GF) (K := K) r max) := by
  unfold isExpLimiter; infer_instance

/-- **A fast-slow failure limiter** (persistent) with delays `fast` and `slow`. -/
def isFastSlowLimiter (r : Loc) (fast slow : time.Duration) : IProp GF :=
  iprop(∃ (fm : Loc) (n : w64),
    structFieldRef (TypedItemFastSlowRateLimiter K) go!"failures" r ↦□ (fm : GoMap) ∗
    structFieldRef (TypedItemFastSlowRateLimiter K) go!"maxFastAttempts" r ↦□ n ∗
    structFieldRef (TypedItemFastSlowRateLimiter K) go!"fastDelay" r ↦□ fast ∗
    structFieldRef (TypedItemFastSlowRateLimiter K) go!"slowDelay" r ↦□ slow ∗
    sync.isMutex (structFieldRef (TypedItemFastSlowRateLimiter K) go!"failuresLock" r)
      (failuresInv (K := K) fm))

instance isFastSlowLimiter_persistent (r : Loc) (fast slow : time.Duration) :
    Persistent (isFastSlowLimiter (GF := GF) (K := K) r fast slow) := by
  unfold isFastSlowLimiter; infer_instance

/-- **A token bucket limiter** (persistent): its `*rate.Limiter`. -/
def isBucketLimiter (r : Loc) : IProp GF :=
  iprop(∃ rl : Loc,
    structFieldRef (TypedBucketRateLimiter K) go!"Limiter" r ↦□ rl ∗ rate.limiterOk rl)

instance isBucketLimiter_persistent (r : Loc) :
    Persistent (isBucketLimiter (GF := GF) (K := K) r) := by
  unfold isBucketLimiter; infer_instance

/-- **A max-of limiter** (persistent): its limiters (each with some bound). -/
def isMaxOfLimiter (r : Loc) : IProp GF :=
  iprop(∃ (sl : GoSlice) (ls : List (TypedRateLimiter K)),
    structFieldRef (TypedMaxOfRateLimiter K) go!"limiters" r ↦□ sl ∗ sl ↦*□ ls ∗
    [∗list] l ∈ ls, ∃ P : time.Duration → Prop, isRateLimiter (K := K) l P)

instance isMaxOfLimiter_persistent (r : Loc) :
    Persistent (isMaxOfLimiter (GF := GF) (K := K) r) := by
  unfold isMaxOfLimiter; infer_instance

end defs

end workqueue
end EtcdGrove
end Perennial
