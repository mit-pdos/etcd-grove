/-
Proof of `Spec/k8s_io/client_go/util/workqueue/NewTypedItemExponentialFailureRateLimiter.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.NewTypedItemExponentialFailureRateLimiter
public import Proof.k8s_io.client_go.util.workqueue.RateLimiterLemmas

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

theorem NewTypedItemExponentialFailureRateLimiter.wp_proof
    (wp_When : TypedItemExponentialFailureRateLimiter.When.spec (GF := GF) (hG := hG))
    (wp_Forget : TypedItemExponentialFailureRateLimiter.Forget.spec (GF := GF) (hG := hG))
    (wp_NumRequeues : TypedItemExponentialFailureRateLimiter.NumRequeues.spec (GF := GF) (hG := hG)) :
    NewTypedItemExponentialFailureRateLimiter.spec (GF := GF) (hG := hG) := by
  intro K T _ base max
  wp_start
  iapply wp_fupd
  wp_auto
  wp_apply wp_map_make1 (K := K) (V := w64) T go.int as %fm Hfm
  (try wp_auto)
  wp_alloc_anon
  rename_i r
  irename : (r ↦ (_ : TypedItemExponentialFailureRateLimiter K) : IProp GF) => Hr
  wp_auto
  iStructNamed Hr
  imod sync.init_Mutex (failuresInv (K := K) fm) ⊤ _ $$ failuresLock [Hfm] with #Hmu
  · inext; iunfold failuresInv; iexists _; iframe
  ipersist failures
  ipersist baseDelay
  ipersist maxDelay
  imodintro
  iapply HΦ
  iapply (exp_isRateLimiter_of (K := K) (T := T) wp_When wp_Forget wp_NumRequeues)
  iunfold isExpLimiter
  iexists fm, base
  iframe #

end proof

end workqueue
end EtcdGrove
end Perennial
