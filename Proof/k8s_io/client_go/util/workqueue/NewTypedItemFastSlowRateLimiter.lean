/-
Proof of `Spec/k8s_io/client_go/util/workqueue/NewTypedItemFastSlowRateLimiter.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.NewTypedItemFastSlowRateLimiter
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

theorem NewTypedItemFastSlowRateLimiter.wp_proof
    (wp_When : TypedItemFastSlowRateLimiter.When.spec (GF := GF) (hG := hG))
    (wp_Forget : TypedItemFastSlowRateLimiter.Forget.spec (GF := GF) (hG := hG))
    (wp_NumRequeues : TypedItemFastSlowRateLimiter.NumRequeues.spec (GF := GF) (hG := hG)) :
    NewTypedItemFastSlowRateLimiter.spec (GF := GF) (hG := hG) := by
  intro K T _ fast slow n
  wp_start
  iapply wp_fupd
  wp_auto
  wp_apply wp_map_make1 (K := K) (V := w64) T go.int as %fm Hfm
  (try wp_auto)
  wp_alloc_anon
  rename_i r
  irename : (r ↦ (_ : TypedItemFastSlowRateLimiter K) : IProp GF) => Hr
  wp_auto
  iStructNamed Hr
  imod sync.init_Mutex (failuresInv (K := K) fm) ⊤ _ $$ failuresLock [Hfm] with #Hmu
  · inext; iunfold failuresInv; iexists _; iframe
  ipersist failures
  ipersist maxFastAttempts
  ipersist fastDelay
  ipersist slowDelay
  imodintro
  iapply HΦ
  iapply (fastSlow_isRateLimiter_of (K := K) (T := T) wp_When wp_Forget wp_NumRequeues)
  iunfold isFastSlowLimiter
  iexists fm, n
  iframe #

end proof

end workqueue
end EtcdGrove
end Perennial
