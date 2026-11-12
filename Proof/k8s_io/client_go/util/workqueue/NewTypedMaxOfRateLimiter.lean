/-
Proof of `Spec/k8s_io/client_go/util/workqueue/NewTypedMaxOfRateLimiter.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.NewTypedMaxOfRateLimiter
public import Proof.k8s_io.client_go.util.workqueue.RateLimiterLemmas

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

theorem NewTypedMaxOfRateLimiter.wp_proof
    (wp_When : TypedMaxOfRateLimiter.When.spec (GF := GF) (hG := hG))
    (wp_Forget : TypedMaxOfRateLimiter.Forget.spec (GF := GF) (hG := hG))
    (wp_NumRequeues : TypedMaxOfRateLimiter.NumRequeues.spec (GF := GF) (hG := hG)) :
    NewTypedMaxOfRateLimiter.spec (GF := GF) (hG := hG) := by
  intro K T _ sl ls
  wp_start as ⟨Hsl, #Hall⟩
  iapply wp_fupd
  (try wp_auto)
  wp_alloc_anon
  rename_i r
  irename : (r ↦ (_ : TypedMaxOfRateLimiter K) : IProp GF) => Hr
  wp_auto
  iStructNamed Hr
  ipersist limiters
  ipersist Hsl
  imodintro
  iapply HΦ
  iapply (maxOf_isRateLimiter_of (K := K) (T := T) wp_When wp_Forget wp_NumRequeues)
  iunfold isMaxOfLimiter
  iexists sl, ls
  iframe #

end proof

end workqueue
end EtcdGrove
end Perennial
