/-
Proof of `Spec/k8s_io/client_go/util/workqueue/DefaultTypedControllerRateLimiter.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.DefaultTypedControllerRateLimiter
public import Spec.k8s_io.client_go.util.workqueue.NewTypedItemExponentialFailureRateLimiter
public import Spec.k8s_io.client_go.util.workqueue.NewTypedMaxOfRateLimiter
public import Spec.golang_org.x.time.rate.NewLimiter
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

theorem DefaultTypedControllerRateLimiter.wp_proof
    (wp_NewExp : NewTypedItemExponentialFailureRateLimiter.spec (GF := GF) (hG := hG))
    (wp_NewLimiter : rate.NewLimiter.spec (GF := GF) (hG := hG))
    (wp_NewMaxOf : NewTypedMaxOfRateLimiter.spec (GF := GF) (hG := hG))
    (wp_When : TypedBucketRateLimiter.When.spec (GF := GF) (hG := hG))
    (wp_Forget : TypedBucketRateLimiter.Forget.spec (GF := GF) (hG := hG))
    (wp_NumRequeues : TypedBucketRateLimiter.NumRequeues.spec (GF := GF) (hG := hG)) :
    DefaultTypedControllerRateLimiter.spec (GF := GF) (hG := hG) := by
  intro K T _
  wp_start
  ihave #Hrate : isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.time.rate $$ []
  · iPkgInit
  iapply wp_fupd
  (try wp_auto)
  wp_apply wp_NewExp (K := K) (T := T) as %e #He
  wp_apply wp_NewLimiter as %lim #Hlim
  wp_alloc_anon
  rename_i b
  irename : (b ↦ (_ : TypedBucketRateLimiter K) : IProp GF) => Hb
  iStructNamed Hb
  ipersist Limiter
  ihave #Hbr := (bucket_isRateLimiter_of (K := K) (T := T) wp_When wp_Forget wp_NumRequeues b) $$ []
  · iunfold isBucketLimiter; iexists lim; iframe #
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %l1 ⟨Hl1, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  wp_apply wp_NewMaxOf (K := K) (T := T) $$ [$Hl1] as %rl #Hrl
  · rw [show sint.nat (W64 (0 + 1)) = 1 from rfl]
    simp only [List.set_cons_succ, List.set_cons_zero]
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iexists _; iexact He
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iexists _; iexact Hbr
    iapply BigSepL.bigSepL_nil.2; itrivial
  imodintro
  iapply HΦ $$ Hrl

end proof

end workqueue
end EtcdGrove
end Perennial
