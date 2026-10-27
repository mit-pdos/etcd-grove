/-
`NewTypedRateLimitingQueueWithConfig[T](rateLimiter, config)` (`rate_limiting_queue.go`): a
rate-limiting queue over a new delaying queue (unless one is given) and the rate limiter.
Lean-first; the configurations of `rlConfigOk`.
-/
module

public import Proof.k8s_io.client_go.util.workqueue.Defs
public import Proof.k8s_io.client_go.util.workqueue.DelayingDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI k8s_io.client_go.util.workqueue

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

/-- `NewTypedRateLimitingQueueWithConfig(rl, cfg)` for a `rlConfigOk` configuration and a rate
limiter whose `When` satisfies `P`: a rate-limiting queue over a new delaying queue, with all but
one of the typed queue's shutdown tokens. -/
abbrev NewTypedRateLimitingQueueWithConfig.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (rl : TypedRateLimiter K)
    (P : time.Duration → Prop) (cfg : TypedRateLimitingQueueConfig K),
  rlConfigOk cfg →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗
      isRateLimiter (K := K) rl P }}
    (App (App (Val #(functions NewTypedRateLimitingQueueWithConfig [T])) (Val #rl)) (Val #cfg))
  {{ (q : Loc) (γ : DNames),
      RET #(interface.mkOk (go.GoType.PointerType (rateLimitingType.ty T)) #q :
        TypedRateLimitingInterface K);
      isRateLimitingQueue (K := K) q γ P ∗ shutdownToks γ.tq (shutdownPool - 1) }}

end spec

end workqueue
end EtcdGrove
end Perennial
