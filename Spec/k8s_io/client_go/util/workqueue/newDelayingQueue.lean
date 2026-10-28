/-
`newDelayingQueue[T](logger, clock, q, name, provider)` (`delaying_queue.go`): the delaying queue
over the typed queue `q`, with its heartbeat ticker, stop and entry channels and retry metrics, its
waiting loop started. Lean-first; the typed queue a `*Typed[T]`, no retry metrics.
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

/-- `newDelayingQueue(logger, c, q, name, provider)` over a typed queue `q` (a `*Typed[T]`), with one
of its shutdown tokens (kept by `stopOnce`, for `ShutDown`), a clock, and no retry metrics (unnamed,
or the no-op providers): the delaying queue over `q`'s ghost names. -/
abbrev newDelayingQueue.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (logger : github_com.go_logr.logr.Logger)
    (c : GoInterface) (tq : Loc) (γq : QNames) (name : GoString) (provider : MetricsProvider),
  name = [] ∨ provider = interface.nil ∨ provider = noopProvider →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ isClock c ∗
      isTyped (K := K) tq γq ∗ shutdownToks γq 1 }}
    (App (App (App (App (App (Val #(functions newDelayingQueue [T])) (Val #logger)) (Val #c))
      (Val #(interface.mkOk (go.GoType.PointerType (Typed.ty T)) #tq : TypedInterface K)))
      (Val #name)) (Val #provider))
  {{ (q : Loc) (γ : DNames), RET #q; ⌜γ.tq = γq⌝ ∗ isDelaying (K := K) q γ }}

end spec

end workqueue
end EtcdGrove
end Perennial
