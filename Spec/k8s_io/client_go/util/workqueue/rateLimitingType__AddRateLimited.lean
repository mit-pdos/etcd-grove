/-
`(*rateLimitingType[T]).AddRateLimited(item)` (`rate_limiting_queue.go`): add the item after the rate limiter's delay for it (`AddAfter`). Lean-first.
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

/-- `q.AddRateLimited(k)`: returns (the item added after the rate limiter's delay, a liveness matter not stated). -/
abbrev rateLimitingType.AddRateLimited.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (q : Loc) (γ : DNames)
    (P : time.Duration → Prop) (k : K),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗
      isRateLimitingQueue (K := K) q γ P }}
    (App (Val (q @!! go.GoType.PointerType (rateLimitingType.ty T) @!! go!"AddRateLimited")) (Val #k))
  {{ RET #(); True }}

end spec

end workqueue
end EtcdGrove
end Perennial
