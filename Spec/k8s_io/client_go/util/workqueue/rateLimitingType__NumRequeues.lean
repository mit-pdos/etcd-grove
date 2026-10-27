/-
`(*rateLimitingType[T]).NumRequeues(item)` (`rate_limiting_queue.go`): the rate limiter's count of the item's requeues. Lean-first.
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

/-- `q.NumRequeues(k)`: some `int`. -/
abbrev rateLimitingType.NumRequeues.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (q : Loc) (γ : DNames)
    (P : time.Duration → Prop) (k : K),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗
      isRateLimitingQueue (K := K) q γ P }}
    (App (Val (q @!! go.GoType.PointerType (rateLimitingType.ty T) @!! go!"NumRequeues")) (Val #k))
  {{ (n : w64), RET #n; True }}

end spec

end workqueue
end EtcdGrove
end Perennial
