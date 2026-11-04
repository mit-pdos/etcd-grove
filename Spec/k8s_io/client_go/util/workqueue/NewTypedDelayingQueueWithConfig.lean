/-
`NewTypedDelayingQueueWithConfig[T](config)` (`delaying_queue.go`): a delaying queue, over a new
typed queue unless one is given. Lean-first; the configurations of `delayConfigOk`.
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

/-- `NewTypedDelayingQueueWithConfig(cfg)` for a `delayConfigOk` configuration: a delaying queue
over a new typed queue, with all but one (kept by `stopOnce`) of its shutdown tokens.
The caller chooses the queue's item predicate `Pk` (`isTyped`), which every item added must satisfy;
the statement without it is the instance `Pk := fun _ => True`. -/
abbrev NewTypedDelayingQueueWithConfig.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (Pk : K → Prop) (cfg : TypedDelayingQueueConfig K),
  delayConfigOk cfg →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue }}
    (App (Val #(functions NewTypedDelayingQueueWithConfig [T])) (Val #cfg))
  {{ (q : Loc) (γ : DNames),
      RET #(interface.mkOk (go.GoType.PointerType (delayingType.ty T)) #q : TypedDelayingInterface K);
      isDelaying (K := K) q γ Pk ∗ shutdownToks γ.tq (shutdownPool - 1) }}

end spec

end workqueue
end EtcdGrove
end Perennial
