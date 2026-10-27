/-
`(*processorListener).pop()` (`shared_informer.go:1468`): the listener's forwarding goroutine,
from `addCh` to `nextCh` through the unbounded ring `pendingNotifications`. Lean-first; phase 4 of
`notes/k8s-daemonset-plan.md` (the processor and listeners).
-/
module

public import Proof.k8s_io.client_go.tools.cache.ListenerDefs
public import Proof.k8s_io.utils.buffer.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`l.pop()`**, `addCh`'s consumer and `nextCh`'s producer (both from the start) with the
empty ring and the right to close `done`: it forwards every notification received on `addCh` to
`nextCh`, in order, with its resource (the two channels' `notifP Q` at the same positions: the
invariant is `received = sent ++ pending`); it returns once `addCh` is closed, closing `done` and
`nextCh`. In an execution of fewer than `2^61` Go steps (the ring's growth: fewer than `2^61`
notifications pending). -/
abbrev processorListener.pop.spec : Prop :=
  ∀ (l : Loc) (γ : LNames) (Q : Nat → Ev → IProp GF) (done : Loc),
  receiptBound GF ≤ 2 ^ 61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isListener l γ Q ∗
      structFieldRef processorListener go!"done" l ↦□ done ∗
      spscConsumer (V := GoInterface) γ.add [] ∗ spscProducer (V := GoInterface) γ.next [] ∗
      buffer.ownRing (structFieldRef processorListener go!"pendingNotifications" l) [] ∗
      ownBroadcastChan done γ.done iprop(True) .Pending }}
    (App (Val (l @!! go.GoType.PointerType processorListener.ty @!! go!"pop")) (Val #()))
  {{ RET #(); True }}

end spec

end cache
end EtcdGrove
end Perennial
