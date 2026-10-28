/-
`(*processorListener).add(notification)` (`shared_informer.go:1461`): an initial-list add starts
the listener's tracker; the notification is sent on `addCh`. Lean-first; phase 4 of
`notes/k8s-daemonset-plan.md` (the processor and listeners).
-/
module

public import Proof.k8s_io.client_go.tools.cache.ListenerDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`l.add(notifOf e)`**, the listener's producer (`spscProducer` of `addCh`, its `sent`
notifications so far), with the event's `Q`: the notification sent (it returns once `pop` received
it: `addCh` is unbuffered). In an execution of fewer than `2^63` Go steps (the tracker's counter,
`SingleFileTracker.Start`). -/
abbrev processorListener.add.spec : Prop :=
  ∀ (l : Loc) (γ : LNames) (Q : Nat → Ev → IProp GF) (sent : List GoInterface) (e : Ev),
  receiptBound GF ≤ 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isListener l γ Q ∗
      spscProducer γ.add sent ∗ Q sent.length e }}
    (App (Val (l @!! go.GoType.PointerType processorListener.ty @!! go!"add")) (Val #(notifOf e)))
  {{ RET #(); spscProducer γ.add (sent ++ [notifOf e]) }}

end spec

end cache
end EtcdGrove
end Perennial
