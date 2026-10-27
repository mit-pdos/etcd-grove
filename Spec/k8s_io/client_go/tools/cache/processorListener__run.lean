/-
`(*processorListener).run()` (`shared_informer.go:1502`): the listener's delivering goroutine, from
`nextCh` to the handler. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the processor and
listeners).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`l.run()`**, `nextCh`'s consumer (from the start), with the handler `h`'s contract
(`lhOk h H Q`) from `H []` and the right to close `runFinished`: it calls the handler on every
notification received, in order (the `i`-th's event, with its `Q i`, at `H` of the first `i`
events), finishing the tracker after an initial-list add (with the start token the notification
carries: `Finished`'s panic unreachable); it returns once `nextCh` is closed, closing
`runFinished`. -/
abbrev processorListener.run.spec : Prop :=
  ∀ (l : Loc) (γ : LNames) (Q : Nat → Ev → IProp GF) (h : GoInterface) (H : List Ev → IProp GF)
    (runFin : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isListener l γ Q ∗
      structFieldRef processorListener go!"handler" l ↦□ h ∗ lhOk h H Q ∗
      structFieldRef processorListener go!"runFinished" l ↦□ runFin ∗
      spscConsumer (V := GoInterface) γ.next [] ∗ H [] ∗
      ownBroadcastChan runFin γ.runFin iprop(True) .Pending }}
    (App (Val (l @!! go.GoType.PointerType processorListener.ty @!! go!"run")) (Val #()))
  {{ RET #(); True }}

end spec

end cache
end EtcdGrove
end Perennial
