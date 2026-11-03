/-
`(*sharedProcessor).addListener(listener)` (`shared_informer.go`): under the listeners' write
lock, the listener added to the map (made if `nil`); if the processor has started, its `run` and
`pop` goroutines started. Returns the listener as the registration and whether started. **A first
cut** (Stage 3): the listener joins the sender's set (`procSend`) at the events `E` sent so far,
its goroutines' resources (`lstnGoPre`) to the goroutines or to the lock (until `run` starts
them). The existing processor model (`ProcDefs.lean`) has every listener from the first event;
a late listener (after the informer's start, `E ≠ []`) needs its own offset: to be fixed with the
processor's proofs. Lean-first; the DaemonSet run's track A.
-/
module

public import Proof.k8s_io.client_go.tools.cache.SIIAt
public import Spec.k8s_io.client_go.tools.cache.processorListener__pop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI apimodel cache informer k8s_io.client_go.tools.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]
/-- **What a listener's two goroutines need** (`run`'s and `pop`'s preconditions but the package and
`isListener`): `run`'s handler and its contract, `pop`'s ring, the channels' other ends, the closed-once
channels. -/
def lstnGoPre (l : Loc) (γ : LNames) (Q : Nat → Ev → IProp GF) : IProp GF :=
  iprop(∃ (h : GoInterface) (H : List Ev → IProp GF) (runFin done : Loc),
    structFieldRef processorListener go!"handler" l ↦□ h ∗ lhOk h H Q ∗
    structFieldRef processorListener go!"runFinished" l ↦□ runFin ∗
    spscConsumer (V := GoInterface) γ.next [] ∗ H [] ∗
    ownBroadcastChan runFin γ.runFin iprop(True) .Pending ∗
    structFieldRef processorListener go!"done" l ↦□ done ∗
    spscConsumer (V := GoInterface) γ.add [] ∗ spscProducer (V := GoInterface) γ.next [] ∗
    buffer.ownRing (structFieldRef processorListener go!"pendingNotifications" l) [] ∗
    ownBroadcastChan done γ.done iprop(True) .Pending)

/-- **`p.addListener(l)`**: see the file header. -/
abbrev sharedProcessor.addListener.spec : Prop :=
  ∀ [ReceiptBoundLe GF (2 ^ 61)] (p l : Loc) (γp : ProcNames) (γl : LNames)
    (QP : Nat → Ev → IProp GF) (E : List Ev),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isProc p ∗ sync.isRWMutexGuard (structFieldRef sharedProcessor go!"listenersLock" p) (procP p γp) ∗
      procSend γp QP E ∗ isListener l γl QP ∗
      spscProducer (V := GoInterface) γl.add (E.map notifOf) ∗ lstnGoPre l γl QP }}
    (App (Val (p @!! go.GoType.PointerType sharedProcessor.ty @!! go!"addListener"))
      (Val #l))
  {{ (started : Bool), RET (PairV #(interface.mkOk (go.GoType.PointerType processorListener.ty) #l :
        ResourceEventHandlerRegistration) #started); procSend γp QP E }}

end spec

end cache
end EtcdGrove
end Perennial
