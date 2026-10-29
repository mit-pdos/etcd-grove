/-
The shared informer's listeners (`shared_informer.go`'s `processorListener`): what their specs are
stated with. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the processor and listeners).

A listener is a pipeline of two goroutines between the informer and one event handler:
`add` (the informer's side, under `blockDeltas`) sends each notification on the unbuffered `addCh`;
`pop` receives them, buffers them in an unbounded ring (`pendingNotifications`) and sends them on
the unbuffered `nextCh`; `run` receives them and calls the handler. Both channels are
single-producer single-consumer (Perennial's `isSpsc`), with the same per-position resource
(`notifP Q γt`): the `i`-th notification is `notifOf e` for an event `e` with the client's `Q i e`
(the listener's contract on its `i`-th event, e.g. "the informer's `i`-th event, after the store
reflects it") and, for an initial-list add, a start token of the listener's tracker (`sftTok`,
which `run` gives back to `Finished`). So the handler receives exactly the events sent, in order.

* `notifOf e`: the notification value of an event (`addNotification`, `updateNotification`,
  `deleteNotification`, as interface values: `run`'s type switch recovers the event).
* `LNames`: a listener's ghost names (the two SPSC channels, the two closed-once channels `done`
  and `runFinished`, the tracker).
* `isListener l γ Q` (persistent): the listener's read-only fields and its channels' and tracker's
  invariants.
* `lhOk h H Q`: the handler `h` takes each event `e` at position `evs.length` with `Q` from `H evs`
  to `H (evs ++ [e])`.
-/
module

public import Proof.k8s_io.client_go.tools.cache.InformerDefs
public import Proof.k8s_io.client_go.tools.cache.synctrack.Defs
public import Perennial.Golang.Theory.Chan.Idioms.Spsc
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section model
variable [GooseExts] [GoGlobalContext]

/-- **The notification of an event** (`shared_informer.go:805-818`), as `distribute` sends it. -/
def notifOf : Ev → GoInterface
  | .add o b => interface.mkOk addNotification.ty #(addNotification.mk o b)
  | .update old new => interface.mkOk updateNotification.ty #(updateNotification.mk old new)
  | .delete o => interface.mkOk deleteNotification.ty #(deleteNotification.mk o)

theorem notif_ty_ne :
    updateNotification.ty ≠ addNotification.ty ∧ deleteNotification.ty ≠ addNotification.ty ∧
    addNotification.ty ≠ updateNotification.ty ∧ deleteNotification.ty ≠ updateNotification.ty ∧
    addNotification.ty ≠ deleteNotification.ty ∧ updateNotification.ty ≠ deleteNotification.ty := by
  unfold updateNotification.ty addNotification.ty deleteNotification.ty
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro h; injection h with h; simp at h)

/-- An initial-list add (`isInInitialList`). -/
def Ev.initial : Ev → Bool
  | .add _ b => b
  | _ => false

end model

/-- A listener's ghost names. -/
structure LNames where
  add : SpscNames
  next : SpscNames
  done : ChanNames
  runFin : ChanNames
  tr : GName

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **The resource of a listener's `i`-th notification** `v`: `notifOf e` for an event `e` with
the client's `Q i e`, and a start token of the tracker `γt` if it is an initial-list add. -/
def notifP (Q : Nat → Ev → IProp GF) (γt : GName) (i : Int) (v : GoInterface) : IProp GF :=
  iprop(∃ e : Ev, ⌜v = notifOf e⌝ ∗ Q i.toNat e ∗
    (if e.initial then synctrack.sftTok γt else iprop(True)))

open Iris.ProofMode in
/-- A notification is not `nil`. -/
theorem notifP_nonnil (Q : Nat → Ev → IProp GF) (γt : GName) (i : Int) (v : GoInterface) :
    notifP Q γt i v ⊢ ⌜v ≠ interface.nil⌝ := by
  iintro H
  iunfold notifP at H
  icases H with ⟨%e, %he, -, -⟩
  ipureintro
  subst he
  cases e <;> simp [notifOf, interface.mkOk]

/-- The listener's invariant's namespace (the length counter's). -/
def lenN : Namespace := nroot.@"cache.processorListener.len"

/-- **The listener** (persistent): its read-only fields (the channels, the handler, the tracker,
the logger; the closed-once channels `done` and `runFinished` are the specs' of the goroutines
closing them),
the SPSC invariants of `addCh` and `nextCh` (each notification's resource `notifP Q`, nothing on
close), the tracker's invariant, and the length counter `pendingNotificationsLength` (an
`atomic.Int64` read only for tracing) in an invariant of its own. -/
def isListener (l : Loc) (γ : LNames) (Q : Nat → Ev → IProp GF) : IProp GF :=
  iprop(∃ (addCh nextCh t : Loc) (h : GoInterface) (lg : github_com.go_logr.logr.Logger)
      (hn : GoString),
    structFieldRef processorListener go!"addCh" l ↦□ addCh ∗
    structFieldRef processorListener go!"nextCh" l ↦□ nextCh ∗
    structFieldRef processorListener go!"logger" l ↦□ lg ∗
    structFieldRef processorListener go!"handlerName" l ↦□ hn ∗
    structFieldRef processorListener go!"handler" l ↦□ h ∗
    structFieldRef processorListener go!"syncTracker" l ↦□ t ∗
    isSpsc (V := GoInterface) γ.add addCh (notifP Q γ.tr) (fun _ => iprop(True)) ∗
    isSpsc (V := GoInterface) γ.next nextCh (notifP Q γ.tr) (fun _ => iprop(True)) ∗
    synctrack.isSFT t γ.tr ∗
    inv lenN (∃ x : w64,
      sync.atomic.ownInt64 (structFieldRef processorListener go!"pendingNotificationsLength" l)
        (DFrac.own 1) x))

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 512 in
instance isListener_persistent (l : Loc) (γ : LNames) (Q : Nat → Ev → IProp GF) :
    Persistent (isListener l γ Q) := by
  unfold isListener; infer_instance

/-- **A listener's handler contract**: `h` takes each event `e` at position `evs.length`, with its
`Q`, from `H evs` to `H (evs ++ [e])`. -/
def lhOk (h : GoInterface) (H : List Ev → IProp GF) (Q : Nat → Ev → IProp GF) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜h = interface.ok i⌝ ∗
    □ (∀ (evs : List Ev) (o : GoInterface) (b : Bool), {{ H evs ∗ Q evs.length (Ev.add o b) }}
        (App (App (Val #(methods i.ty go!"OnAdd" i.v)) (Val #o)) (Val #b))
        {{ RET #(); H (evs ++ [Ev.add o b]) }}) ∗
    □ (∀ (evs : List Ev) (old new : GoInterface), {{ H evs ∗ Q evs.length (Ev.update old new) }}
        (App (App (Val #(methods i.ty go!"OnUpdate" i.v)) (Val #old)) (Val #new))
        {{ RET #(); H (evs ++ [Ev.update old new]) }}) ∗
    □ (∀ (evs : List Ev) (o : GoInterface), {{ H evs ∗ Q evs.length (Ev.delete o) }}
        (App (Val #(methods i.ty go!"OnDelete" i.v)) (Val #o))
        {{ RET #(); H (evs ++ [Ev.delete o]) }}))

instance lhOk_persistent (h : GoInterface) (H : List Ev → IProp GF) (Q : Nat → Ev → IProp GF) :
    Persistent (lhOk h H Q) := by
  unfold lhOk; infer_instance

end defs

end cache
end EtcdGrove
end Perennial
