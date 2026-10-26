/-
The representation predicates of client-go's work queue (`k8s.io/client-go/util/workqueue`,
`queue.go`). Lean-first (no Rocq counterpart); phase 2 of the DaemonSet plan
(`notes/k8s-daemonset-plan.md`).

**Items.** The queue is generic in its item type `T` (Go, `comparable`), whose Lean values are a
type `K` (`IntoValTyped K T`), with decidable equality, injective `#`, countable (the per-item
tokens are a ghost map over `K`), and safe as map keys (`SafeMapKey T k`: comparing an item
with itself does not panic; for the DaemonSet controller `T = string`). `QItem` bundles them.

**The slice FIFO** `ownFifo l xs`: the default `Queue[T]` (`queue[T]`, a `[]T` behind a pointer)
holding `xs`, front first.

**The abstract state** `QState`: the FIFO's order `queue`, the `dirty` set (items added and not
yet handed out by `Get`), the `processing` set (items handed out by `Get` and not yet `Done`) and
the shutting-down flag. Its invariant `QState.wf`: the FIFO has no duplicates and holds exactly
the dirty items not being processed (`queue.go`'s comment on `Typed.queue`: "Every element of
queue should be in the dirty set and not in the processing set"; the converse holds too). The
operations are `QState.add`, `QState.get`, `QState.done` (the code's effect, proved by the
methods' proofs); `wf` is preserved by each (`Lemmas.lean`), `done` only for an item being
processed: `Done(k)` on a dirty item that is not being processed pushes a second copy of `k`
(`issues/k8s-workqueue-done-without-get-duplicates.md`), which is why `Done` takes the item's
token.

**The tokens.** `keyTok γ k` (exclusive, `Get` gives it, `Done` takes it): the caller processes
`k`; the lock invariant holds the authority of the ghost map `γ.proc` whose domain is the
processing set, so `keyTok γ k` means `k` is being processed and no second `keyTok γ k` exists
(`keyTok_excl`): one worker per key. `shutdownLb γ` (persistent): the queue is shutting down.
`shutdownToks γ n` (`NewTyped*` gives `shutdownToks γ shutdownPool`): each `ShutDown` or
`ShutDownWithDrain` holds one for its duration (their deferred `wg.Wait()`: Perennial's
`WaitGroup.Wait` spec bounds the concurrent waiters below `2^31`, `notes/perennial-changes.md`).

**The queue** `isTyped T q γ` (persistent): `q` is a `*Typed[T]` built by `NewTyped*` with the
default FIFO and no metrics (`noMetrics`: the queue is unnamed, or its metrics provider is the
no-op one, the global default; so no goroutine runs and the wait group's counter stays `0`).
-/
module

public import GeneratedProof.k8s_io.client_go.util.workqueue
public import Proof.k8s_io.apimachinery.pkg.util.sets.Defs
public import Proof.k8s_io.client_go.util.workqueue.Init
public import Perennial.Proof.sync
public import Perennial.Proof.TokSet
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.DGhostVar
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI k8s_io.client_go.util.workqueue

open sets (Elem present)

/-! ## The abstract state -/

/-- The typed queue's abstract state (see the file header). -/
structure QState [FfiSyntax] (K : Type) [DecidableEq K] where
  queue : List K
  dirty : GMap K Elem
  processing : GMap K Elem
  shuttingDown : Bool

section state
variable [FfiSyntax] {K : Type} [DecidableEq K]

/-- The FIFO holds each dirty item that is not being processed, once. -/
def QState.wf (σ : QState K) : Prop :=
  σ.queue.Nodup ∧
    ∀ k, k ∈ σ.queue ↔ ((σ.dirty !! k).isSome ∧ σ.processing !! k = none)

/-- `Add(k)`: ignored when shutting down or when `k` is dirty; otherwise `k` becomes dirty, and
is queued unless it is being processed (then `Done` queues it). -/
def QState.add (σ : QState K) (k : K) : QState K :=
  if σ.shuttingDown || (σ.dirty !! k).isSome then σ
  else if (σ.processing !! k).isSome then { σ with dirty := <[k := present]> σ.dirty }
  else { σ with dirty := <[k := present]> σ.dirty, queue := σ.queue ++ [k] }

/-- `Get()` handing out the front item `k` (`σ.queue = k :: rest`): it is no longer dirty and is
being processed. -/
def QState.get (σ : QState K) (k : K) (rest : List K) : QState K :=
  { σ with queue := rest, processing := <[k := present]> σ.processing,
           dirty := GMap.delete k σ.dirty }

/-- `Done(k)`: `k` is no longer being processed; if it was added meanwhile, it is queued. -/
def QState.done (σ : QState K) (k : K) : QState K :=
  if (σ.dirty !! k).isSome then
    { σ with processing := GMap.delete k σ.processing, queue := σ.queue ++ [k] }
  else { σ with processing := GMap.delete k σ.processing }

/-- The initial state. -/
def QState.init : QState K := ⟨[], ∅, ∅, false⟩

end state

/-- The ghost names of a typed queue. -/
structure QNames where
  /-- the processing set (a ghost map, its authority in the lock invariant, `keyTok` its
  elements) -/
  proc : GName
  /-- the shutting-down flag (`dghostVar`: exclusive `false`, then discarded `true`) -/
  sd : GName
  /-- the shutdown tokens (`ownTokAuth`/`ownToks`, `shutdownToks`) -/
  pool : GName
  /-- the wait group `wg` -/
  wg : sync.WaitGroupNames
  /-- the channel `stopCh` -/
  ch : ChanNames

/-- The fixed locations of a typed queue: the FIFO (`*queue[T]`), the two sets' maps, the
condition variable and its mutex, the stop channel. -/
structure QLocs where
  fifo : Loc
  dirty : Loc
  processing : Loc
  cond : Loc
  mu : Loc
  stopCh : Loc

/-- The number of shutdown tokens a queue starts with: Perennial's `WaitGroup.Wait` bounds the
waiters below `2^31` (`alloc_wait_token`), and each holder of a token is one. -/
abbrev shutdownPool : Nat := 2 ^ 31 - 2

/-- The namespace of the queue's invariants. -/
def wqN : Namespace := nroot.@"workqueue"

theorem val_false_ne_true [FfiSyntax] [GoGlobalContext] : (#false : val) ≠ #true :=
  fun h => absurd (GoGlobalContext.intoVal_inj_bool h) (by decide)

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The requirements on the item type: Lean values `K` of the Go type `T`, with decidable and
injective equality, countable, every item a safe map key. -/
class QItem (K : Type) (T : outParam go.GoType) where
  zero : ZeroVal K
  tp : TypedPointsto (GF := GF) K
  ivt : IntoValTyped (GF := GF) K T
  deq : DecidableEq K
  inj : go.IntoValInj K
  cnt : Pos.Countable K
  safe : ∀ k : K, SafeMapKey (GF := GF) T k

set_option warn.classDefReducibility false in
attribute [instance] QItem.zero QItem.tp QItem.ivt QItem.deq QItem.inj QItem.cnt QItem.safe

variable {K : Type} {T : go.GoType} [QItem (GF := GF) K T]

/-- The slice FIFO at `l` (a `*queue[T]`) holds `xs`, front first: the slice header, its
elements and its capacity. -/
def ownFifo (l : Loc) (xs : List K) : IProp GF :=
  iprop(∃ s : GoSlice, l ↦ (s : queue K) ∗ s ↦* xs ∗ ownSliceCap K s (DFrac.own 1))

/-- The FIFO's length is an `int`'s. -/
theorem ownFifo_length_lt (l : Loc) (xs : List K) :
    ownFifo (GF := GF) l xs ⊢ ⌜xs.length < 2 ^ 63⌝ := by
  unfold ownFifo
  iintro ⟨%s, -, Hs, -⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ipureintro
  rw [Hlen.1]
  word

/-- **The per-item token** (exclusive): `k` is being processed by the holder. -/
def keyTok (γ : QNames) (k : K) : IProp GF := ghostMapElem γ.proc k (DFrac.own 1) present

/-- **Shutting down** (persistent). -/
def shutdownLb (γ : QNames) : IProp GF := dghostVar γ.sd DFrac.discard true

instance shutdownLb_persistent (γ : QNames) : Persistent (shutdownLb (GF := GF) γ) := by
  unfold shutdownLb; infer_instance

/-- **Shutdown tokens** (`n` of them): each `ShutDown`/`ShutDownWithDrain` holds one. -/
def shutdownToks (γ : QNames) (n : Nat) : IProp GF := ownToks γ.pool n

/-- The shutting-down flag's ghost state, in the lock invariant. -/
def sdGhost (γ : QNames) (b : Bool) : IProp GF :=
  if b then shutdownLb γ else dghostVar γ.sd (DFrac.own 1) false

/-- **The lock invariant** of the queue's mutex: the FIFO, the sets, the flags at the abstract
state `σ` (`wf`), the processing set's ghost authority, the flag's ghost state. -/
def qLockInv (q : Loc) (L : QLocs) (γ : QNames) : IProp GF :=
  iprop(∃ (σ : QState K) (drain : Bool),
    "Hfifo" ∷ ownFifo L.fifo σ.queue ∗
    "Hdirty" ∷ L.dirty ↦$ σ.dirty ∗
    "Hproc" ∷ L.processing ↦$ σ.processing ∗
    "Hsd" ∷ structFieldRef (Typed K) go!"shuttingDown" q ↦ σ.shuttingDown ∗
    "Hdrain" ∷ structFieldRef (Typed K) go!"drain" q ↦ drain ∗
    "Hauth" ∷ ghostMapAuth γ.proc 1 σ.processing ∗
    "Hsdg" ∷ sdGhost γ σ.shuttingDown ∗
    "%Hwf" ∷ ⌜σ.wf⌝)

/-- The invariant of the wait group `wg` (whose counter stays `0`: no goroutine is started):
the counter, the waiters' authority, one shutdown token per possible waiter, and the tokens'
authority. -/
def wgInv (γ : QNames) : IProp GF :=
  iprop(∃ w : Nat,
    sync.ownWaitGroup γ.wg (W32 0) ∗ sync.ownWaitGroupWaiters γ.wg w ∗ ownToks γ.pool w ∗
    ownTokAuth γ.pool shutdownPool)

/-- **The typed queue** (persistent): see the file header. -/
def isTyped (q : Loc) (γ : QNames) : IProp GF :=
  iprop(∃ L : QLocs,
    "#Hqueue" ∷ structFieldRef (Typed K) go!"queue" q ↦□
      (interface.mkOk (go.GoType.PointerType (queue.ty T)) #L.fifo : Queue K) ∗
    "#Hdirty" ∷ structFieldRef (Typed K) go!"dirty" q ↦□ L.dirty ∗
    "#Hproc" ∷ structFieldRef (Typed K) go!"processing" q ↦□ L.processing ∗
    "#Hcond" ∷ structFieldRef (Typed K) go!"cond" q ↦□ L.cond ∗
    "#Hcv" ∷ sync.isCond L.cond (interface.mk (go.GoType.PointerType sync.Mutex.ty) #L.mu) ∗
    "#Hmu" ∷ sync.isMutex L.mu (qLockInv (K := K) q L γ) ∗
    "#Hmetrics" ∷ structFieldRef (Typed K) go!"metrics" q ↦□
      (interface.mkOk (noMetrics.ty T) #(noMetrics.mk : noMetrics K) : queueMetrics K) ∗
    "#Hwg" ∷ sync.isWaitGroup (structFieldRef (Typed K) go!"wg" q) γ.wg (wqN.@"wg") ∗
    "#Hwginv" ∷ inv (wqN.@"wginv") (wgInv γ) ∗
    "#HstopCh" ∷ structFieldRef (Typed K) go!"stopCh" q ↦□ L.stopCh ∗
    "#Honce" ∷ sync.isOnce (structFieldRef (Typed K) go!"stopOnce" q)
      (ownBroadcastChan L.stopCh γ.ch iprop(True) .Pending) iprop(True))

/-- A condition variable's locker field (`c.L`, read-only for good). -/
theorem isCond_L (c : Loc) (m : GoInterfaceOk) :
    sync.isCond (GF := GF) c m ⊢ structFieldRef sync.Cond go!"L" c ↦□ (interface.ok m : GoInterface) := by
  rw [sync.isCond_unseal]; unfold sync.isCondDef
  iintro ⟨-, $, -⟩

instance isTyped_persistent (q : Loc) (γ : QNames) :
    Persistent (isTyped (GF := GF) (K := K) q γ) := by
  unfold isTyped; simp only [named]; infer_instance

end defs

end workqueue
end EtcdGrove
end Perennial
