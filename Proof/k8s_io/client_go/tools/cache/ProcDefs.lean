/-
The shared informer's processor (`shared_informer.go`'s `sharedProcessor`): what `distribute`'s
spec is stated with. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the processor and
listeners).

The processor's listeners live in `listeners` (a map from a listener to "is syncing"), under
`listenersLock` (an `RWMutex`: `distribute` reads under the read lock). The sender of the
notifications (the informer's `OnAdd`/`OnUpdate`/`OnDelete`, under `blockDeltas`) holds each
listener's `addCh` producer (`procSend`), the listener set agreeing with the map's (a ghost
variable of its keys, half in the lock's resource, half the sender's).

* Every listener is registered before the informer starts and receives every event, from the
  first: its `i`-th notification is the `i`-th event's, with the processor's persistent `QP i`
  (one family for all listeners). (`AddEventHandlerWithOptions` after the start replays the store
  to the new listener first: not covered here.)
* Every listener is "syncing" (`true` in the map): `addListener` adds it so, and only
  `shouldResync` sets it `false`, which the informer calls only with a positive resync period
  (none in `Main`: `informers.NewSharedInformerFactory(clients, 0)`, handlers without a resync
  period). So `distribute(obj, sync)` sends to every listener, whatever `sync`.
-/
module

public import Proof.k8s_io.client_go.tools.cache.ListenerDefs
public import Perennial.Proof.sync.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

/-- The processor's ghost names. -/
structure ProcNames where
  keys : GName

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- A map's key set (the listeners'). -/
def keysOf {V : Type} (M : GMap Loc V) : GMap Loc Unit := GMap.fmap (fun _ => ()) M

/-- **The listeners' lock's resource** at fraction `q`: the started flag, the listener map (every
listener syncing), half the ghost key set (at `q`). -/
def procP (p : Loc) (γp : ProcNames) (q : Qp) : IProp GF :=
  iprop(∃ (started : Bool) (ml : Loc) (M : GMap Loc Bool),
    structFieldRef sharedProcessor go!"listenersStarted" p ↦{DFrac.own q} started ∗
    structFieldRef sharedProcessor go!"listeners" p ↦{DFrac.own q} ml ∗
    ml ↦${DFrac.own q} M ∗ ghostVar γp.keys q.half (keysOf M) ∗
    ⌜∀ l b, M !! l = some b → b = true⌝)

/-- The listeners' lock and its condition variable (persistent). -/
def isProc (p : Loc) : IProp GF :=
  iprop(∃ c : Loc, structFieldRef sharedProcessor go!"listenersRCond" p ↦□ c ∗
    sync.isCond c (sync.rlockerOf (structFieldRef sharedProcessor go!"listenersLock" p)))

instance isProc_persistent (p : Loc) : Persistent (isProc (GF := GF) p) := by
  unfold isProc; infer_instance

/-- One of the listeners' lock's reader slots. -/
def procReader (p : Loc) (γp : ProcNames) : IProp GF :=
  sync.ownRWMutex (structFieldRef sharedProcessor go!"listenersLock" p) (procP p γp)

/-- **The sender's resource**: the listeners (by ghost names), half the ghost key set, and each
listener's `addCh` producer, having sent the notifications of the events `E` (every listener
receives every event, `QP` its contract). -/
def procSend (γp : ProcNames) (QP : Nat → Ev → IProp GF) (E : List Ev) : IProp GF :=
  iprop(∃ Ls : GMap Loc LNames, ghostVar γp.keys (1 : Qp).half (keysOf Ls) ∗
    [∗map] l ↦ γl ∈ Ls, isListener l γl QP ∗ spscProducer (V := GoInterface) γl.add (E.map notifOf))

end defs

end cache
end EtcdGrove
end Perennial
