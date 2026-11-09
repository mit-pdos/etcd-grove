/-
# `pkg/wait`: the wait registries (batch 2c), vocabulary

Two primitives (`wait.go`, `wait_time.go`):

* **`Wait`** (`New()`: a `*list`, 64 shards of a locked map `id ↦ chan any` with buffer 1):
  `Register(id)` makes a channel for `id` (and panics, `log.Panicf("dup id")`, if `id` is
  registered); `Trigger(id, x)` removes `id`'s channel, if any, sends `x` on it and closes it.
  The server registers each request under its fresh id before proposing it
  (`processInternalRaftRequestOnce`), the apply thread triggers every applied entry's id with its
  result (`applyEntryNormal`), and the requester triggers its own id with `nil` when it gives up
  (a timeout, a failed proposal: "GC wait").
* **`WaitTime`** (`NewTimeList()`: a `*timeList`): `Wait(d)` returns a channel closed once a
  `Trigger(d')` with `d ≤ d'` has run (or an already-closed one if the last trigger was at least
  `d`); `Trigger(d)` closes the channels of every deadline at most `d`. The server's `applyWait`:
  the apply thread triggers each applied index, the read loop and `waitAppliedIndex` wait for one.

## Vocabulary

* `WaitNames` (opaque ghost names).
* `listAt l γw P` (persistent): `l` is a `*list` registry whose registrations under `id` are
  answered by values `x` with `P id x` (fixed at `New`; the triggerer supplies it).
* `waitToks γw U` (exclusive): the ids registered so far are `U`; `waitTok γw id` (exclusive) the
  right to register `id` once (`waitToks_take`: a fresh id's). The client chooses how it knows an id
  is fresh (the server: `IdUtil.idFresh`, exclusive, kept beside `waitToks` in its invariant).
* `waitRecv γw id ch` (exclusive): `ch` is `id`'s channel, and the holder is its one receiver: a
  receive on it yields a value with `P id x` (`waitRecv_recv`, with `listAt`). The holder may instead
  give it up to `Trigger(id, nil)` (the requester's "GC wait").
* `waitWasReg γw id`, `waitGone γw id`, `waitNever γw id` (persistent): `id` has been registered;
  was registered and removed (it never comes back); will never be registered (its token burnt,
  `waitToks_never`). `waitDone` is the last two: no value is owed; `IsRegistered`'s `false` gives it
  for an id the caller knows registered or never-registered; `Trigger` accepts it (round 1,
  completeness F7: the apply thread skips a result nobody waits for, `apply/apply.go:40`).
* `timeListAt tl P` (persistent): `tl` is a `*timeList` whose triggers at `d` carry `□ P d`; `P` is
  downward closed (a premise of `NewTimeList`).
* `timeChan ch P d` (persistent): a channel `Wait(d)` returned; a receive completes only with
  `□ P d` (`timeChan_recv`).

The predicates `P` are the client's, fixed at allocation, as Perennial's channel and lock idioms
take theirs: a generic synchronization primitive, a deliberate departure from "TaDa, not HoCAP"
(`PRINCIPLES.md`), as `isLock l R`.

## Intended realization

`listAt`: for each shard, `isRWMutex` whose invariant holds the shard's map, and for each `id` in
it a registration: Perennial's channel ownership of a buffered-1 channel with an empty buffer and
the saved fact that its value is `P id`; `waitToks` a ghost set authority (`waitTok` its
singletons), the invariant holding `id`'s token while it is registered (so a second `Register(id)`
is excluded: `dup id` never panics); `waitRecv` the channel's receive half. `timeListAt`: the lock
invariant `□ P last`, each map entry's channel open with the saved deadline; `closec` (closed in
`init`, the package's fact) for a deadline already passed.

## Requirement snippets

`examples/specreq/wait/wait.go` (`ReqRegisterTrigger`, `ReqGiveUp`, `ReqWaitTime`).
-/
module

public import GeneratedProof.go_etcd_io.etcd.pkg.v3.wait
public import Spec.PkgInit.go_etcd_io.etcd.pkg.v3.wait
public import Perennial.Proof.context

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Wait

open Iris Iris.BI

/-- A wait registry's ghost names (opaque). -/
opaque WaitNames : Type := Unit

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **`l` is a `*list` registry** whose registrations under `id` are answered by values with
`P id`. Persistent. -/
opaque listAt (l : Loc) (γw : WaitNames) (P : w64 → GoInterface → IProp GF) : IProp GF := iprop(True)

/-- The ids handed out for registration so far. Exclusive. -/
opaque waitToks (γw : WaitNames) (U : List w64) : IProp GF := iprop(True)

/-- The right to register `id` (once). Exclusive. -/
opaque waitTok (γw : WaitNames) (id : w64) : IProp GF := iprop(True)

/-- `ch` is `id`'s channel and the holder its one receiver. Exclusive. -/
opaque waitRecv (γw : WaitNames) (id : w64) (ch : Loc) : IProp GF := iprop(True)

/-- **`tl` is a `*timeList`** whose triggers at `d` carry `□ P d`. Persistent. -/
opaque timeListAt (tl : Loc) (P : w64 → IProp GF) : IProp GF := iprop(True)

/-- `id` has been registered (persistent: from `Register`). -/
opaque waitWasReg (γw : WaitNames) (id : w64) : IProp GF := iprop(True)

/-- `id` was registered and its registration removed (triggered): it never comes back (its token was
one-shot). Persistent. -/
opaque waitGone (γw : WaitNames) (id : w64) : IProp GF := iprop(True)

/-- `id` will never be registered (its token burnt). Persistent. -/
opaque waitNever (γw : WaitNames) (id : w64) : IProp GF := iprop(True)

/-- **`id` is not registered and never will be again** (no value owed to anyone). -/
def waitDone (γw : WaitNames) (id : w64) : IProp GF := iprop(waitGone γw id ∨ waitNever γw id)

/-- `ch` was returned by a `Wait(d)` of a time list over `P`. Persistent. -/
opaque timeChan (ch : Loc) (P : w64 → IProp GF) (d : w64) : IProp GF := iprop(True)

def listAt_persistent.spec : Prop := ∀ l γw P, Persistent (listAt (GF := GF) l γw P)
def timeListAt_persistent.spec : Prop := ∀ tl P, Persistent (timeListAt (GF := GF) tl P)
def timeChan_persistent.spec : Prop := ∀ ch P d, Persistent (timeChan (GF := GF) ch P d)
def waitToks_timeless.spec : Prop := ∀ γw U, Timeless (waitToks (GF := GF) γw U)
def waitWasReg_persistent.spec : Prop := ∀ γw id, Persistent (waitWasReg (GF := GF) γw id)
def waitGone_persistent.spec : Prop := ∀ γw id, Persistent (waitGone (GF := GF) γw id)
def waitNever_persistent.spec : Prop := ∀ γw id, Persistent (waitNever (GF := GF) γw id)

/-- A registered id was not burnt. -/
def waitRecv_never.spec : Prop := ∀ (γw : WaitNames) (id : w64) (ch : Loc),
  waitRecv (GF := GF) γw id ch ∗ waitNever γw id ⊢ iprop(False)

/-- **Burning a fresh id's token**: it will never be registered (an id of another member's entry,
which the apply thread triggers here). -/
def waitToks_never.spec : Prop := ∀ (γw : WaitNames) (U : List w64) (id : w64), id ∉ U →
  waitToks (GF := GF) γw U ⊢ |==> waitToks γw (id :: U) ∗ waitNever γw id

/-- **A fresh id's registration right.** -/
def waitToks_take.spec : Prop := ∀ (γw : WaitNames) (U : List w64) (id : w64), id ∉ U →
  waitToks (GF := GF) γw U ⊢ |==> waitToks γw (id :: U) ∗ waitTok γw id

/-- **Receiving on a registration's channel** (a blocking receive or a `select` case) yields a
value with `P id`. (In a `select`, the case's `recvAu` is built from `waitRecv` under an Iris
conjunction with `waitRecv` itself, kept for the other cases.) -/
def waitRecv_recv.spec : Prop := ∀ (l : Loc) (γw : WaitNames) (P : w64 → GoInterface → IProp GF)
    (id : w64) (ch : Loc),
  listAt (GF := GF) l γw P ∗ waitRecv γw id ch ⊢
    ∃ γc : ChanNames, isChan ch γc GoInterface ∗
      ∀ Φ : GoInterface → Bool → IProp GF, (∀ v ok, P id v -∗ Φ v ok) -∗ recvAu γc GoInterface Φ

/-- **Receiving on a time list's channel** completes only with `□ P d`. -/
def timeChan_recv.spec : Prop := ∀ (ch : Loc) (P : w64 → IProp GF) (d : w64),
  timeChan (GF := GF) ch P d ⊢
    ∃ γc : ChanNames, isChan ch γc Unit ∗
      □ ∀ Φ : Unit → Bool → IProp GF, (∀ v ok, □ P d -∗ Φ v ok) -∗ recvAu γc Unit Φ

end vocab

end Wait
end EtcdGrove
end Perennial
