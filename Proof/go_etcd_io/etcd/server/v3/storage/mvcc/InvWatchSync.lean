/-
The watchable store's sync machinery (`watchable_store.go`, unit 3b): the events a range read of
the bucket yields (`rangeEvents`, `kvsToEvents`), the victims out with their mover
(`moveVictims`), the background loops' wait group and stop channel, and the right to close the
store. Lean-first; `notes/decisions.md`, "The watchable store's concurrency (unit 3)".

**The bucket's entries as events.** A range read of the revisions `[lo, hi)` of the committed log
returns the bucket's entries of those revisions in key order, which is revision order
(`bucketRange_logEnts`, `SyncModel.lean`): `logEnts log lo hi`, each entry its revision, whether it
is a tombstone, and the key-value it encodes (`KvEnt`). `kvsToEvents` makes each the event
`KvEnt.ev` (a tombstone a `DELETE` with the revision as `ModRevision`) and keeps those of a key
some member of the group covers (`wgCovers`): `entsEvents`. They are the log's events
(`logEnts_events`: `logEvents`, what `notify` sends).

**The victims' mover** (`moveVictims`) takes the victim batches out of the lock: each victim's
watcher moves to the "out" population (`WsState.Wo`, the lock keeping half its state), the mover
holding the rest (`moverRes`: the other half of its state, the lock's halves of its delivered
events and live ghost, and what its batch delivers), until it puts the watcher back (synced or
unsynced, the batch sent) or makes it a victim again.

**The loops** run on the store's wait group (`wsWgInv`: the counter is the number of done tokens
out, `wsDone` each loop's, `wsWaiter` the closer's) until the stop channel (`isStopChan`, a
broadcast channel closed once: `stopCloser`) is closed. `wsCloser` is `Close`'s right: the stop
channel's close, the wait, and the inner store's close (`storeCloser`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore
public import Perennial.Proof.sync

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-! ## The bucket's entries as events (pure) -/

/-- A bucket entry as `kvsToEvents` reads it: its revision, whether it is a tombstone, and the
key-value it encodes. -/
structure KvEnt where
  rev : Rev
  tomb : Bool
  kv : EtcdKv

/-- The entry's key and value in the bucket. -/
def KvEnt.pair (e : KvEnt) : GoString × GoString := (revBytes e.rev e.tomb, kvEncode e.kv)

/-- The event `kvsToEvents` makes of the entry: a tombstone is a `DELETE` with the revision as
`ModRevision`, else a `PUT`; no previous key-value. -/
def KvEnt.ev (e : KvEnt) : EvM :=
  if e.tomb then ⟨true, { e.kv with modRev := e.rev.main }, none⟩ else ⟨false, e.kv, none⟩

/-- The bucket's entries of revision `r` (changes `cs`, the state `before` before them), in
sub-revision order (`bucketOfRev`'s, as entries). -/
def entsOfRev (r : Nat) (before : List EtcdKv) (cs : List Change) : List KvEnt :=
  cs.zipIdx.filterMap fun p =>
    (changeKv (W64 r) before cs p.2).map fun kv => ⟨⟨W64 r, W64 p.2⟩, p.1.isDel, kv⟩

/-- The bucket's entries of the revisions `[lo, hi)` of `log`, in revision order. -/
def logEnts (log : Log) (lo hi : Nat) : List KvEnt :=
  ((List.range' lo (hi - lo)).map fun m =>
    entsOfRev m (stateAt log (m - 1)) (log.getD m [])).flatten

open Classical in
/-- Some member of `W` covers the key `k` (`watcherGroup.contains`, whose spec decides it
classically). -/
def wgCovers (W : GMap Loc WatchRange) (k : GoString) : Bool :=
  decide (∃ w r, W !! w = some r ∧ r.covers k = true)

/-- The events `kvsToEvents` makes of the entries `ents` for the group `W`. -/
def entsEvents (W : GMap Loc WatchRange) (ents : List KvEnt) : List EvM :=
  (ents.map KvEnt.ev).filter fun ev => wgCovers W ev.kv.key

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The address of the watchable store's wait group. -/
abbrev wsWgAddr (s : Loc) : Loc := structFieldRef watchableStore go!"wg" s

end addrs

/-- The namespace of the store's wait group (Perennial's `isWaitGroup`). -/
def wsWgWGN : Namespace := nroot.@"mvccWaitGroup"

/-- The namespace of the store's wait-group counter invariant (`wsWgInv`). -/
def wsWgN : Namespace := nroot.@"mvccWgCounter"

section reprs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-! ## The victims out with their mover -/

/-- **A victim out with the mover** (`moveVictims`), with its state `st` and its batch `B`: the
mover's half of its state (the lock keeps the other, `WsState.Wo`), the lock's halves of its
delivered events `evsw` and of its live ghost, its names, fixed fields, channel and filters, and
what the batch delivers: the delivered events and the batch's are the range's up to its
`minRev` (`evsWf`, as a victim's `popFacts`), with `victimBatchOk`. -/
def moverRes (γ : WsNames) (w : Loc) (st : WatcherSt) (B : EventBatch) : IProp GF :=
  iprop(∃ (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice) (evsw : List EvM),
    watcherMeta γ w γw ∗ watcherFixed w r fcs ∗ watcherChan γ w γw st.ch ∗ filtersOk fcs ∗
    ⌜sint.Z r.startRev ≤ (γw.lo : Int) ∧ (γw.lo : Int) ≤ sint.Z st.minRev ∧
      victimBatchOk γw.lo st B⌝ ∗
    watcherOwn w st (1 : Qp).half ∗ monoListAuthOwn γw.evs (1 : Qp).half evsw ∗
    dghostVar γw.live (DFrac.own (1 : Qp).half) true ∗
    evsWf γ r γw.lo (evsw ++ B.evs) (sint.nat st.minRev))

/-! ## The loops' wait group and stop channel -/

/-- The store's wait-group counter (an invariant, in `wsWgN`): the counter is the number `n` of
done tokens out (`γd`: one per running loop, `wsDone`). -/
def wsWgInv (γwg : sync.WaitGroupNames) (γd : GName) : IProp GF :=
  iprop(∃ (ctr : w32) (n : Nat), sync.ownWaitGroup γwg ctr ∗ ownTokAuth γd n ∗
    ⌜sint.Z ctr = (n : Int)⌝)

/-- A loop's right to call `s.wg.Done()` once (a done token). -/
def wsDone (s : Loc) : IProp GF :=
  iprop(∃ (γwg : sync.WaitGroupNames) (γd : GName),
    sync.isWaitGroup (wsWgAddr s) γwg wsWgWGN ∗ inv wsWgN (wsWgInv γwg γd) ∗ ownToks γd 1)

/-- The closer's right to call `s.wg.Wait()` (no other waiter, no more `Add`). -/
def wsWaiter (s : Loc) : IProp GF :=
  iprop(∃ (γwg : sync.WaitGroupNames) (γd : GName),
    sync.isWaitGroup (wsWgAddr s) γwg wsWgWGN ∗ inv wsWgN (wsWgInv γwg γd) ∗
    sync.ownWaitGroupWaiters γwg 0)

/-- The right to close the stop channel `c` (once). -/
def stopCloser (c : Loc) : IProp GF :=
  iprop(∃ γc : ChanNames, ownBroadcastChan c γc iprop(True) Broadcast.Pending)

/-- **The right to close the watchable store** `s` over the store `st` (`Close`, once): the stop
channel's close, the wait for the loops, and the inner store's close. -/
def wsCloser (s st : Loc) : IProp GF :=
  iprop(∃ stc : Loc, s.[watchableStore, go!"stopc"] ↦□ stc ∗ stopCloser stc ∗ wsWaiter s ∗
    storeCloser st)

end reprs

end mvcc
end EtcdGrove
end Perennial
