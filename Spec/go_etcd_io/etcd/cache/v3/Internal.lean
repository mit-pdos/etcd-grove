/-
# etcd's cache: the internal vocabulary (batch 1g)

What the specs of the cache's unexported functions are stated in: its ring buffers, store,
snapshots, demux, watchers, readiness flag, notifier, progress requestor, clock, and the watch loop.
No module outside `Spec/go_etcd_io/etcd/cache/v3/` imports it: the cache's clients see `Api.lean`
only. The specs here mirror the code; their predicates are opaque, with the intended realization
below (the old proof's `Inv*.lean` modules, restated over W0's model).

## The cluster facts the internals carry

Everything the cache knows of the cluster is `etcdLb γ σ` with a pure condition on `σ.kv` (W0): a
snapshot's content (`snapCert`), a gap's quietness (`quiet`, `Api.lean`), an upstream response's
events (`deliv`). `prefixRange pfx` is the range the cache covers. A snapshot's content, like
`deliv` and `quiet`, is certified only under `EtcdModel.exactFrom σ.kv 0` (the upstream watch's
events are exact only under it, 1b's `watchStep`): `snapCert γ pfx r s` says "at a reached `σ`,
`exactFrom σ.kv 0 →` the items are etcd's store under the prefix at `r`" (integration I1).

## Resources (intended realizations)

* `ownRingBuffer r cap isItem revOf items dq`: the `ringBuffer[T]` at `r` with `cap` slots holds
  `items` (revisions strictly increasing), each slot's item modelled by `isItem` (persistent); the
  old `InvRingBuffer.lean`'s `ownRingBuffer` (the struct, the buffer slice, `RingOk`).
* `kvItemAt p k kv` (persistent): `*kvItem` `p` with key `k` and key-value pointer `kv`, read-only.
* `kvTree t dq s`: the `*btree.BTree[*kvItem]` `t` holds, in key order, one `*kvItem` per entry
  `(k, kv)` of `s`, with key `k` and key-value pointer `kv` (`kvItemAt _ k kv`): the entries are
  (key, `*mvccpb.KeyValue`), not the items (`BTree.ownBTree` at the order whose `item p k` is
  `kvItemAt p k _`).
* `snapAt p r s` (persistent): the `*snapshot` `p` has revision `r` and a frozen tree holding `s`
  (entries as for `kvTree`).
* `isStore s γ pfx` (persistent): the store's `RWMutex` and `revCond`, its lock invariant: the latest
  revision `lr` with `storeRevLb`'s authoritative half, every snapshot in the history ring certified
  (`snapCert γ pfx r s`: its items are, in key order, etcd's store under the prefix at `r`, each `kv`
  a read-only `keyValueOwn` of the record), the gap after each snapshot quiet up to the next one's
  revision and the newest's up to `lr` (`quiet` at `prefixRange pfx`), `lr` reached by the cluster.
  `storeLocked s γ pfx lr` (exclusive): the write lock held with that invariant open at `lr`.
  `storeRevLb s r` (persistent): the latest revision has been at least `r`.
* `isWatcher w` (persistent): a `*watcher` (its channel, `stopOnce`, `keyPred`, `cancelResp`);
  `watcherConsumer w γ rng st` (exclusive): the receiving end of its channel at a `WatchSt` (the
  same protocol as `cacheWatchAt`, on `w.respCh`); `watcherProducer w γ rng pos` (exclusive, held in
  the demux's invariant): the sending end, with the demux's position for it.
* `isDemux d γ pfx` (persistent): the demux's `RWMutex`, its lock invariant (`minRev`, `maxRev`,
  the history ring of event batches each certified, every registered watcher's producer end at its
  position with every event under its range from the consumer's position to the demux's enqueued,
  `maxRev` reached), and its `resynced` notifier. `demuxLocked d γ pfx` (exclusive): the write lock
  held with that invariant open. `demuxFeed d γ pfx pos` (exclusive, the watch loop's): the right
  to `Init` and `Broadcast`, at the upstream watch's position `pos` (the demux's next expected
  revision).
* `isReady r` (persistent): the `ready`'s mutex and state channel; `readyWasSet r` (persistent): it
  has been set.
* `isNotifier n` (persistent): the `notifier`'s lock and channel.
* `isProgressRequestor p` (persistent): its mutex, condition variable, and its notifier
  (`watcherAt`'s `RequestProgress` triple, 1b).
* `clockOk clk` (persistent), `timerOk tm` (exclusive): the `Clock` and `Timer` interface values'
  method triples (a bundle); `realTimerAt r` (exclusive): a `*realTimer` (Perennial's `time.Timer`).
* `cacheLoop c` (exclusive): the watch loop's role (`demuxFeed`, the ready's setter, the store's
  restorer, the store watcher's registration); `cacheLoopAt c r` the same after a restore at `r`.
* `storeApplier c w` (exclusive): the store watcher `w`'s consumer end, held by `applyStorage`.
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Cache

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

/-! ## Ring buffers: the pure model -/

/-- The revisions of `items` are strictly increasing (as `int64`s). -/
def RevSorted {V : Type} (revOf : V → w64) (items : List V) : Prop :=
  items.Pairwise (fun a b => sint.Z (revOf a) < sint.Z (revOf b))

/-- The number of items with revision `< pivot` (`findFirstIndexGreaterOrEqual`). -/
def ltCount {V : Type} (revOf : V → w64) (pivot : w64) (items : List V) : Nat :=
  items.countP (fun v => decide (sint.Z (revOf v) < sint.Z pivot))

/-- The number of items with revision `≤ pivot` (one more than `findLastIndexLessOrEqual`). -/
def leCount {V : Type} (revOf : V → w64) (pivot : w64) (items : List V) : Nat :=
  items.countP (fun v => decide (sint.Z (revOf v) ≤ sint.Z pivot))

/-- The revision of the newest item, `0` if none (`PeekLatest`). -/
def latestRev {V : Type} (revOf : V → w64) (items : List V) : w64 :=
  match items.getLast? with
  | some v => revOf v
  | none => W64 0

/-- The revision of the oldest item, `0` if none (`PeekOldest`). -/
def oldestRev {V : Type} (revOf : V → w64) (items : List V) : w64 :=
  match items.head? with
  | some v => revOf v
  | none => W64 0

/-- The items `AscendGreaterOrEqual(pivot, _)` visits, in order. -/
def ascendGeVisited {V : Type} (revOf : V → w64) (pivot : w64) (items : List V) : List V :=
  items.drop (ltCount revOf pivot items)

/-- The items `AscendLessThan(pivot, _)` visits, in order. -/
def ascendLtVisited {V : Type} (revOf : V → w64) (pivot : w64) (items : List V) : List V :=
  items.take (ltCount revOf pivot items)

/-- The items `DescendGreaterThan(pivot, _)` visits, in order. -/
def descendGtVisited {V : Type} (revOf : V → w64) (pivot : w64) (items : List V) : List V :=
  (items.drop (leCount revOf pivot items)).reverse

/-- The items `DescendLessOrEqual(pivot, _)` visits, in order. -/
def descendLeVisited {V : Type} (revOf : V → w64) (pivot : w64) (items : List V) : List V :=
  (items.take (leCount revOf pivot items)).reverse

/-- What `Append` leaves: the new item at the end, the oldest dropped if the ring was full. -/
def ringAppend {V : Type} (cap : Nat) (items : List V) (v : V) : List V :=
  if items.length < cap then items ++ [v] else items.tail ++ [v]

/-- `v`'s revision is above the newest item's. -/
def RevAbove {V : Type} (revOf : V → w64) (items : List V) (v : V) : Prop :=
  ∀ last, items.getLast? = some last → sint.Z (revOf last) < sint.Z (revOf v)

/-! ## The cache's range and the store's model -/

/-- **The range a cache of `pfx` covers** (all keys for `pfx = ""`). -/
def prefixRange (pfx : GoString) : KeyRange := { key := pfx, rangeEnd := prefixEnd pfx }

/-- A response's next position for the upstream watch (`demuxFeed`): after events up to `b`, `b + 1`;
after a progress notification at `p`, `p + 1` at least. -/
def WatchRespM.lastRev (m : WatchRespM) : Option Nat :=
  m.events.getLast?.map (·.rev)

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-! ## Ring buffers -/

/-- **The ring buffer at `r`** (`cap` slots) holds `items`, read at `dq`. -/
opaque ownRingBuffer {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] {V : Type}
    (r : Loc) (cap : Nat) (isItem : T' → V → IProp GF) (revOf : V → w64) (items : List V)
    (dq : DFrac := DFrac.own 1) : IProp GF := iprop(True)

/-- The `revisionOf` closure `f` returns each item's revision. -/
def revisionOfSpec {T' : Type} {V : Type} (f : GoFunc) (isItem : T' → V → IProp GF)
    (revOf : V → w64) : IProp GF :=
  iprop(□ ∀ (p : T') (v : V),
    {{ isItem p v }} (App (Val #f) (Val #p)) {{ RET #(revOf v); True }})

/-- The iteration callback `iter` over the visited items `vis`, with the caller's invariant `P` (on
the number visited) and final `Q` (if it stops). -/
def iterSpec {T' : Type} {V : Type} (iter : GoFunc) (isItem : T' → V → IProp GF) (revOf : V → w64)
    (vis : List V) (P : Nat → IProp GF) (Q : IProp GF) : IProp GF :=
  iprop(□ ∀ (i : Nat) (p : T') (v : V), ⌜vis[i]? = some v⌝ -∗
    {{ P i ∗ isItem p v }}
      (App (App (Val #iter) (Val #(revOf v))) (Val #p))
    {{ (cont : Bool), RET #cont; if cont then P (i + 1) else Q }})

/-! ## Items, trees, snapshots -/

/-- `*kvItem` `p` with key `k` and key-value pointer `kv` (persistent). -/
opaque kvItemAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (k : GoString) (kv : Loc) : IProp GF := iprop(True)

/-- The store's working tree `t` holds the entries `s` (key, key-value pointer), in key order. -/
opaque kvTree [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (t : Loc) (dq : DFrac) (s : List (GoString × Loc)) : IProp GF := iprop(True)

/-- The `*snapshot` `p` has revision `r` and a frozen tree holding `s` (persistent). -/
opaque snapAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (r : Nat) (s : List (GoString × Loc)) : IProp GF := iprop(True)

/-- **A snapshot's content is etcd's store under `pfx` at `r`**: the items, in key order, are the
present keys of `σ.kv.storeAt r` in the prefix range (under the compaction condition
`exactFrom σ.kv 0`, see the header), each `kv` read-only holding the record. -/
def snapCert (γ : Cluster) (pfx : GoString) (r : Nat) (s : List (GoString × Loc)) : IProp GF :=
  iprop(∃ (σ : State) (kvs : List KV), etcdLb γ σ ∗ ⌜r ≤ σ.kv.rev⌝ ∗
    ⌜(EtcdModel.exactFrom σ.kv 0 → Store.rangeKVs (σ.kv.storeAt r) (prefixRange pfx) kvs) ∧
      s.map Prod.fst = kvs.map (·.key)⌝ ∗
    [∗list] e; kv ∈ s; kvs, keyValueOwn e.2 DFrac.discard (KeyValueM.ofKV kv))

/-! ## The store -/

/-- **`s` is the cache's store** for `pfx` of the cluster `γ` (persistent). -/
opaque isStore [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (γ : Cluster) (pfx : GoString) : IProp GF := iprop(True)

/-- The store's write lock held, its invariant open at the latest revision `lr`. -/
opaque storeLocked [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (γ : Cluster) (pfx : GoString) (lr : Nat) : IProp GF := iprop(True)

/-- The store's latest revision has been at least `r` (persistent). -/
opaque storeRevLb [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (r : Nat) : IProp GF := iprop(True)

/-- **Every event under the prefix of a revision below `a` is in the store's latest snapshot or
before it** (persistent: the store's latest revision `L` only grows, and no prefix event lies in
`(L, a)`). What an applied response's successor needs: its events continue from `a`. -/
opaque storeUpTo [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (a : Int) : IProp GF := iprop(True)

/-- **The store's ceiling** (exclusive, the watch loop's): the store's latest revision is at most
`r`, and every response certified for the store is (`storeCeilLb`); raised by its holder before it
broadcasts a response above it, and `Restore`'s revision is at least it (so the latest revision
never decreases). -/
opaque storeCeil [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (r : Nat) : IProp GF := iprop(True)

/-- The store's ceiling has been raised to at least `r` (persistent). -/
opaque storeCeilLb [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (r : Nat) : IProp GF := iprop(True)

/-- **The snapshot `p` answers for revision `tgt`**: its frozen tree's items are, in key order, the
present keys of etcd's store under the prefix at `tgt` (its own revision at most `tgt`, the gap up
to `tgt` quiet), each `kv` a read-only record. -/
def snapFor (p : Loc) (γ : Cluster) (pfx : GoString) (tgt : Nat) : IProp GF :=
  iprop(∃ (r : Nat) (s : List (GoString × Loc)) (σ : State) (kvs : List KV),
    snapAt p r s ∗ etcdLb γ σ ∗
    ⌜r ≤ tgt ∧ tgt ≤ σ.kv.rev ∧ Store.rangeKVs (σ.kv.storeAt tgt) (prefixRange pfx) kvs ∧
      s.map Prod.fst = kvs.map (·.key)⌝ ∗
    [∗list] e; kv ∈ s; kvs, keyValueOwn e.2 DFrac.discard (KeyValueM.ofKV kv))

/-! ## Watchers and the demux -/

/-- A `*watcher` (persistent). -/
opaque isWatcher [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (w : Loc) : IProp GF := iprop(True)

/-- A new watcher, not yet registered, filtering by `rng` (`none`: no filter, the store's). -/
opaque watcherNew [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (w : Loc) (rng : Option KeyRange) : IProp GF := iprop(True)

/-- The watcher has been stopped: its channel closed (persistent). -/
opaque watcherStopped [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (w : Loc) : IProp GF := iprop(True)

/-- The receiving end of the watcher `w`'s channel, on the range `rng`, at `st`. -/
opaque watcherConsumer [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (w : Loc) (γ : Cluster) (rng : KeyRange) (st : WatchSt) : IProp GF :=
  iprop(True)

/-- The sending end of the watcher `w`'s channel (the demux's), at the demux's position `pos`. -/
opaque watcherProducer [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (w : Loc) (γ : Cluster) (rng : KeyRange) (pos : Option Int) : IProp GF :=
  iprop(True)

/-- **`d` is the cache's demux** for `pfx` of `γ`, feeding the store `s` (persistent). -/
opaque isDemux [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (d : Loc) (γ : Cluster) (pfx : GoString) (s : Loc) : IProp GF := iprop(True)

/-- The demux's write lock held, its invariant open; `pend`: a response recorded in the history
(`updateStoreLocked`) but not yet broadcast to the watchers (`broadcastLocked`). -/
opaque demuxLocked [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (d : Loc) (γ : Cluster) (pfx : GoString) (s : Loc) (pend : Option WatchRespM) :
  IProp GF := iprop(True)

/-- The watch loop's right to feed the demux, the upstream watch at position `pos`. -/
opaque demuxFeed [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (d : Loc) (γ : Cluster) (pfx : GoString) (s : Loc) (pos : Option Int) : IProp GF :=
  iprop(True)

/-- **An upstream response's fact** for a watch of `rng` at position `pos`, the next position
`pos'`: events (`deliv`), a progress notification (`quiet`), or a response that moves nothing
(created, canceled, a compaction, or a header revision `0`: never a progress notification, which
must be quiet). -/
def respFact (γ : Cluster) (rng : KeyRange) (pos : Option Int) (m : WatchRespM)
    (pos' : Option Int) : IProp GF :=
  iprop((∃ (σ : State) (b : Int), etcdLb γ σ ∗ ⌜deliv σ.kv rng pos m.events b ∧ pos' = some (b + 1)⌝) ∨
    (∃ σ : State, etcdLb γ σ ∗ ⌜m.events = [] ∧ m.hdrRev ≠ 0 ∧ quiet σ.kv rng pos m.hdrRev ∧
      pos' = WatchSt.afterProgress pos m.hdrRev⌝) ∨
    ⌜m.events = [] ∧ (m.hdrRev = 0 ∨ m.created = true ∨ m.canceled = true ∨ m.compactRev ≠ 0) ∧
      pos' = pos⌝)

/-! ## Readiness, notifier, progress requestor, clock -/

opaque isReady [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (r : Loc) : IProp GF := iprop(True)
opaque readyWasSet [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (r : Loc) : IProp GF := iprop(True)
opaque isNotifier [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (n : Loc) : IProp GF := iprop(True)
opaque isProgressRequestor [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) : IProp GF := iprop(True)
opaque clockOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (clk : GoInterface) : IProp GF := iprop(True)
opaque timerOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (tm : GoInterface) : IProp GF := iprop(True)
opaque realTimerAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (r : Loc) : IProp GF := iprop(True)
/-- `ch` is a timer's channel: receiving from it never panics (persistent). -/
opaque timerChan [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ch : Loc) : IProp GF := iprop(True)
/-- `pred` (a `func() bool` closure over the `ready` `r`) returns whether `r.isReady` is `b`, under
`r.mu`. -/
opaque readyPredFor [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (r : Loc) (pred : GoFunc) (b : Bool) : IProp GF := iprop(True)
/-- The progress requestor's notifier `n` (a `progressNotifier` interface value): its
`RequestProgress(ctx)` returns some error for any context (1b's `watcherAt`). -/
opaque progressNotifierOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (n : GoInterface) : IProp GF := iprop(True)
/-- The right to `Add(1)` to the cache's wait group `wg` and run a goroutine that calls `Done`
(the wait group's protocol: a fraction of `cacheOpen`, the goroutine's thread token). -/
opaque wgAddOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (wg : Loc) : IProp GF := iprop(True)

/-! ## The watch loop -/

/-- The watch loop's role in the cache `c`. -/
opaque cacheLoop [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (c : Loc) : IProp GF := iprop(True)

/-- The watch loop's role after a restore of the store at `r` (the demux to start at `r + 1`). -/
opaque cacheLoopAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (c : Loc) (r : Nat) : IProp GF := iprop(True)

/-- The watch loop's role while the upstream watch from `rev` runs (the store watcher registered,
its applier running): `demuxFeed`, `storeCeil`, the ready's setter. -/
opaque cacheLoopRun [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (c : Loc) (rev : Int) : IProp GF := iprop(True)

/-- The store watcher `w`'s consumer end, held by `applyStorage`. -/
opaque storeApplier [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (c w : Loc) : IProp GF := iprop(True)

/-- The receiving end of `watch`'s `applyErr` channel `ch` (the applier sends at most one error,
then closes it). -/
opaque applyErrChan [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ch : Loc) : IProp GF := iprop(True)

/-- `watch`'s `*sync.Once` `ro`, guarding `c.ready.Set`. -/
opaque readyOnceAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (c ro : Loc) : IProp GF := iprop(True)

/-- The cache `c`'s store is `s` (persistent: the field, read-only, with `isStore`). -/
opaque cacheStoreAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (c s : Loc) : IProp GF := iprop(True)

/-! ## Internal laws -/

/-- The cache's revision lower bounds are its store's. -/
def cacheRevLb_store.spec : Prop := ∀ (c s : Loc) (r : Nat),
  cacheStoreAt (GF := GF) c s ⊢ (cacheRevLb c r ∗-∗ storeRevLb s r)

/-- The ceiling's holder raises it. -/
def storeCeil_raise.spec : Prop := ∀ (s : Loc) (r r' : Nat), r ≤ r' →
  storeCeil (GF := GF) s r ⊢ |==> storeCeil s r'

/-- A lower bound of the ceiling. -/
def storeCeil_lb.spec : Prop := ∀ (s : Loc) (r : Nat),
  storeCeil (GF := GF) s r ⊢ storeCeil s r ∗ storeCeilLb s r

end res

end Cache
end EtcdGrove
end Perennial
