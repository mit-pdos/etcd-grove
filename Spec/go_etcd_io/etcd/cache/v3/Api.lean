/-
# etcd's cache: the vocabulary (batch 1g)

`go.etcd.io/etcd/cache/v3` (`cache/*.go`): a local copy of the keys under a prefix, fed by one client
watch, that serves `Get` and `Watch` without going to the cluster. **Its specs state what a cache user
observes in terms of W0's model** (`api/v3/Model.lean`'s `KVHist`, `api/v3/State.lean`'s `etcdLb`),
never the cache's internals (its store, demux, ring buffers: `Internal.lean`):

* a `Get` answers **etcd's store at the revision asked for** (or at the cache's latest revision for
  `0`), restricted to the requested range, with that latest revision `L` as the header's, at a
  state the cluster has reached (`etcdLb γ σ`, `L ≤ σ.kv.rev`). A linearizable `Get` (not
  `WithSerializable`) is at least as fresh as a state the caller knew at the call (`etcdLb γ σ0`,
  `σ0.kv.rev ≤ L`); a serializable one at least as fresh as a revision the cache was known to have
  reached (`cacheRevLb c r0`). The cluster's history is kept whole in the model, so the answer at a
  compacted revision is still a well-defined statement (the cache keeps its own window; a revision
  outside it is an error, `ErrCompacted`).
* a `Watch` delivers **the history's events under the requested range**, revision after revision,
  with no gap and no duplicate (`evsBetween`), and progress notifications that say no event under
  the range happened up to their revision; it may end (the channel closed) at any time, or with a
  compaction's cancel response. Each response's fact is `etcdLb γ σ` with a pure condition on
  `σ.kv`, so a client combines a watch's events with any other reply (a `Get`, a `Put`'s) through
  the history (`etcdLb_ord`, `Reach`).

**The compaction condition.** The cache's history and snapshots are built from its upstream client
watch, whose events and progress facts 1b's `watchStep` states only under W0's `exactFrom` (a
compaction at a revision that changes a key twice keeps one change). So `deliv`, `quiet` and
`getOk`'s content are stated under `EtcdModel.exactFrom h 0`, at the state the fact names; a user
discharges it from its workload (no transaction puts and deletes one key) or a cluster that never
compacts, as for a client watch (integration I1).

**Principals.** `isCache c γ who pfx`'s `who` is the client's default principal (W0's round 3:
`isClient c γ who`); the cache's own requests (its list, its upstream watch, `RequestProgress`) run
on its internal context (`WithCancel(Background())`: `ctxPrin who ctx who`); a `Get` passes the
caller's context to the client's `Get` for the linearizable revision, so it takes `ctxPrin who ctx p`
for the caller's principal `p`. The answers themselves are the cache's: the cache checks no
permission, so a cache user sees every key under the prefix the cache's own principal may read.

**Not a `Watcher`** (batch-1g.md open question 1, decided at integration I1: recorded, not unified).
The cache's `Watch` cannot meet 1b's `Watcher.WatchTriple`/`watchChAt`: (1) 1b's response owns its
events in full (`watchRespAt`, consumers rewrite them), the cache's are shared read-only
(`watchRespRO` at most); (2) a compaction cancel's `CompactRevision` is the cache's window start,
not a cluster compaction (`watchStep`'s `cr ≤ σ.kv.compacted` is false); (3) a rejected request's
cancel (`Canceled`, compact revision `0`, `closeErr` `nil`) is no `watchStep` response; (4)
`watchChAt ch γ p` names the call's principal `p` as admitted (`σa`), while the cache serves any
caller with its own principal's view; (5) the cache sends no `Created` and fabricates headers
(revision only). Unifying would take, in 1b's `ApiWatch.lean`: a `WatchRespM` ownership index
(full / read-only), a `watchStep` arm for a source-local cancel (any `cr`, no claim), an arm for
a rejected request's first-and-only cancel, and `Watcher.WatchTriple`'s channel at the handle's
principal rather than the call's (a weaker contract every `watcherAt` realizer then meets). What
is shared: the event messages (`eventOwn` below is W0's `EtcdWire.eventOwn` at `DFrac.discard`),
the history (`KVHist`, `etcdLb`) and `exactFrom`.

## Pure vocabulary

* `RevEvent`: one event of the history with its revision (W0's `Event`); `evsBetween h rng a b`: the
  events of revisions `a..b` of the history `h` whose key is in the range `rng`, in order.
* `WatchRespM`: a `clientv3.WatchResponse` as the cache sends one (header revision, events,
  compact revision, flags). `WatchSt`: where a consumer of a cache watch is (`live pos`: every event
  under the range from revision `pos` on is still to come, `none` when the watch started "from now"
  and nothing came yet; `rejected`: the one cancel response of a rejected request is pending;
  `closed`: nothing more).
* `getUnsupported`, `watchUnsupported`, `cacheRange`, `rangeOk`: the cache's request validation
  (`validateGet`, `validateWatch`, `validateRange`), on W0's `OpM`.
* `defaultConfigM`, `cfgApply`, `CfgValid`, `CfgBounded`: the configuration (`config.go`) as Goose's
  `Config` struct.

## Resources

* `isCache c γ who pfx` (persistent): `c` is a cache of the keys under `pfx` of the cluster `γ`  reading through a client of principal `who` (`New`'s
  result). Intended realization: the cache's fields read-only; the client's `kvAt`/`watcherAt` for
  its `kv` and `watcher` (W0, 1b) and the read permission `etcdPeek γ` `New` took; the invariants
  of the store (`isStore`: every snapshot is etcd's store under the prefix at its revision, every
  gap between snapshots quiet, the latest revision reached by the cluster), of the demux
  (`isDemux`: the history it holds is the upstream watch's, every registered watcher's position
  is owed exactly the events from it on), of `ready` and the progress requestor; the wait group's
  protocol (each goroutine counted by a thread token it holds, the `cacheOpen` token to exclude a
  `Watch`'s `Add` from `Close`'s `Wait`).
* `cacheOpen c q` (fractional): the right to call `Watch` (which adds to the cache's wait group) as
  opposed to `Close` (which waits on it), `nonissues/etcd-cache-watch-during-close-waitgroup.md`:
  `Watch` takes a fraction, `Close` the whole; both give it back.
* `cacheRevLb c r` (persistent): the cache's latest revision has been at least `r` (its store's
  revision only grows: a re-list after an upstream failure restores at a linearizable read's
  revision, above everything the cache saw). From `WaitForRevision`, `WaitReady` (`r = 1`), `Get`.
* `cacheWatchAt ch γ rng st` (exclusive): the consumer of a cache watch's channel `ch` on the range
  `rng`, at `st` (`cacheWatchAt_recv`). Intended realization: the watch goroutine's channel
  (unbuffered, closed by the goroutine) with a ghost variable of the consumer's position, whose
  other half the watcher's demux entry (`isDemux`) keeps.
* W0's `etcdPeek γ` (`State.lean`, persistent): the program's permission to look at the cluster's
  state without changing it: the cache's own reads of the cluster (its initial list, the revision a
  linearizable `Get` waits for) are made of it. `New` takes it.
* `wrapsErr err e` (persistent): `errors.Is(err, e)` holds (`err` is `e`, or a `fmt.Errorf("%w")`
  wrapping of it): how a caller tests `ErrUnsupportedRequest` and `ErrKeyRangeInvalid`.
* `eventOwn`, `eventsAt`, `watchRespAt` (transparent over W0's `EtcdWire.eventOwn`, `respHeaderOwn`,
  read-only): a received
  response's memory, read-only (the cache shares every event among its watchers and its store).

## Laws

`isCache_persistent`, `isCache_ne_null`, `wrapsErr_persistent`, `wrapsErr_refl`, `errorsIs_wraps`, `cacheRevLb_persistent`, `cacheRevLb_zero`, `cacheRevLb_mono`,
`cacheRevLb_reached`, `cacheOpen_fractional`, `cacheWatchAt_recv`, `init` (the error variables).

## Requirement snippets

`examples/specreq/cache/`: `get.go` (a linearizable `Get` sees an acknowledged write; a `Get` at a
revision agrees with a watch's events; `WaitForRevision` then a serializable `Get`; the range checks
the callers test), `watch.go` (a watch from a revision reports exactly the writes, gap-free; a
progress notification is quiet; the channel's end; a rejected request), `lifecycle.go` (`New` with
options, `WaitReady`, `Close`).
-/
module

public import GeneratedProof.go_etcd_io.etcd.cache.v3
public import Spec.PkgInit.go_etcd_io.etcd.cache.v3
public import Spec.go_etcd_io.etcd.client.v3.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Cache

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

/-! ## History events -/

/-- **One event of the history, with its revision.** -/
structure RevEvent where
  rev : Nat
  ev : Event

/-- The events of revision `r` of `h`, tagged with it. -/
def revEvents (h : KVHist) (r : Nat) : List RevEvent :=
  (h.eventsAt r).map (fun e => ⟨r, e⟩)

/-- **The events of revisions `a..b` (inclusive) of the history `h` whose key is in `rng`**, in
order (revision `1` and below have none; above `h.rev` none are known, so callers keep
`b ≤ h.rev`). -/
def evsBetween (h : KVHist) (rng : KeyRange) (a b : Int) : List RevEvent :=
  ((List.range (h.rev + 1)).filter (fun (r : Nat) => decide (a ≤ (r : Int) ∧ (r : Int) ≤ b))).flatMap
    (fun (r : Nat) => (revEvents h r).filter (fun e => decide (rng.mem e.ev.key)))

/-! ## Watch responses -/

/-- **A `clientv3.WatchResponse` as the cache sends one**: its header's revision (every response the
cache sends has a header: `0` but for a progress notification), its events, its compact revision,
its `Canceled` and `Created` flags. -/
structure WatchRespM where
  hdrRev : Nat
  events : List RevEvent
  compactRev : Int
  canceled : Bool
  created : Bool

/-- **Where the consumer of a cache watch is.** -/
inductive WatchSt where
  /-- every event under the range from revision `pos` on is still to come (`none`: the watch started
  at the cache's newest revision and has delivered nothing yet, so its first event is the first it
  owes); `seen`, the highest revision a response of the watch has named (an event's, or a
  progress notification's): a later progress notification is not below it -/
  | live (pos : Option Int) (seen : Nat)
  /-- a rejected request: its one cancel response is pending -/
  | rejected
  /-- the channel is closed, or will be at the next receive -/
  | closed

/-- The position after a progress notification at `p`. -/
def WatchSt.afterProgress (pos : Option Int) (p : Nat) : Option Int :=
  some (match pos with
    | some a => max a ((p : Int) + 1)
    | none => (p : Int) + 1)

/-- **An events response's events against the history** from the consumer's position `pos`: they
are the events under `rng` of the revisions `a..b`, where `a` is the position (or, from "now",
the first event's revision), `b` at least the last event's; the next position is `b + 1`. The
events' exactness holds under W0's compaction condition `exactFrom h 0` (every revision up to the
compaction changes each key at most once): the cache's history is its upstream client watch's,
whose events 1b's `watchStep` states exact only under `exactFrom` (integration I1; the condition
from the watch's first revision would do, but the upstream watch's start is the cache's, which
its users do not see). -/
def deliv (h : KVHist) (rng : KeyRange) (pos : Option Int) (evs : List RevEvent) (b : Int) : Prop :=
  evs ≠ [] ∧ b ≤ h.rev ∧ (EtcdModel.exactFrom h 0 →
  ∃ a : Int, (pos = some a ∨ (pos = none ∧ ∀ e ∈ evs.head?, a = e.rev)) ∧ evs = evsBetween h rng a b)

/-- **A progress notification at `p` against the history**: the cluster reached `p`, and (under
the compaction condition `exactFrom h 0`, as `deliv`) no event under `rng` happened from the
consumer's position up to `p`. -/
def quiet (h : KVHist) (rng : KeyRange) (pos : Option Int) (p : Nat) : Prop :=
  p ≤ h.rev ∧ (EtcdModel.exactFrom h 0 → ∀ a, pos = some a → evsBetween h rng a p = [])

/-! ## The cache's request validation -/

/-- `validateGet`'s rejections (the options the cache does not serve). A keys-only `Get` is
served with values (`validateGet` does not reject `WithKeysOnly`): the answer below is the full
key-values either way. -/
def getUnsupported (o : OpM) : Prop :=
  o.countOnly = true ∨ o.prevKV = true ∨ o.sort ≠ none ∨ o.limit ≠ W64 0 ∨
  o.minModRev ≠ W64 0 ∨ o.maxModRev ≠ W64 0 ∨ o.minCreateRev ≠ W64 0 ∨ o.maxCreateRev ≠ W64 0

/-- `validateWatch`'s rejections. -/
def watchUnsupported (o : OpM) : Prop :=
  o.prevKV = true ∨ o.fragment = true ∨ o.createdNotify = true ∨ o.filterPut = true ∨
  o.filterDelete = true

/-- **The range a cache request names**: the key argument (not the `Op`'s key, which `WithPrefix`
and `WithFromKey` rewrite for an empty key) and the `Op`'s range end. Unlike the client's request
(W0's `OpM.endReq`: a non-`nil` empty end is `"\x00"`), the cache reads a `nil` and a non-`nil`
empty end alike, as one key (`validateRange`, `snapshot.Range`: `len(endKey) == 0`). -/
def cacheRange (key : GoString) (o : OpM) : KeyRange :=
  { key := key, rangeEnd := o.rangeEnd.getD [] }

/-- **`validateRange`**: the range is a single key, a from-key range (only for the root cache,
`pfx = ""`), or a non-empty `[key, end)`; for a prefix cache, inside `[pfx, prefixEnd pfx)`. -/
def rangeOk (pfx : GoString) (r : KeyRange) : Prop :=
  if r.rangeEnd = [] then pfx = [] ∨ (keyLe pfx r.key ∧ keyLt r.key (prefixEnd pfx))
  else if r.rangeEnd = [W8 0] then pfx = []
  else keyLt r.key r.rangeEnd ∧ (pfx = [] ∨ (keyLe pfx r.key ∧ keyLe r.rangeEnd (prefixEnd pfx)))

/-- **Where a `Watch`'s consumer starts** (if the cache was ready): a rejected request's cancel, or
the requested revision (`none`: "from now", `WithRev` absent or `0`). -/
def watchStart (pfx : GoString) (rng : KeyRange) (o : OpM) : WatchSt :=
  if watchUnsupported o ∨ ¬ rangeOk pfx rng then .rejected
  else .live (if o.rev = W64 0 then none else some (sint.Z o.rev)) 0

/-- The `GetResponse` a successful `Get` returns: the header's revision `L` (its other fields zero),
the key-values, `More` false, `Count` their number. -/
def getRespM (L : Nat) (kvs : List KV) : RangeRespM :=
  { hdr := some { clusterId := W64 0, memberId := W64 0, revision := W64 L, raftTerm := W64 0,
                  leaderId := W64 0 },
    kvs := kvs.map KeyValueM.ofKV, more := false, count := W64 kvs.length }

/-! ## The configuration -/

open go_etcd_io.etcd.cache.v3 in
/-- The value `defaultConfig()` returns (durations in nanoseconds). -/
def defaultConfigM [GooseExts] : Config :=
  { PerWatcherBufferSize' := W64 10
    HistoryWindowSize' := W64 2048
    ResyncInterval' := W64 50000000
    InitialBackoff' := W64 50000000
    MaxBackoff' := W64 2000000000
    GetTimeout' := W64 5000000000
    WaitTimeout' := W64 3000000000
    BTreeDegree' := W64 32
    ProgressRequestInterval' := W64 100000000
    ProgressNotifyInterval' := W64 600000000000 }

open go_etcd_io.etcd.cache.v3 in
/-- The configuration after the options with transformers `gs`, applied in order. -/
def cfgApply [GooseExts] (gs : List (Config → Config)) (c : Config) : Config :=
  gs.foldl (fun c g => g c) c

open go_etcd_io.etcd.cache.v3 in
/-- `newCache`'s validation: `HistoryWindowSize > 0` and `BTreeDegree >= 2`. -/
def CfgValid [GooseExts] (c : Config) : Prop :=
  0 < sint.Z c.HistoryWindowSize' ∧ 2 ≤ sint.Z c.BTreeDegree'

open go_etcd_io.etcd.cache.v3 in
/-- **What an accepted configuration must also meet**, which `newCache` does not check: a
non-negative `PerWatcherBufferSize` (`make(chan, n)` panics on a negative one, in `Watch` and in the
watch loop's goroutine), below `2^32` (Perennial's `make(chan T, n)` is defined there: a
limitation of the model, kept here, at the one producer); the history window at most `2^61` (the
ring buffer's index arithmetic, `at`); the B-tree degree at most `2^62` (its `maxItems()`
overflows above). -/
def CfgBounded [GooseExts] (c : Config) : Prop :=
  0 ≤ sint.Z c.PerWatcherBufferSize' ∧ sint.Z c.PerWatcherBufferSize' < 2 ^ 32 ∧
  sint.Z c.HistoryWindowSize' ≤ 2 ^ 61 ∧ sint.Z c.BTreeDegree' ≤ 2 ^ 62

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- The `mvccpb.KeyValue` model of an event's key-value: a put's record, a delete's key and
revision (its other fields unspecified). -/
def kvMatches (e : RevEvent) (m : KeyValueM) : Prop :=
  match e.ev with
  | .put k r => m = KeyValueM.ofKV (KV.ofRec k r) ∧ r.modRev = e.rev
  | .delete k => m.key = k ∧ m.modRevision = W64 e.rev

/-- Whether an event is a delete (`mvccpb.Event_EventType` `DELETE`). -/
def RevEvent.del (e : RevEvent) : Bool :=
  match e.ev with
  | .put _ _ => false
  | .delete _ => true

/-- **A `*mvccpb.Event` holding the event `e`**, read-only: W0's message predicate
`EtcdWire.eventOwn` (`api/v3/Wire.lean`, unfolded by `eventOwn_unfold`) at `DFrac.discard`, with no
`PrevKv` (the cache rejects `WithPrevKV` and watches without it). The cache's events are its
upstream watch's messages, made read-only (1b's `watchRespAt_persist`) and shared among its
watchers and store. Persistent once W0's messages at `DFrac.discard` are (requested of W0 at
integration: a `*Own_discard_persistent` law in `Wire.lean`). -/
def eventOwn (p : Loc) (e : RevEvent) : IProp GF :=
  iprop(∃ m : EventM, EtcdWire.eventOwn p DFrac.discard m ∗
    ⌜m.del = e.del ∧ m.prevKv = none ∧ kvMatches e m.kv⌝)

/-- A read-only slice of `*mvccpb.Event`s holding `evs`, in order. -/
def eventsAt (sl : GoSlice) (evs : List RevEvent) : IProp GF :=
  iprop(∃ ps : List Loc, sl ↦*□ ps ∗ [∗list] p; e ∈ ps; evs, eventOwn p e)

/-- **A received `WatchResponse` value `v` modelled by `m`**: its header (never `nil`) read-only
with revision `m.hdrRev`, its events, its fields, and no close error (the cache never sets one: `Err()` is `nil` but for a cancel)
(persistent). -/
def watchRespAt (v : go_etcd_io.etcd.client.v3.WatchResponse) (m : WatchRespM) : IProp GF :=
  iprop(∃ hm : HeaderM, respHeaderOwn v.Header' DFrac.discard hm ∗ ⌜hm.revision = W64 m.hdrRev⌝ ∗
    eventsAt v.Events' m.events ∗
    ⌜v.CompactRevision' = W64 m.compactRev ∧ v.Canceled' = m.canceled ∧ v.Created' = m.created ∧
      v.closeErr' = GoInterface.nil⌝)

/-- **`c` is a cache of the keys under `pfx` of the cluster `γ`** (persistent). -/
opaque isCache (c : Loc) (γ : Cluster) (who : Principal) (pfx : GoString) : IProp GF := iprop(True)

/-- **The right to call `Watch`** (a fraction) or `Close` (the whole). -/
opaque cacheOpen (c : Loc) (q : Qp) : IProp GF := iprop(True)

/-- **The cache's latest revision has been at least `r`** (persistent). -/
opaque cacheRevLb (c : Loc) (r : Nat) : IProp GF := iprop(True)

/-- **The consumer of a cache watch's channel `ch`**, on the range `rng`, at `st` (exclusive). -/
opaque cacheWatchAt (ch : Loc) (γ : Cluster) (rng : KeyRange) (st : WatchSt) : IProp GF :=
  iprop(True)

/-- **What a successful `Get` returns**: the response (read-only: its key-values are the cache's),
the latest revision `L` as its header's, the answer at the revision asked for (`rr`, or `L` for `0`)
restricted to the range, at a state the cluster reached, fresher than the anchors `σ0` (if
linearizable) and `r0`. The content holds under the compaction condition `exactFrom σ.kv 0` (as
`deliv`: the snapshots are built from the upstream watch's events). -/
def getOk (c : Loc) (γ : Cluster) (rng : KeyRange) (o : OpM) (σ0 : State) (r0 : Nat)
    (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop(∃ (L : Nat) (kvs : List KV) (σ : State),
    ⌜err = GoInterface.nil⌝ ∗ rangeRespOwn resp DFrac.discard (getRespM L kvs) ∗ etcdLb γ σ ∗
    cacheRevLb c L ∗
    ⌜0 ≤ sint.Z o.rev ∧ sint.Z o.rev ≤ L ∧ r0 ≤ L ∧ L ≤ σ.kv.rev ∧
      (o.serializable = false → σ0.kv.rev ≤ L) ∧
      (EtcdModel.exactFrom σ.kv 0 →
        Store.rangeKVs (σ.kv.storeAt (if sint.Z o.rev = 0 then L else (sint.Z o.rev).toNat)) rng kvs)⌝)

/-- **`errors.Is(err, e)` holds**: `err` is `e`, or wraps it (`fmt.Errorf("%w: ...", e)`)
(persistent). -/
opaque wrapsErr (err e : GoInterface) : IProp GF := iprop(True)

open go_etcd_io.etcd.cache.v3 in
/-- **What a failed `Get` returns**: no response, a non-`nil` error; for a request with an option the
cache does not serve, an error wrapping `ErrUnsupportedRequest`; for a served request whose range
it rejects, `ErrKeyRangeInvalid` (either, or the context's error, if the cache was not yet ready and
the context is done); for a served request, `ErrFutureRev` (rpctypes', unwrapped) unless the
context is done, the revision asked for is one the cluster reached (the cache's other errors:
`ErrCompacted`, a negative revision), or the request is linearizable (the client's own `Get` and the
timeout may fail first). -/
def getErr (γ : Cluster) (pfx : GoString) (ctx : GoInterface) (rng : KeyRange) (o : OpM) (resp : Loc)
    (err : GoInterface) : IProp GF :=
  iprop(⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗
    (⌜getUnsupported o⌝ -∗
      ((∃ e, globalAddr ErrUnsupportedRequest ↦□ e ∗ wrapsErr err e) ∨ Context.ctxDone ctx)) ∗
    (⌜¬ getUnsupported o ∧ ¬ rangeOk pfx rng⌝ -∗
      (globalAddr ErrKeyRangeInvalid ↦□ err ∨ Context.ctxDone ctx)) ∗
    (⌜¬ getUnsupported o ∧ rangeOk pfx rng⌝ -∗
      (⌜err = errVal .futureRev⌝ ∨ Context.ctxDone ctx ∨
       (∃ σ : State, etcdLb γ σ ∗ ⌜sint.Z o.rev ≤ σ.kv.rev⌝) ∨ ⌜o.serializable = false⌝)))

/-- **The `KeyPredicate` closure `f` decides `P`** on the key a read-only slice holds (persistent;
`ExactKey`, `FromKey`, `Range`, `KeyPredForRange`'s results). -/
def keyPredAt (f : GoFunc) (P : GoString → Prop) : IProp GF :=
  iprop(⌜f ≠ func.nil⌝ ∗ □ ∀ (sl : GoSlice) (k : GoString) (dq : DFrac),
    {{ sl ↦*{dq} k }} (App (Val #f) (Val #sl)) {{ RET #(decide (P k)); sl ↦*{dq} k }})

/-- The `Option` closure `f` (`func(*Config)`) transforms the `Config` it is given by `g`
(persistent). -/
def cfgOptAt (f : GoFunc) (g : go_etcd_io.etcd.cache.v3.Config → go_etcd_io.etcd.cache.v3.Config) :
    IProp GF :=
  iprop(□ ∀ (cp : Loc) (c : go_etcd_io.etcd.cache.v3.Config),
    {{ cp ↦ c }} (App (Val #f) (Val #cp)) {{ RET #(); cp ↦ g c }})

/-- The `[]Option` slice `sl` (read-only) holds closures with the transformers `gs`, in order. -/
def cfgOptsAt (sl : GoSlice)
    (gs : List (go_etcd_io.etcd.cache.v3.Config → go_etcd_io.etcd.cache.v3.Config)) : IProp GF :=
  iprop(∃ fs : List GoFunc, sl ↦*□ fs ∗ [∗list] f; g ∈ fs; gs, cfgOptAt f g)

/-! ## Laws -/

def isCache_persistent.spec : Prop := ∀ c γ who pfx, Persistent (isCache (GF := GF) c γ who pfx)

def cacheRevLb_persistent.spec : Prop := ∀ c r, Persistent (cacheRevLb (GF := GF) c r)

/-- Every cache has reached revision `0`. -/
def cacheRevLb_zero.spec : Prop := ∀ c, ⊢ cacheRevLb (GF := GF) c 0

def cacheRevLb_mono.spec : Prop := ∀ c r r', r' ≤ r → cacheRevLb (GF := GF) c r ⊢ cacheRevLb c r'

/-- A revision the cache reached, the cluster reached. -/
def cacheRevLb_reached.spec : Prop := ∀ c γ who pfx r,
  isCache (GF := GF) c γ who pfx ∗ cacheRevLb c r ⊢ ∃ σ, etcdLb γ σ ∗ ⌜r ≤ σ.kv.rev⌝

/-- A cache is a non-`nil` pointer. -/
def isCache_ne_null.spec : Prop := ∀ c γ who pfx, isCache (GF := GF) c γ who pfx ⊢ ⌜c ≠ null⌝

def wrapsErr_persistent.spec : Prop := ∀ err e, Persistent (wrapsErr (GF := GF) err e)

/-- A non-`nil` error wraps itself. -/
def wrapsErr_refl.spec : Prop := ∀ e, e ≠ GoInterface.nil → ⊢ wrapsErr (GF := GF) e e

/-- **`errors.Is(err, e)`** for an error that wraps `e`: `true` (Perennial's `errors.Is` follows
`Unwrap`, which `fmt.Errorf`'s `%w` provides: a trust-boundary fact of `errors` and `fmt`). -/
def errorsIs_wraps.spec : Prop := ∀ (err e : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ wrapsErr err e }}
    (App (App (Val (@! errors.Is)) (Val #err)) (Val #e))
  {{ RET #true; True }}

def cacheOpen_fractional.spec : Prop := ∀ c (q1 q2 : Qp),
  cacheOpen (GF := GF) c (q1 + q2) ⊣⊢ cacheOpen c q1 ∗ cacheOpen c q2

/-- **Receiving from a cache watch's channel** (`<-ch`, `for resp := range ch`):
* `closed`: nothing (`ok = false`), for good;
* `rejected`: the cancel response (`Canceled`, no events, compact revision `0`), then closed;
* `live pos`: the channel closed (the context done, the cache closed, its upstream watch
  restarted), or a response `m` (header never `nil`, never `Created`), one of
  - **events**: `m.events` are the history's events under the range from the position to some
    `b ≥` the last one's revision (`deliv`), the next position `b + 1`;
  - **a progress notification** at `p = m.hdrRev ≠ 0`: the cluster reached `p` and nothing
    under the range happened from the position up to `p` (`quiet`);
  - **a progress notification** is never below the highest revision the watch named before
    (`seen`);
  - **a cancel** (`Canceled`), at any time: a lagging watcher compacted out of the cache's history
    window (the code's `CancelReason` is `ErrCompacted`'s text; not stated); then closed. -/
def cacheWatchAt_recv.spec : Prop := ∀ (ch : Loc) (γ : Cluster) (rng : KeyRange) (st : WatchSt),
  {{ cacheWatchAt (GF := GF) ch γ rng st }}
    (App (Val (chan.receive go_etcd_io.etcd.client.v3.WatchResponse.ty)) (Val #ch))
  {{ (v : go_etcd_io.etcd.client.v3.WatchResponse) (ok : Bool), RET (PairV #v #ok);
      match st with
      | .closed => ⌜ok = false⌝ ∗ cacheWatchAt ch γ rng .closed
      | .rejected => ⌜ok = true⌝ ∗ cacheWatchAt ch γ rng .closed ∗ ∃ m, watchRespAt v m ∗
          ⌜m.canceled = true ∧ m.events = [] ∧ m.compactRev = 0 ∧ m.created = false⌝
      | .live pos seen =>
          (⌜ok = false⌝ ∗ cacheWatchAt ch γ rng .closed) ∨
          (⌜ok = true⌝ ∗ ∃ m, watchRespAt v m ∗ ⌜m.created = false⌝ ∗
            ((⌜m.canceled = false ∧ m.compactRev = 0 ∧ m.hdrRev = 0⌝ ∗
                ∃ (σ : State) (b : Int), etcdLb γ σ ∗ ⌜deliv σ.kv rng pos m.events b⌝ ∗
                  cacheWatchAt ch γ rng (.live (some (b + 1)) (max seen b.toNat))) ∨
             (⌜m.canceled = false ∧ m.compactRev = 0 ∧ m.events = [] ∧ m.hdrRev ≠ 0⌝ ∗
                ∃ σ : State, etcdLb γ σ ∗ ⌜seen ≤ m.hdrRev ∧ quiet σ.kv rng pos m.hdrRev⌝ ∗
                  cacheWatchAt ch γ rng (.live (WatchSt.afterProgress pos m.hdrRev) m.hdrRev)) ∨
             (⌜m.canceled = true ∧ m.events = []⌝ ∗ cacheWatchAt ch γ rng .closed))) }}

open go_etcd_io.etcd.cache.v3 in
/-- **The package's error variables** (`ErrUnsupportedRequest`, `ErrKeyRangeInvalid`,
`ErrCacheTimeout`, `ErrNotReady`): read-only, non-`nil`, distinct, and none of rpctypes' errors. -/
def init.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ⊢
    ∃ e1 e2 e3 e4 : GoInterface,
      globalAddr ErrUnsupportedRequest ↦□ e1 ∗ globalAddr ErrKeyRangeInvalid ↦□ e2 ∗
      globalAddr ErrCacheTimeout ↦□ e3 ∗ globalAddr ErrNotReady ↦□ e4 ∗
      ⌜[e1, e2, e3, e4].Nodup ∧ (∀ e ∈ [e1, e2, e3, e4], e ≠ GoInterface.nil ∧
        ∀ x : EtcdErr, e ≠ errVal x)⌝

end res

end Cache
end EtcdGrove
end Perennial
