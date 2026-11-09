/-
# mvcc's watch API: the vocabulary (batch 3f)

What a user of mvcc's watchable store (`watchable_store.go`, `watcher.go`) holds and what each
response of a watch stream means. The users: etcd's gRPC watch handler (v3rpc's `serverWatchStream`,
batch 2b: one stream per gRPC stream, its receive loop the control side, its send loop the
consumer), and the server (2d) that makes the store (`New`), restores it (`Restore`) and closes it.

## A watch is a sequence of facts about the store's history

The store's history is 3e's model (`Model.lean`: `MvccState`, W0's `KVHist`), and its watch
guarantee is stated against **the notified history** (`MvccState.notified`: the committed revisions
and the revision being committed, which `watchableStoreTxnWrite.End` sends to the watchers before it
makes it visible to reads). Every response a stream's consumer receives comes with **persistent
facts** about the history at a point the store reached (`mvccLb γ h`: the store's notified history
extends `h`; with 3e's client-owned `mvccState γ σ` it gives `histLe h σ.notified`, `mvccLb_le`, so
the server's invariant relates it to the cluster's history, as W0's `etcdLb` does for a client), read against the
watcher's **position**: the revision up to which its events were all delivered. No atomic update is
fired: a watch reports the past. This is the server-side mirror of 1b's `watchStep`
(`client/v3/ApiWatch.lean`), over mvcc's own registrations, ids and positions.

* **A watcher** (`WatcherM`): its range (3e's `MRange`, read as the watcher groups do,
  `MRange.watchMem`: a single key, or an affine interval of the interval tree), its filters (the
  pure predicates `drops` its filter functions compute: an event a filter holds of is not sent), its
  start revision, its **position at registration** (`startRev - 1`; from `0`, the store's revision
  at registration: its events from the next one on), and its **stamp** (the number of responses the
  stream had sent when it was registered: a stream-wide progress after that covers it).
* **A response** (`WResp`): the watcher's id (`-1`: a progress of every watcher of the stream), its
  events (`EvM`: `Type` and `Kv` as a watch delivers them, `evOf`), its revision, its compaction
  revision (`0`: none).
* `posOf W id rs`: the position of the watcher `W` (id `id`) after the responses `rs` received
  before: the last event's revision of its last response with events, or the revision of its last
  progress (its own, or a stream-wide one after its stamp).
* **What a response says** (`wsRespOk`): a response of a watcher `W` at its position `p`
  and its events position (`posEvOf`, events only: a compaction is checked against it) (`wStep`): with events, **exactly the events of `W` of the revisions `p + 1` to the last event's**
  (`wEvents`: whole revisions, in order, filtered), the response's revision at least that and
  reached; a progress, no event of `W` from `p + 1` up to its revision, which is reached and not
  below `W`'s start revision (`progStep`); a compaction, the revision after `W`'s last event is
  below a compaction revision of the store (a progress does not move that: after a `Restore`, a
  compaction may come at or below a progress's revision). A stream-wide progress (id `-1`): `progStep` for every watcher
  registered before it (by stamp) and not cancelled before it. No response of a watcher after its
  cancel (`wsCanceled`), none after its compaction response but a resent compaction response
  (`issues/etcd-watch-compacted-resent.md`).
* **The compaction condition** (the user's, round 11 of the mvcc API, `watch-compaction.md`): the
  events and progress facts hold when every revision from the watcher's next one up to the
  store's compaction revision changes each key at most once (`exactFrom`; vacuous while the
  compaction revision is below the position). A compaction at a revision that changes a key twice
  keeps only the key's last change there, which a watcher reading that revision afterwards gets
  alone (`nonissues/etcd-mvcc-watch-compact-rev-subrev-lost.md`; through gRPC such a revision comes
  from `issues/etcd-txn-check-intervals-sibling.md`). The condition is the client's to discharge
  (its workload, or a store that never compacts).

## Resources

* `watchableAt kv γ` (persistent): **`kv` is a watchable store of `γ`** (its dynamic type
  `*watchableStore`: `watchableAt_shape`), with 3e's handle (`watchableAt_isMvcc`). Intended
  realization: the store's `isMvcc` and the watchable store's invariant: its lock `mu` over the two
  watcher groups (each watcher's record, its channel's stream invariant), the victims, the loops'
  stop channel and wait group; the store's notified history moves only under `mu`.
* `mvccLb γ h` (persistent): **the store has notified at least `h`**. Intended realization: a
  fragment of a monotone (prefix-ordered) ghost authority of the notified history, kept by the
  store's invariant beside 3e's half of `mvccState` (the two agree: the authority is
  `σ.notified`); it grows at a commit's first step and at a `Restore` (whose update shows the new
  history extends the committed one, which is the notified one under `s.mu`), never otherwise (a
  compaction raises only its compaction revision). **A constraint on 3e's realization** (round 1,
  S1): `mvccLb_le` and `mvccLb_get` are plain entailments over `mvccState` alone, so the authority (or
  a fractional half of it) must be part of `mvccState`'s own realization, not only of the store's
  invariant.
* `wsAt w γ ι` (persistent): **`w` (a `*watchStream`) is a watch stream of `γ`, named `ι`**: its
  channel `wsChanOf ι`, its lock over `nextID`, `closed`, `cancels`, `watchers`. Intended
  realization: the stream's invariant: the channel's sends (all of them by the store's code, under
  its locks or by `moveVictims` for a victim it holds), each with its `wsRespOk` facts, a ghost list
  of them (`wsCons` its consumer half, `wsSentLb` its lower bounds); the registrations (a ghost map
  id ↦ watcher, persistent entries: `wsReg`), the cancelled ids with the send count at their removal
  (`wsCanceled`).
* `wsCtl ι n` (exclusive): **the stream's control side**: the stream's next id is `n`, every
  registered id below it (`wsReg_ctl`; the auto ids are consecutive). One goroutine registers
  watchers (v3rpc's receive loop). The counter cannot wrap: `Watch` takes a time receipt bounded by
  the adequacy theorem's receipt bound (`ReceiptBoundLe`), which the stream's invariant counts.
* `wsOpen ι` (exclusive): the right to close the stream (`Close` closes its channel: a second
  `Close` panics).
* `wsCons ι rs` (exclusive): **the consumer has received the responses `rs`**, in order.
* `wsReg ι id W` (persistent): the stream's watcher `id` was registered as `W`.
* `wsCanceled ι id c` (persistent): every response of the watcher `id` is among the first `c` the
  stream sent (its cancel removed it from the store's groups then).
* `wsSentLb ι n` (persistent): the stream has sent at least `n` responses. `wsClosed ι`
  (persistent): the stream was closed (`Close`'s post; why a `Watch` may fail on a valid range).
* Go values (definitions): `evOwn p e` (a fresh `*mvccpb.Event`, owned, its `Kv` read-only: shared
  by the watchers; `PrevKv` `nil`), `wrespAt v r` (a `WatchResponse` value: its events slice and
  events owned by the consumer), `filterOk f d` (a `FilterFunc` computes `d`), `filtersAt fcs ds`,
  `errMsgOk err msg` (an error whose `Error()` returns `msg`).

## Laws

`mvccLb_le`, `mvccLb_get` (the lower bound against 3e's `mvccState`), `watch_persistent`,
`wsReg_agree`, `wsCanceled_mono`, `wsSentLb_zero`, `wsSentLb_mono`,
`watchableAt_shape`, `watchableAt_isMvcc`, `wsCons_recv` (receiving on the stream's channel, plain or in a
`select`, and the non-blocking receive of a drain: empty means every response sent before is
received), `watch_init` (the package's watch variables and error values).

## Requirement snippets

`examples/specreq/mvccwatch/`: `history.go` (events from the start revision without a gap, whole
revisions, filters; a watch from the current revision; compaction), `progress.go` (a progress means
nothing missed; a stream-wide progress covers every live watcher; the drain before a creation),
`lifecycle.go` (ids fresh and not `-1`, an empty range refused, `Cancel` stops a watcher,
`Close`, calls after `Close` send nothing), `store.go` (the store's writes reach the watchers,
`Restore`, `Close` gives the loops' resources back).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Spec.go_etcd_io.etcd.pkg.v3.adt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire
open Classical

/-! ## What a watch delivers (pure) -/

/-- The key an event changes. -/
def evKey : Event → Key
  | .put k _ => k
  | .delete k => k

/-- **A watcher's range as the watcher groups read it**: a single key (`end` `nil`, the key
watchers' map), else the affine interval `[key, end)` of the interval tree (an empty `end` the top:
every key from `key` on; an empty `key` the top too: such a range holds no key). For a non-empty
key this is `MRange.mem` (v3rpc sends `"\x00"` for an empty key). -/
def MRange.watchMem (rg : MRange) (k : Key) : Prop :=
  if rg.endNil then k = rg.key else Adt.ivlCmp (Adt.pointOf k) (rg.key, rg.rangeEnd) = 0

/-- **An event as a watch response carries it** (`*mvccpb.Event`: `Type` and `Kv`). -/
structure EvM where
  del : Bool
  kv : KeyValueM

/-- The event `e` of revision `r` as delivered: a put's record; a delete's key with `ModRevision`
`r` and zero fields (`watchableStoreTxnWrite.End`, `kvsToEvents` patch the revision in). -/
def evOf (r : Nat) : Event → EvM
  | .put k kr => { del := false, kv := KeyValueM.ofKV (KV.ofRec k kr) }
  | .delete k => { del := true,
                   kv := { key := k, createRevision := W64 0, modRevision := W64 r,
                           version := W64 0, value := [], lease := W64 0 } }

/-- **A watcher, as registered** (see the header). -/
structure WatcherM where
  range : MRange
  drops : List (EvM → Bool)
  startRev : Int
  pos : Nat
  stamp : Nat

/-- The watcher sends the event `e` of revision `r`: its key in the range, no filter drops it. -/
def WatcherM.keeps (W : WatcherM) (r : Nat) (e : Event) : Prop :=
  W.range.watchMem (evKey e) ∧ ∀ d ∈ W.drops, d (evOf r e) = false

/-- **The events of `W` of the revisions `lo..hi`** of `h`, in order (revision order, each
revision's events in their order), with their revisions. -/
def wEvents (W : WatcherM) (h : KVHist) (lo hi : Nat) : List (Nat × Event) :=
  ((List.range' lo (hi + 1 - lo)).flatMap (fun n => (h.eventsAt n).map (fun e => (n, e)))).filter
    (fun x => decide (W.keeps x.1 x.2))

/-- **The compaction condition**: every revision from `lo` up to `h`'s compaction revision changes
each key at most once (vacuous when `h.compacted < lo`). The same statement as 1b's
`ClientV3.exactFrom` (`evKey` is its `Event.key`), which mvcc cannot import; both should move to
W0's model (`req/go_etcd_io_etcd_api_v3.md`, "from 3f"). -/
def exactFrom (h : KVHist) (lo : Nat) : Prop :=
  ∀ r : Nat, lo ≤ r → r ≤ h.compacted → ((h.eventsAt r).map evKey).Nodup

/-- **A watch response** (`mvcc.WatchResponse`): id, events, revision, compaction revision. -/
structure WResp where
  id : w64
  evs : List EvM
  rev : w64
  compactRev : w64

/-- **The position of the watcher `W` (id `id`) after the responses `rs`**: see the header. -/
def posOf (W : WatcherM) (id : w64) (rs : List WResp) : Nat :=
  rs.zipIdx.foldl (fun p xi =>
    if xi.1.id = id ∧ xi.1.compactRev = W64 0 then
      match xi.1.evs.getLast? with
      | some e => (sint.Z e.kv.modRevision).toNat
      | none => (sint.Z xi.1.rev).toNat
    else if xi.1.id = W64 (-1) ∧ W.stamp ≤ xi.2 then (sint.Z xi.1.rev).toNat
    else p) W.pos

/-- **The events position** of the watcher `W` (id `id`) after `rs`: as `posOf`, counting only its
responses with events (a progress does not move it): what the store's `minRev - 1` bounds, so what a
compaction response is checked against (round 1, F1: after a snapshot `Restore` a watcher told by a
progress that nothing changed up to `P` may still be sent a compaction at or below `P`,
`issues/etcd-mvcc-watch-compacted-after-progress-restore.md`). -/
def posEvOf (W : WatcherM) (id : w64) (rs : List WResp) : Nat :=
  rs.foldl (fun p x =>
    if x.id = id ∧ x.compactRev = W64 0 then
      match x.evs.getLast? with
      | some e => (sint.Z e.kv.modRevision).toNat
      | none => p
    else p) W.pos

/-- The shape of every response: a compaction response is a watcher's, without events, at revision
`0`; a stream-wide one (`-1`) a progress. -/
def respShape (r : WResp) : Prop :=
  (r.compactRev ≠ W64 0 → r.evs = [] ∧ r.rev = W64 0 ∧ r.id ≠ W64 (-1)) ∧
  (r.id = W64 (-1) → r.evs = [] ∧ r.compactRev = W64 0)

/-- **A progress of `W` at `rev`, from the position `p`**, against the reached history `h`: `rev` is
reached, at least `p` and `W`'s start revision; (under the compaction condition) no event of `W`
from `p + 1` up to it. -/
def progStep (W : WatcherM) (h : KVHist) (p : Nat) (rev : w64) : Prop :=
  ∃ P : Nat, sint.Z rev = P ∧ p ≤ P ∧ P ≤ h.rev ∧ W.startRev ≤ P ∧
    (exactFrom h (p + 1) → wEvents W h (p + 1) P = [])

/-- **What a response `r` of the watcher `W` says**, at its position `p` and its events position
`pe` (`posEvOf`), against the reached history `h`: a compaction (the revision after `W`'s last
event, `pe + 1`, is below a compaction revision of the store: not `p + 1`, a progress does not
protect a watcher from a compaction); a progress (`progStep`); events: up to the last event's
revision `c'` (above `p`, at most the response's revision, which is reached), and (under the
compaction condition) exactly `W`'s events of the revisions `p + 1 .. c'`. (Margin of the
condition: only the compaction revision itself can lose a key's earlier change in it.) -/
def wStep (W : WatcherM) (h : KVHist) (p pe : Nat) (r : WResp) : Prop :=
  if r.compactRev ≠ W64 0 then
    ∃ cr : Nat, sint.Z r.compactRev = cr ∧ pe + 1 < cr ∧ cr ≤ h.compacted
  else if r.evs = [] then progStep W h p r.rev
  else ∃ c' : Nat, p < c' ∧ (c' : Int) ≤ sint.Z r.rev ∧ sint.Z r.rev ≤ h.rev ∧
    r.evs.getLast?.map (fun e => e.kv.modRevision) = some (W64 c') ∧
    (exactFrom h (p + 1) → r.evs = (wEvents W h (p + 1) c').map (fun x => evOf x.1 x.2))

/-- **`h'` extends `h`**: its revisions continue `h`'s, its compaction revision is not below. -/
def histLe (h h' : KVHist) : Prop := h.revs <+: h'.revs ∧ h.compacted ≤ h'.compacted

/-! ## Resources -/

/-- A watch stream's ghost names (opaque). -/
opaque WsNames : Type := Unit

/-- The stream's channel (fixed at its creation). -/
opaque wsChanOf (ι : WsNames) : GoChan

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

open go_etcd_io.etcd.server.v3.storage.mvcc go_etcd_io.etcd.api.v3

/-- **The store `γ` has notified at least the history `h`** (persistent): `h` is extended by the
store's notified history (`histLe h σ.notified`, `mvccLb_le`). -/
opaque mvccLb (γ : MvccName) (h : KVHist) : IProp GF := iprop(True)

/-- **`kv` is a watchable store of `γ`** (persistent). -/
opaque watchableAt (kv : GoInterface) (γ : MvccName) : IProp GF := iprop(True)

/-- **`w` is a watch stream of `γ`, named `ι`** (persistent). -/
opaque wsAt (w : Loc) (γ : MvccName) (ι : WsNames) : IProp GF := iprop(True)

/-- **The stream's control side**: the stream's next id is `n`; every id registered so far is
below it (exclusive; `wsReg_ctl`). -/
opaque wsCtl (ι : WsNames) (n : Int) : IProp GF := iprop(True)

/-- The right to close the stream (exclusive). -/
opaque wsOpen (ι : WsNames) : IProp GF := iprop(True)

/-- **The consumer has received `rs`**, in order (exclusive). -/
opaque wsCons (ι : WsNames) (rs : List WResp) : IProp GF := iprop(True)

/-- The watcher `id` was registered as `W` (persistent). -/
opaque wsReg (ι : WsNames) (id : w64) (W : WatcherM) : IProp GF := iprop(True)

/-- Every response of the watcher `id` is among the first `c` sent (persistent). -/
opaque wsCanceled (ι : WsNames) (id : w64) (c : Nat) : IProp GF := iprop(True)

/-- The stream was closed (persistent): its watchers cancelled, its channel closed. -/
opaque wsClosed (ι : WsNames) : IProp GF := iprop(True)

/-- The stream has sent at least `n` responses (persistent). -/
opaque wsSentLb (ι : WsNames) (n : Nat) : IProp GF := iprop(True)

/-- **An event message** at `p` (fresh, owned; its `Kv` read-only, shared by the watchers it was
sent to; `PrevKv` `nil`). -/
def evOwn (p : Loc) (e : EvM) : IProp GF :=
  iprop(∃ kv : Loc, protoRest mvccpb.Event p (DFrac.own 1) ∗
    p.[mvccpb.Event, go!"Type"] ↦ (if e.del then W32 1 else W32 0) ∗
    p.[mvccpb.Event, go!"Kv"] ↦ kv ∗ keyValueOwn kv DFrac.discard e.kv ∗
    p.[mvccpb.Event, go!"PrevKv"] ↦ (null : Loc))

/-- **The `WatchResponse` value `v` is the response `r`**: its events slice and events owned. -/
def wrespAt (v : WatchResponse) (r : WResp) : IProp GF :=
  iprop(⌜v.WatchID' = r.id ∧ v.Revision' = r.rev ∧ v.CompactRevision' = r.compactRev⌝ ∗
    ∃ ps : List Loc, v.Events' ↦* ps ∗ [∗list] p; e ∈ ps; r.evs, evOwn p e)

/-- **The filter function `f` computes `d`**: called on an event message (as `watcher.send` does,
owning it), it returns `d` of the event, reading it only. -/
def filterOk (f : GoFunc) (d : EvM → Bool) : IProp GF :=
  iprop(□ ∀ (p : Loc) (e : EvM),
    {{ evOwn p e }} (App (Val #f) (Val #p)) {{ (b : Bool), RET #b; ⌜b = d e⌝ ∗ evOwn p e }})

/-- **The filters slice `fcs`** (read-only: the watcher keeps it) holds functions computing `ds`. -/
def filtersAt (fcs : GoSlice) (ds : List (EvM → Bool)) : IProp GF :=
  iprop(∃ fs : List GoFunc, fcs ↦*□ fs ∗ [∗list] f; d ∈ fs; ds, filterOk f d)

/-- **`err` is an error whose `Error()` returns `msg`**, on every call (persistent). -/
def errMsgOk (err : GoInterface) (msg : GoString) : IProp GF :=
  iprop(⌜err ≠ GoInterface.nil⌝ ∗
    □ {{ True }} (App (Val (err @!! go.error @!! go!"Error")) (Val #())) {{ RET #msg; True }})

/-- **What the response `r`, received after `rs`, says** (persistent facts; see the header). -/
def wsRespOk (γ : MvccName) (ι : WsNames) (rs : List WResp) (r : WResp) : IProp GF :=
  iprop(∃ h : KVHist, mvccLb γ h ∗ ⌜respShape r⌝ ∗
    (□ ∀ c, wsCanceled ι r.id c -∗ ⌜rs.length < c⌝) ∗
    if r.id = W64 (-1) then
      □ ∀ (id : w64) (W : WatcherM), wsReg ι id W -∗ ⌜W.stamp ≤ rs.length⌝ -∗
        (∃ c, wsCanceled ι id c ∗ ⌜c ≤ rs.length⌝) ∨ ⌜progStep W h (posOf W id rs) r.rev⌝
    else ∃ W : WatcherM, wsReg ι r.id W ∗
      ⌜W.stamp ≤ rs.length ∧ wStep W h (posOf W r.id rs) (posEvOf W r.id rs) r ∧
        (r.compactRev = W64 0 → ∀ x ∈ rs, x.id = r.id → x.compactRev = W64 0)⌝)

/-- What a receive on the stream's channel gives: a response with its facts, or (`!ok`) the end of
the closed channel. -/
def wsRecvPost (γ : MvccName) (ι : WsNames) (rs : List WResp) (v : WatchResponse) (ok : Bool) :
    IProp GF :=
  if ok then iprop(∃ r : WResp, wrespAt v r ∗ wsRespOk γ ι rs r ∗ wsCons ι (rs ++ [r]))
  else iprop(wsCons ι rs)

/-! ## Laws -/

def watch_persistent.spec : Prop :=
  (∀ kv γ, Persistent (watchableAt (GF := GF) kv γ)) ∧ (∀ γ h, Persistent (mvccLb (GF := GF) γ h)) ∧
  (∀ w γ ι, Persistent (wsAt (GF := GF) w γ ι)) ∧
  (∀ ι id W, Persistent (wsReg (GF := GF) ι id W)) ∧
  (∀ ι id c, Persistent (wsCanceled (GF := GF) ι id c)) ∧
  (∀ ι n, Persistent (wsSentLb (GF := GF) ι n)) ∧ (∀ ι, Persistent (wsClosed (GF := GF) ι)) ∧
  (∀ ι n, Timeless (wsCtl (GF := GF) ι n)) ∧ (∀ ι rs, Timeless (wsCons (GF := GF) ι rs))

/-- **What a lower bound says** of the store's state (the client's): its notified history extends
`h`. -/
def mvccLb_le.spec : Prop := ∀ γ σ h,
  mvccState (GF := GF) γ σ ∗ mvccLb γ h ⊢ ⌜histLe h σ.notified⌝

/-- **A lower bound of the current state** (the client relates its own state to the facts it will
receive: the watchers' registrations and responses are at or past it). -/
def mvccLb_get.spec : Prop := ∀ γ σ,
  mvccState (GF := GF) γ σ ⊢ |==> mvccState γ σ ∗ mvccLb γ σ.notified

/-- **Registered ids are below the control side's next id** (and not negative): an id the control
side did not get from `Watch` is not registered. -/
def wsReg_ctl.spec : Prop := ∀ ι id W n,
  wsReg (GF := GF) ι id W ∗ wsCtl ι n ⊢ ⌜0 ≤ sint.Z id ∧ sint.Z id < n⌝

/-- One registration per id (the stream's ids are fresh). -/
def wsReg_agree.spec : Prop := ∀ ι id W W',
  wsReg (GF := GF) ι id W ∗ wsReg ι id W' ⊢ ⌜W = W'⌝

def wsCanceled_mono.spec : Prop := ∀ ι id (c c' : Nat), c ≤ c' →
  wsCanceled (GF := GF) ι id c ⊢ wsCanceled ι id c'

def wsSentLb_zero.spec : Prop := ∀ ι, ⊢ wsSentLb (GF := GF) ι 0

def wsSentLb_mono.spec : Prop := ∀ ι (n n' : Nat), n' ≤ n →
  wsSentLb (GF := GF) ι n ⊢ wsSentLb ι n'

/-- A watchable store is a `*watchableStore`. -/
def watchableAt_shape.spec : Prop := ∀ kv γ,
  watchableAt (GF := GF) kv γ ⊢ ∃ s : Loc, ⌜kv = interface.mkOk (go.GoType.PointerType watchableStore.ty) #s⌝

/-- A watchable store is a store (3e's handle: its `KV` methods). -/
def watchableAt_isMvcc.spec : Prop := ∀ kv γ, watchableAt (GF := GF) kv γ ⊢ isMvcc kv γ

/-- **Receiving on the stream's channel**, in Perennial's channel forms: a receive (`recvAu`: alone
or as a `select` case) gives the next response with its facts (`wsRecvPost`), or the end of the
closed channel; a non-blocking receive (`nonblockingRecvAuAlt`: a `select` with a `default`, v3rpc's
drain) gives the same, or the channel empty: every response the stream sent before is received (at
least the `n` of a `wsSentLb ι n` taken before). -/
def wsCons_recv.spec : Prop := ∀ (w : Loc) (γ : MvccName) (ι : WsNames),
  wsAt (GF := GF) w γ ι ⊢
    ∃ (_ : Pos.Countable WatchResponse) (γc : ChanNames),
      isChan (wsChanOf ι) γc WatchResponse ∗
      (□ ∀ (rs : List WResp) (Φ : WatchResponse → Bool → IProp GF),
        wsCons ι rs -∗ £ 1 ∗ £ 1 -∗
        (▷ ∀ (v : WatchResponse) (ok : Bool), wsRecvPost γ ι rs v ok -∗ Φ v ok) -∗
        recvAu γc WatchResponse Φ) ∗
      (□ ∀ (rs : List WResp) (n : Nat) (Φ : WatchResponse → Bool → IProp GF) (Ψ : IProp GF),
        wsCons ι rs -∗ wsSentLb ι n -∗ £ 1 ∗ £ 1 -∗
        ((▷ ∀ (v : WatchResponse) (ok : Bool), wsRecvPost γ ι rs v ok -∗ Φ v ok) ∧
          (wsCons ι rs -∗ ⌜n ≤ rs.length⌝ -∗ Ψ)) -∗
        nonblockingRecvAuAlt γc WatchResponse Φ Ψ)

/-- **The package's watch variables after initialization** (no verified code writes them): the
buffer of a stream's channel, the batch sizes, the resync period, and the three error values with
their messages. -/
def watch_init.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ⊢
    globalAddr chanBufLen ↦□ (W64 128) ∗ globalAddr maxWatchersPerSync ↦□ (W64 512) ∗
    globalAddr watchBatchMaxRevs ↦□ (W64 1000) ∗
    globalAddr watchResyncPeriod ↦□ (W64 100000000) ∗
    ∃ (e1 e2 e3 : GoInterface),
      globalAddr ErrEmptyWatcherRange ↦□ e1 ∗ errMsgOk e1 go!"mvcc: watcher range is empty" ∗
      globalAddr ErrWatcherNotExist ↦□ e2 ∗ errMsgOk e2 go!"mvcc: watcher does not exist" ∗
      globalAddr ErrWatcherDuplicateID ↦□ e3 ∗
      errMsgOk e3 go!"mvcc: duplicate watch ID provided on the WatchStream"

end res

end Mvcc
end EtcdGrove
end Perennial
