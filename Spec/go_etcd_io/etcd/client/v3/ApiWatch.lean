/-
# etcd's Go client: the watch API's vocabulary (batch 1b)

What a program using `clientv3.Watcher` (`client/v3/watch.go`) holds, and the contract its
responses meet, over the cluster's abstract state (`api/v3/State.lean`'s `etcdLb γ σ`, `Model.lean`'s
`KVHist`). It fills W0's slot `watcherAt v γ who` (`client/v3/Api.lean`) with the bundle of the
`Watcher` interface's three triples (`Watcher.*Triple`), realized for `*watcher` by
`watcherHandle_watcherAt`.

## A watch is a sequence of facts about the history, not a linearized read

The model keeps the whole KV history (`KVHist.revs`, `compacted` only the floor below which reads
fail), so **every response of a watch is a persistent fact about the history at a state the
cluster has reached** (`etcdLb γ σ`): its events are exactly the events of the watched range of
the revisions it covers, in order, with nothing skipped and nothing repeated; a progress
notification at `P` says that the range had no event since the last response up to `P`; a
compaction error says the next revision the watch needs is below a compaction the cluster made.
No atomic update is fired: a watch reports the past, and a client that keeps `etcdState` in an
invariant relates a response to the current state by `etcdLb_reach` (the history only grows: a
pure lemma of the model, `Reach σ σ' → σ.kv.revs <+: σ'.kv.revs`, that clients prove). Decision
(1b): this replaces the old spec's persistent read update fired once per response (D47), which
predates `etcdLb`; the update carried no information a past fact does not, and its `Q` threaded
through every response.

The facts are stated by **`watchStep who w σ σa p m p'`** (pure): the response `m` received at the
watch position `p` leaves it at `p'`, read against the reached states `σ` (the history) and `σa`
(an auth state that admitted the watch). The **position** `WatchPos` records how far the watch is
known complete (`done`: every event of the range up to that revision has been delivered; `none`
for a watch from the current revision before its first event), its **floor** (a watch from the
current revision: every event above it is delivered), whether a response arrived (`started`: a
`Created` response comes first or never) and whether the watch ended (`ended`: after an error
response only `closeErr` responses, then the channel closes).

The positions start at `WatchPos.init rev r0` (`Watch`'s post): a watch from `rev > 0` is complete
up to `rev - 1` (its events start at `rev`: the fork's fix of
`issues/etcd-watch-resume-below-start-revision.md` keeps a resumed watch at or above it); a watch
from the current revision (`rev = 0`) has an unknown position and the floor `r0`, a revision the
cluster had reached when `Watch` returned (`Watch` returns only once the member's `Created`
response, at header `H ≤ r0`, has set the resume revision to `H`): its first event is at most
`r0 + 1`, and from there on it is complete. Not "complete from the member's revision at
creation": after a reconnect before any event the client resumes from `H`, not `H + 1`
(`serveSubstream`: `nextRev = wr.Header.Revision`), so it may deliver revision `H`'s events, which
precede the watch (`issues/etcd-watch-current-resume-past-event.md`); a revision between the
member's registration and its header read may be skipped then; and a progress notification
computed in that window is below `H`, so a progress does not fix an unknown position.

A watch's channel may also end at once (`WatchPos.closed`: a closed watcher, a done context, a
stream that ended before the watch was registered), with at most one error response.

**The compaction condition** (`exactFrom`, an abbreviation of W0's `EtcdModel.exactFrom`): the
events and progress facts are exact only when no revision from the watch's next one up to the
compaction revision changes a key twice (a compaction keeps a key's last change of such a revision
only); vacuous on a cluster that never compacts below the watch. Stated once, in `Model.lean`;
2b's `srvWireStep` and 3f's `wStep` cite it.

## Vocabulary

Pure (transparent):
* `WatchReq` (`api/v3/Wire.lean`, with the other watch messages): what a watch delivers (its
  range, normalized as the member does: an empty key is `"\x00"`; `prevKV`; the filters; the
  notification flags). `OpM.watchReq`, `OpM.watchRev`.
* `WEv` (a history event as a watch delivers it: revision, delete or put, the key-value),
  `watchEvents w h lo hi` (the range's events of revisions `lo..hi`, in order, filtered),
  `WatchReq.prevOk` (the previous key-value: the key's record at the revision before, absent only
  for a creation, below the compaction (`nonissues/etcd-watch-prevkv-nil-after-compaction.md`), or
  in a registration's first responses (the member's `prevKV` window, 2b's finding): a client's
  channel stays in that window (`WatchPos.prevLoose`), since every reconnect reopens it: a
  non-`nil` `PrevKv` is the previous record, a `nil` one says nothing).
* `EventM` (an `mvccpb.Event`, `Wire.lean`), `WatchRespM` (a `clientv3.WatchResponse`: its
  exported fields, and the kind of its private `closeErr`), `WatchPos`, `watchStep`.
* The wire protocol of one gRPC watch stream (**the contract with 2a/2b**): `WireWatchReq` (a
  create, a cancel, a progress request), `WireWatchRespM` (a `pb.WatchResponse`; both in
  `Wire.lean`), `WireSt` (the stream's registrations as its responses made them) and `wireStep`:
  a `Created` answers the oldest unanswered create, a response of a registration's id is a `watchStep` of it, the id `-1`
  a progress of every registration, fragments reassemble to one response.

Resources:
* `watcherHandle w c γ who` (persistent): a `*watcher` of the cluster `γ` as `who`
  (`NewWatchFromWatchClient`'s), whose stub works once the client `c` is ready (`clientReady c`,
  1c's readiness; `null` for a caller's stub): `watcherHandle_watcherAt` takes `clientReady c`, as
  `lessorHandle_leaseAt` and `kvHandle_kvAt` do (verify-round W3). Intended realization: its
  read-only fields (`remote` with `□ (clientReady c -∗ remoteWatchAt remote γ who)`, `callOpts`,
  the logger), and its lock `mu` over `streams` (`nil` once closed, else a map from stream keys to
  `*watchGRPCStream`s: the key `k` to a stream `wgsAt s w γ p` opened with a context `ctx₀`, with
  `ctxStreamKey ctx₀ k ∗ ctxPrin who ctx₀ p` kept, so that a context of the same key is
  authenticated as `p` too, `ctxStreamKey_prin`; `WatchInternal.lean`).
* `ctxStreamKey ctx k` (persistent): `k` is `streamKeyFromCtx(ctx)` (the printed outgoing
  metadata). Law: `ctxStreamKey_prin` (equal keys, equal principals, verify-round W2).
* `watchChAt ch γ who w p` (exclusive): **the consumer of a watch's channel** `ch` at the position
  `p`. Laws: `watchChAt_recv` (a receive, alone or in a `for range`), `watchChAt_recvAu` (a
  receive as a `select` case). Intended realization: the consumer half of the channel's protocol
  (Perennial's SPSC idiom over `outc`, whose producers are, in turn, the substream's goroutine,
  `sendCloseSubstream`, `closeSubstream` and `Watch`'s closed channel), each element a response
  with its `watchStep` facts at the position of its index (a monotone list of positions).
* `watchRespAt v m` (exclusive): the `WatchResponse` value `v` is modelled by `m`: its header (owned
  in full when the response has events; read-only otherwise: a progress notification's header is
  shared by every substream it was broadcast to), its events owned in full (Kubernetes' etcd3
  watcher and the namespace wrapper rewrite them; `concurrency.Election.Observe` writes the
  header's revision). Laws: `watchRespAt_fields`; `watchRespAt_persist` (to the read-only
  `watchRespRO`, persistent), `eventOwn_persist`.
* `eventOwn p dq e`: an `mvccpb.Event` message (`eventOwn_unfold`, `eventOwn_persist`; with W0's
  `keyValueOwn`), in `api/v3/Wire.lean` (W0's, realized by 3h): 2b builds these.
* `closeErrOk e k` (persistent): `e` is `nil` (`k = none`) or an error that `rpctypes.Error` maps
  to one of kind `k` (`CallErr`); `closeErrOk_nil`.
* **Slots of the gRPC boundary (2a, with 2b's handler and 3h's stub)**: `remoteWatchAt v γ who`
  (a `pb.WatchClient` whose `Watch` opens a stream, `remoteWatchAt_watch`), the stream's halves
  `wireWatchSend wc γ who g ss` (the sends so far, `wireWatchSend_send`) and `wireWatchRecv wc γ who
  g st` (the stream's state, `wireWatchRecv_recv`), `wireWatchSentLb g ss` (persistent: at least
  `ss` was sent); the messages `watchReqOwn p dq r` (a `pb.WatchRequest`), `wireWatchRespOwn p dq m`
  (a `pb.WatchResponse`) are in `api/v3/Wire.lean`. `WatchStreamNames`: grpc's stream name.
  Integration X: the stream's contract `watchSpec γ` (2a's) is stated here over its records `wsReq`,
  `wsLog`, `wsSt`, `wsWho` (laws `watchSpec_records`, `wsLog_alloc`, `wsLog_add`, `wsLog_lb`), and
  `wireWatchSentLb g ss` is a definition over `wsReq`; the halves stay 2a's slots (their realization
  goes through 3h's stub wrapper).

## Requirement snippets

`examples/specreq/clientv3watch/`: `history.go` (no gap from the start revision, revision order,
values; all events of a revision in one response; filters), `progress.go` (progress notifications
monotone and meaning "nothing missed"; `RequestProgress`), `ending.go` (compaction, errors end the
watch, `Created` first, a refused watch delivers nothing, `Close`), `consume.go` (a `select` with
the context, writing the response as `Election.Observe` and the namespace wrapper do, the
previous key-value Kubernetes reads, watches sharing one stream by their contexts' metadata).

## Changes (verify-round, 2026-11-09)

* W1: `WireSt.frag` keeps the first fragment, and the later fragments agree with its header,
  compaction revision and cancel reason (`run` dispatches the first fragment with every
  fragment's events).
* W2: `ctxStreamKey` and `ctxStreamKey_prin` (equal stream keys, equal principals), which
  `streamKeyFromCtx.spec` now gives and `watcher.Watch` needs to join a stream another context
  opened.
* W3: `watcherHandle w c γ who` records the client whose readiness its stub needs;
  `watcherHandle_watcherAt` takes `clientReady c`.
* W4: `watchStep`'s ended case says `m.created = false`.
* S2 (and A3's request): `watchStep`'s event case says, unconditionally, that each event is an
  event of the history the watch keeps (its key in the range, the filters); only exactness is
  gated on `exactFrom`.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Api
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Api
public import Spec.google_golang_org.grpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

/-! ## What a watch delivers -/

/-- The watch an `Op` built by `OpWatch` asks for (`watcher.Watch`: `string(ow.key)`,
`string(ow.end)`; a `nil` end is the single key). Unlike a range's `OpM.endReq` (W0), a non-`nil`
empty end (`WithRange("")`) is the single key too: the watch sends it as a string, and the member's
`recvLoop` reads an empty `RangeEnd` as `nil`; `WithFromKey`'s `"\x00"` is every key from the key
on (`recvLoop`'s `[]byte{}`, `KeyRange.mem`'s `"\x00"`). -/
def OpM.watchReq (o : OpM) : WatchReq :=
  { range := { key := if o.key = [] then [W8 0] else o.key, rangeEnd := o.rangeEnd.getD [] },
    prevKV := o.prevKV, filterPut := o.filterPut, filterDelete := o.filterDelete,
    progressNotify := o.progressNotify, createdNotify := o.createdNotify, fragment := o.fragment }

/-- Its start revision (`WithRev`; `0`: the member's current one; a negative one is refused with
`ErrCompacted`). -/
def OpM.watchRev (o : OpM) : Int := sint.Z o.rev

/-- **A history event as a watch delivers it**: its revision, whether a delete, and the key-value
it carries (a put's the record it wrote; a delete's the key and `ModRevision` alone,
`mvcc.watchableStoreTxnWrite.End`). -/
structure WEv where
  rev : Nat
  del : Bool
  kv : KeyValueM

def WEv.ofEvent (r : Nat) : Event → WEv
  | .put k kr => { rev := r, del := false, kv := KeyValueM.ofKV (KV.ofRec k kr) }
  | .delete k => { rev := r, del := true,
                   kv := { key := k, createRevision := W64 0, modRevision := W64 r,
                           version := W64 0, value := [], lease := W64 0 } }

/-- The watch keeps the event: its key in the range, not filtered out. -/
def _root_.Perennial.EtcdGrove.EtcdWire.WatchReq.keeps (w : WatchReq) (e : WEv) : Prop :=
  w.range.mem e.kv.key ∧ ¬ (e.del = true ∧ w.filterDelete = true) ∧
    ¬ (e.del = false ∧ w.filterPut = true)

/-- **The events the watch `w` delivers of the revisions `lo..hi`** of the history `h`, in order
(revision order, and each revision's events in their order). -/
def watchEvents (w : WatchReq) (h : KVHist) (lo hi : Nat) : List WEv :=
  ((List.range' lo (hi + 1 - lo)).flatMap (fun r => (h.eventsAt r).map (WEv.ofEvent r))).filter
    (fun e => decide (w.keeps e))

/-- **An event's previous key-value** (`WithPrevKV`; `v3rpc/watch.go`'s range at `ModRevision - 1`):
the key's record at the revision before, or none when there is none, the event is a creation
(`IsCreateEvent`: not looked up), that revision is below the compaction, or the watch is still in
its registration's window (`loose`: the member's `sendLoop` reads `prevKV[id]` before `recvLoop`
sets it, `v3rpc/watch.go:443-445` against `:342-349`, so the responses it built for a new
registration before then carry no `PrevKv`). Without `prevKV`, none. -/
def _root_.Perennial.EtcdGrove.EtcdWire.WatchReq.prevOk (w : WatchReq) (h : KVHist) (loose : Bool) (e : WEv) (pk : Option KeyValueM) :
    Prop :=
  if w.prevKV then
    pk = (h.storeAt (e.rev - 1) e.kv.key).map (fun r => KeyValueM.ofKV (KV.ofRec e.kv.key r)) ∨
    (pk = none ∧ (loose = true ∨ e.kv.createRevision = e.kv.modRevision ∨ e.rev - 1 < h.compacted))
  else pk = none

/-- **The compaction condition**: `EtcdModel.exactFrom` (`Model.lean`, the one statement of it
that 1b, 2b and 3f cite); this name is kept for the client's statements. -/
abbrev exactFrom (h : KVHist) (lo : Nat) : Prop := EtcdModel.exactFrom h lo

/-- The delivered event `m` is the history's event `e`. -/
def _root_.Perennial.EtcdGrove.EtcdWire.EventM.isOf (w : WatchReq) (h : KVHist) (loose : Bool) (m : EventM) (e : WEv) : Prop :=
  m.del = e.del ∧ m.kv = e.kv ∧ w.prevOk h loose e m.prevKv

/-- **A `clientv3.WatchResponse`**: its exported fields (the header always set on a response of a
watch's channel), and the kind of its private `closeErr` (`none`: `nil`), which `Err()` reports. -/
structure WatchRespM where
  hdr : HeaderM
  events : List EventM
  compactRev : w64
  canceled : Bool
  created : Bool
  cancelReason : GoString
  closeErr : Option CallErr

/-- `Err() != nil` for a response of a watch's channel. -/
def WatchRespM.isErr (m : WatchRespM) : Prop := m.closeErr ≠ none ∨ m.compactRev ≠ W64 0

/-- `IsProgressNotify()`. -/
def WatchRespM.isProgressNotify (m : WatchRespM) : Bool :=
  decide (m.events = [] ∧ m.canceled = false ∧ m.created = false ∧ m.compactRev = W64 0 ∧
    m.hdr.revision ≠ W64 0)

/-- **A watch's position**: `done`, the revision up to which every event of the watch has been
delivered (`none`: not yet known, a watch from the current revision); `started`, a response was
received; `ended`, an error response was received. -/
structure WatchPos where
  done : Option Nat
  floor : Option Nat
  started : Bool
  ended : Bool
  /-- `PrevKv` may still be missing (`WatchReq.prevOk`'s window): true at a registration, false
  once the member's responses carry it, for good; a client's channel keeps it (a reconnect
  re-registers the watch, which reopens the window) -/
  prevLoose : Bool
  /-- the revision up to which the watch is known complete by its **events** alone (the last
  event's revision, or the start's - 1; `none` for a watch from the current revision before its
  first event): a progress notification never raises it, as it never raises the member's
  `minRev`, which a compaction is compared against (`watcher_group.go:255`; a `Restore` keeps
  `minRev`, `watchable_store.go:215-219`) -/
  evDone : Option Nat

/-- A new watch from the revision `rev`; `r0` a revision the cluster had reached when `Watch`
returned (the floor of a watch from the current revision: every event above it is delivered). -/
def WatchPos.init (rev : Int) (r0 : Nat) : WatchPos :=
  { done := if 0 < rev then some (rev.toNat - 1) else none,
    floor := if 0 < rev then none else some r0, started := false, ended := false,
    prevLoose := true, evDone := if 0 < rev then some (rev.toNat - 1) else none }

/-- A watch whose channel delivers at most one error response, then closes (`Watch` on a closed
watcher, a done context, a stream that ended). -/
def WatchPos.closed (rev : Int) : WatchPos :=
  { WatchPos.init rev 0 with ended := true }

/-- **What a response of the watch `w` says**, received at the position `p` and leaving it at `p'`,
read against the reached states `σ` (the history) and `σa` (an auth state that admitted the watch
of the principal `who`: the member's applied one when it registered the watch, so any state the
cluster reached, a lagging member's included):

* every response's header revision has been reached; the floor never changes;
* after an error, only `closeErr` responses (header `0`, no compaction, no events, not `Created`:
  every `closeErr` response is `WatchResponse{Header: &pb.ResponseHeader{}, Canceled: true,
  closeErr: …}`, `watch.go:366,381,500`);
* an **error** (`Err() != nil`) ends the watch; a `closeErr` one has header `0` and no compaction;
  a compaction (`CompactRevision` set, then no `closeErr`) says the revision after the watch's last
  event (or its start) is below a compaction of the cluster (not the one after a progress
  notification: after a member restores a snapshot, a watch told "nothing up to `P`" may be
  canceled at a compaction revision at most `P`);
* a **`Created`** response only first, and only with `WithCreatedNotify`;
* a response **with events**: its last event's revision reached and past `p`'s; each event, whatever
  the compaction did, an event of the history that the watch keeps (its key in the range, not
  filtered out: the namespace wrapper's `Key[len(pfx):]`, the recipes' prefix keys; mvcc reads only
  records of real revisions and filters by the range, `kvsToEvents`; a compaction affects only
  exactness, decision A17); and, under the
  compaction condition (`exactFrom` from the first revision it covers), exactly the watch's events
  of the revisions from just after `p`'s (if `p`'s is unknown: from some revision at most the
  floor's + 1) to the last event's; the principal was permitted to read the range;
* a **progress notification** (no events, a header revision `P`): `P` is not below `p`'s revision,
  and (under the compaction condition) nothing of the watch's since `p`'s revision up to `P` (a watch whose position is still unknown learns
  nothing from it: after a reconnect such a watch resumes from its creation's header revision,
  which a progress computed before that header may be below);
* any other response (no events, header revision `0`): nothing. -/
def watchStep (who : Principal) (w : WatchReq) (σ σa : State) (p : WatchPos) (m : WatchRespM)
    (p' : WatchPos) : Prop :=
  sint.Z m.hdr.revision ≤ (σ.kv.rev : Int) ∧ p'.started = true ∧ p'.floor = p.floor ∧
  (p'.prevLoose = true → p.prevLoose = true) ∧
  p'.evDone = (if m.events = [] then p.evDone else p'.done) ∧
  if p.ended = true then
    m.closeErr ≠ none ∧ m.compactRev = W64 0 ∧ m.hdr.revision = W64 0 ∧ m.events = [] ∧
    m.canceled = true ∧ m.created = false ∧ p'.done = p.done ∧ p'.ended = true
  else if m.isErr then
    m.events = [] ∧ m.canceled = true ∧ m.created = false ∧ p'.done = p.done ∧ p'.ended = true ∧
    (m.closeErr ≠ none → m.compactRev = W64 0 ∧ m.hdr.revision = W64 0) ∧
    (m.compactRev ≠ W64 0 → m.closeErr = none ∧ ∃ cr : Nat, sint.Z m.compactRev = cr ∧
      cr ≤ σ.kv.compacted ∧ ∀ c, p.evDone = some c → c + 1 < cr)
  else if m.created = true then
    p.started = false ∧ w.createdNotify = true ∧ m.events = [] ∧ m.canceled = false ∧
    p'.done = p.done ∧ p'.ended = false
  else if m.events = [] then
    m.canceled = false ∧ p'.ended = false ∧
    (if m.hdr.revision = W64 0 then p'.done = p.done
     else ∃ P : Nat, sint.Z m.hdr.revision = P ∧
       (∀ c, p.done = some c → c ≤ P ∧
         (exactFrom σ.kv (c + 1) → watchEvents w σ.kv (c + 1) P = [])) ∧
       p'.done = p.done.map (fun _ => P))
  else
    m.canceled = false ∧ p'.ended = false ∧ σa.permits who [(.read, w.range)] [] ∧
    (∀ e ∈ m.events, ∃ (r : Nat) (ev : Event), ev ∈ σ.kv.eventsAt r ∧ e.kv.modRevision = W64 r ∧
      (WEv.ofEvent r ev).del = e.del ∧ (WEv.ofEvent r ev).kv = e.kv ∧ w.keeps (WEv.ofEvent r ev)) ∧
    ∃ lo c' : Nat, (∀ c, p.done = some c → lo = c + 1) ∧
      (∀ f, p.done = none → p.floor = some f → lo ≤ f + 1) ∧ lo ≤ c' ∧
      (c' : Int) ≤ sint.Z m.hdr.revision ∧
      (exactFrom σ.kv lo →
        List.Forall₂ (EventM.isOf w σ.kv p.prevLoose) m.events (watchEvents w σ.kv lo c')) ∧
      m.events.getLast?.map (fun e => e.kv.modRevision) = some (W64 c') ∧ p'.done = some c'

/-! ## The wire protocol of a gRPC watch stream (the contract with 2a and 2b) -/

/-- The client-level response a wire response (with its reassembled events `evs`) is, as
`dispatchEvent` builds it. -/
def _root_.Perennial.EtcdGrove.EtcdWire.WireWatchRespM.toResp (m : WireWatchRespM) (evs : List EventM) : WatchRespM :=
  { hdr := m.hdr.getD HeaderM.zero, events := evs, compactRev := m.compactRev,
    canceled := m.canceled, created := m.created, cancelReason := m.cancelReason,
    closeErr := none }

/-- **A stream's state** as its responses so far made it: how many creates were answered, the live
registrations (id, watch, position), the first fragment and the events of fragments not yet
completed (`run` keeps the first fragment as `cur` and appends the later ones' events to it,
`watch.go:596-603`: the dispatched response is the first's with every fragment's events). -/
structure WireSt where
  answered : Nat
  regs : List (Int × WatchReq × WatchPos)
  frag : Option (WireWatchRespM × List EventM)
  /-- the ids announced by a `Created` (mvcc's ids only grow: never announced twice) -/
  seen : List Int
  /-- the ids whose cancel response was sent: nothing more is sent for them -/
  retired : List Int

def WireSt.init : WireSt := { answered := 0, regs := [], frag := none, seen := [], retired := [] }

/-- The registration of an id. -/
def WireSt.reg (st : WireSt) (id : Int) : Option (WatchReq × WatchPos) :=
  (st.regs.find? (fun r => decide (r.1 = id))).map (·.2)

/-- The registrations with the one of `id` at `p` (removed if `p` ended). -/
def WireSt.setReg (st : WireSt) (id : Int) (p : WatchPos) : List (Int × WatchReq × WatchPos) :=
  (st.regs.map (fun r => if r.1 = id then (r.1, r.2.1, p) else r)).filter
    (fun r => decide (r.1 ≠ id ∨ p.ended = false))

/-- **What the member's response `m` on a stream may be**, after the requests `ss` (a prefix of
what was sent, containing every request the member read before answering) and the responses that
made the state `st`; `st'` the state after it. `σ`, `σa` reached states as in `watchStep`.

* every response has a header;
* a fragment (`Fragment` set) carries part of a response's events (at least one), for a registered
  watch with `Fragment` set: the next responses up to the first without `Fragment` are of the same
  id, with the same header, compaction revision and cancel reason as the first (`WireSt.frag` keeps
  the first; `sendFragments` copies them into every fragment, `v3rpc/watch.go:634-643`), none a
  creation or a cancel, and together they are one response;
* ids: a registration's id was never announced before (`WireSt.seen`); every other response of an
  id is of an announced one, never of one whose cancel response was sent (`WireSt.retired`);
* `Created` answers the oldest unanswered create: refused (`Canceled`, with a reason: an auth
  check, a negative start revision (always refused), an empty range), or registered (a start
  revision not negative) under a fresh id, the principal
  permitted to read the range, at the position the start revision gives (from `0`: the floor is the
  creation's header revision: every event above it is sent);
* `Canceled` without compaction ends the id's registration (a cancel's answer);
* the id `-1` (no events, not created, canceled or compacted): a progress notification for every
  registration whose cancel the member has not read (each `watchStep`'s progress case at the same
  header; a registration with a cancel in `ss` keeps its position: the member dropped it from mvcc
  before computing the progress, and its cancel response may come later; the client never
  delivers the progress to it, having removed its substream before sending the cancel);
* an id with a registration: a `watchStep` of it (events, progress, compaction);
* an id with none (canceled, or a stale one): nothing. -/
def wireStep (who : Principal) (σ σa : State) (ss : List WireWatchReq) (st : WireSt)
    (m : WireWatchRespM) (st' : WireSt) : Prop :=
  let evs := (st.frag.map (·.2)).getD [] ++ m.events
  -- every response has a header
  m.hdr ≠ none ∧
  -- a pending fragment: the next response is of its id, with its header, compaction revision and
  -- cancel reason, neither a creation nor a cancel
  (∀ f fe, st.frag = some (f, fe) → m.watchId = f.watchId ∧ m.hdr = f.hdr ∧
    m.compactRev = f.compactRev ∧ m.cancelReason = f.cancelReason ∧ m.created = false ∧
    m.canceled = false) ∧
  if m.fragment = true then
    m.created = false ∧ m.canceled = false ∧ m.events ≠ [] ∧
    (∃ w p, st.reg m.watchId = some (w, p) ∧ w.fragment = true) ∧
    st' = { st with frag := some ((st.frag.map (·.1)).getD m, evs) }
  else if m.created = true then
    ∃ w s, (WireWatchReq.creates ss)[st.answered]? = some (w, s) ∧ evs = [] ∧
      sint.Z (m.hdr.getD HeaderM.zero).revision ≤ (σ.kv.rev : Int) ∧
      (s < 0 → m.canceled = true) ∧
      (if m.canceled = true then
         m.watchId = -1 ∧ m.cancelReason ≠ [] ∧
         st' = { st with answered := st.answered + 1, frag := none }
       else 0 ≤ s ∧ σa.permits who [(.read, w.range)] [] ∧ m.watchId ∉ st.seen ∧ m.watchId ≠ -1 ∧
         st' = { answered := st.answered + 1,
                 regs := st.regs ++ [(m.watchId, w,
                   WatchPos.init s (sint.Z (m.hdr.getD HeaderM.zero).revision).toNat)],
                 frag := none, seen := st.seen ++ [m.watchId], retired := st.retired })
  else if m.canceled = true ∧ m.compactRev = W64 0 then
    evs = [] ∧ m.watchId ∈ st.seen ∧ m.watchId ∉ st.retired ∧
    st' = { st with regs := st.regs.filter (fun r => decide (r.1 ≠ m.watchId)), frag := none,
                    retired := st.retired ++ [m.watchId] }
  else if m.watchId = -1 then
    evs = [] ∧ m.canceled = false ∧ m.compactRev = W64 0 ∧
    ∃ P : Nat, sint.Z (m.hdr.getD HeaderM.zero).revision = P ∧ (P : Int) ≤ σ.kv.rev ∧
      (∀ r ∈ st.regs, WireWatchReq.cancel r.1 ∉ ss →
        ∀ c, r.2.2.done = some c → c ≤ P ∧
          (exactFrom σ.kv (c + 1) → watchEvents r.2.1 σ.kv (c + 1) P = [])) ∧
      st' = { st with
        regs := st.regs.map (fun r => if WireWatchReq.cancel r.1 ∈ ss then r
          else (r.1, r.2.1, { r.2.2 with done := r.2.2.done.map (fun _ => P) })),
        frag := none }
  else
    m.watchId ∈ st.seen ∧ m.watchId ∉ st.retired ∧
    match st.reg m.watchId with
    | none => st' = { st with frag := none }
    | some (w, p) => ∃ p', watchStep who w σ σa p (m.toResp evs) p' ∧
        st' = { st with regs := st.setReg m.watchId p', frag := none }

/-! ## Resources -/

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **A `*watcher`** of the cluster `γ` as `who` (persistent), whose stub works once the client `c`
is ready (`clientReady c`; `null`: a caller's stub, which needs no readiness). -/
opaque watcherHandle [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (w c : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)

/-- **`k` is a stream key of the context `ctx`** (persistent): what `streamKeyFromCtx(ctx)`
returns, Go's `fmt.Sprintf("%+v", md)` of the context's gRPC outgoing metadata `md`, or `""` without
any. Intended realization: `∃ md, Grpc.outMD ctx md ∗ ⌜(k = "" ∧ md = []) ∨ k = streamKeyOf md⌝`
(the disjunction because grpc's `FromOutgoingContext.spec` does not say whether an empty map was
attached), with `streamKeyOf` the printing function of `fmt`'s trust-boundary spec of `%+v` on a
`map[string][]string`. Not stated functional (no law needs it: a stream's `ctxKey` that differed
from its map key would only make `closeStream` forget another entry, a liveness matter). -/
opaque ctxStreamKey [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ctx : GoInterface) (k : GoString) : IProp GF := iprop(True)

/-- **The consumer of a watch's channel** `ch` (exclusive): the watch `w` of the principal `who`,
at the position `p`. -/
opaque watchChAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ch : Loc) (γ : Cluster) (who : Principal) (w : WatchReq) (p : WatchPos) :
  IProp GF := iprop(True)

/-- **The `WatchResponse` value `v` is modelled by `m`** (exclusive: see the header). -/
opaque watchRespAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (v : go_etcd_io.etcd.client.v3.WatchResponse) (m : WatchRespM) : IProp GF :=
  iprop(True)

/-- **`e` is a watch response's `closeErr`** of kind `k` (persistent): `nil` (`none`), or an error
`rpctypes.Error` maps to one of kind `k`. -/
opaque closeErrOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (e : GoInterface) (k : Option CallErr) : IProp GF := iprop(True)

/-- Ghost names of one gRPC watch stream: grpc's stream name (integration X), which 2a's records
(`wsReq`, `wsSt`, `wsWho`) are keyed by. -/
abbrev WatchStreamNames : Type := Grpc.StreamName

/-! ### The watch stream's contract (2a's `watchSpec`, here so that the client's names are defined
over its records: integration X; `v3rpc/Api.lean` uses it from here) -/

/-- **The `i`-th request of the watch stream `g` is `r`** (persistent, agreeing; minted by the
client's sending half from `wsLog`). -/
opaque wsReq [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (g : Grpc.StreamName) (i : Nat) (r : WireWatchReq) : IProp GF := iprop(True)

/-- **The requests sent on the watch stream `g` so far** (exclusive; the client's sending half holds
it: the realization of `wireWatchSend`). -/
opaque wsLog [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (g : Grpc.StreamName) (ss : List WireWatchReq) : IProp GF := iprop(True)

/-- **After `j` responses the client's state of the watch stream `g` is `sst`** (persistent,
agreeing; `wsSt g 0 WireSt.init`; minted by the server's sending half, 2b's `srvWatchSend`). -/
opaque wsSt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (g : Grpc.StreamName) (j : Nat) (sst : WireSt) : IProp GF := iprop(True)

/-- **The watch stream `g` was opened as the principal `who`** (persistent, agreeing; minted by the
client from `streamKey g`). -/
opaque wsWho [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (g : Grpc.StreamName) (who : Principal) : IProp GF := iprop(True)

/-- **The `Watch` stream's contract** (2a's; 2b's handler, 1b's client): each request a wire request,
recorded; each response a `wireStep` of the stream's principal from the state the earlier responses
made, after requests that were sent, against reached states; nothing at the end. -/
def watchSpec (γ : Cluster) : Grpc.StreamSpec (GF := GF) where
  up := fun g _ i c => iprop(∃ r : WireWatchReq, ⌜EtcdServerPb.watchReqHolds c r⌝ ∗ wsReq g i r)
  dn := fun g _ j c => iprop(∃ (who : Principal) (m : WireWatchRespM) (σ σa : State)
      (rs : List WireWatchReq) (sst sst' : WireSt),
    ⌜EtcdServerPb.watchRespHolds c m ∧ wireStep who σ σa rs sst m sst'⌝ ∗ wsWho g who ∗
    etcdLb γ σ ∗ etcdLb γ σa ∗ ([∗list] i ↦ r ∈ rs, wsReq g i r) ∗ wsSt g j sst ∗ wsSt g (j + 1) sst')
  fin := fun _ _ _ _ => iprop(True)

/-- **Slot (2a)**: the `pb.WatchClient` value `v` opens watch streams to members of `γ` as `who`. -/
opaque remoteWatchAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (v : GoInterface) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)

/-- **Slot (2a)**: the sending half of the watch stream `wc` (exclusive), the requests `ss` sent.
Intended realization: grpc's sending half of a `watchSpec γ` stream `g` under the stub's wrapper,
with `wsLog g ss` and `wsWho g who`. -/
opaque wireWatchSend [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (wc : GoInterface) (γ : Cluster) (who : Principal) (g : WatchStreamNames)
  (ss : List WireWatchReq) : IProp GF := iprop(True)

/-- **Slot (2a)**: the receiving half of the watch stream `wc` (exclusive), at the state `st`.
Intended realization: grpc's receiving half of a `watchSpec γ` stream `g` under the stub's wrapper,
`n` received, with `wsSt g n st` and `wsWho g who`. -/
opaque wireWatchRecv [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (wc : GoInterface) (γ : Cluster) (who : Principal) (g : WatchStreamNames)
  (st : WireSt) : IProp GF := iprop(True)

/-- **At least the requests `ss` were sent on the stream `g`** (persistent; integration X: 2a's
records). -/
def wireWatchSentLb (g : WatchStreamNames) (ss : List WireWatchReq) : IProp GF :=
  iprop([∗list] i ↦ r ∈ ss, wsReq g i r)

/-- The fraction a response's header is owned at: in full with events (unicast), read-only
without (a broadcast progress notification shares its header). -/
def WatchRespM.hdrDq (m : WatchRespM) : DFrac :=
  if m.events = [] then DFrac.discard else DFrac.own 1

/-! ## The `Watcher` contract (`Watcher.*Triple`), filling W0's `watcherAt` -/

/-- **`Watch(ctx, key, opts...)`**: the watch `OpWatch(key, opts...)` builds, from its start
revision; its channel (never `nil`), and the channel's consumer (`watchChAt`) at the initial
position, whose floor (a watch from the current revision) is the revision of a state the cluster
reached before the return; or a channel that ends at once. Any context: when it is done, the channel closes
(liveness, not stated). The options are given back. `OpWatch` must not panic (`watchPanics`: no
lease, no range-only option). `ctxPrin who ctx p` (W0): the member authenticates a request with
`ctx` as `p` (the client's `who` without token metadata); the watch stream this watch joins was
opened with a context of the same stream key (`streamKeyFromCtx`, `ctxStreamKey`), which
`ctxStreamKey_prin` makes authenticated as `p` too, so the member checks the create as `p`'s, and
the consumer's facts are `p`'s. (Two contexts whose metadata print alike share a stream,
`nonissues/etcd-watch-stream-key-collision.md`: not with tokens, which hold no spaces.) -/
def Watcher.WatchTriple (f : val) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (key : GoString) (opts : GoSlice) (gs : List (OpM → OpM)),
  {{ P ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗ optsAt opts gs ∗ ⌜¬ (opWatchM key gs).watchPanics⌝ }}
    (App (App (App (Val f) (Val #ctx)) (Val #key)) (Val #opts))
  {{ (ch : Loc), RET #ch; ⌜ch ≠ null⌝ ∗ optsAt opts gs ∗
      ((∃ σ0 : State, etcdLb γ σ0 ∗
          watchChAt ch γ p (opWatchM key gs).watchReq
            (WatchPos.init (opWatchM key gs).watchRev σ0.kv.rev)) ∨
       watchChAt ch γ p (opWatchM key gs).watchReq (WatchPos.closed (opWatchM key gs).watchRev)) }}

/-- **`RequestProgress(ctx)`**: asks the member of the stream `ctx`'s metadata names for a progress
notification on every watch of that stream (what such a notification means is `watchStep`'s; that
one comes is liveness). The error (`nil`, the context's, the stream's, "no stream found") is not
modelled. -/
def Watcher.RequestProgressTriple (f : val) (P : IProp GF) (who : Principal) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal),
  {{ P ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p }}
    (App (Val f) (Val #ctx))
  {{ (err : GoInterface), RET #err; True }}

/-- **`Close()`**: cancels every watch (their channels close: liveness); later `Watch` calls return
a closed channel. Any number of times, concurrently. The error is not modelled (`Client.Close`
drops it). -/
def Watcher.CloseTriple (f : val) (P : IProp GF) : Prop :=
  {{ P }}
    (App (Val f) (Val #()))
  {{ (err : GoInterface), RET #err; True }}

/-! ## Laws -/

def watch_persistent.spec : Prop :=
  (∀ w c γ who, Persistent (watcherHandle (GF := GF) w c γ who)) ∧
  (∀ ctx k, Persistent (ctxStreamKey (GF := GF) ctx k)) ∧
  (∀ v γ who, Persistent (remoteWatchAt (GF := GF) v γ who)) ∧
  (∀ g ss, Persistent (wireWatchSentLb (GF := GF) g ss)) ∧
  (∀ e k, Persistent (closeErrOk (GF := GF) e k))

/-- **`watcherAt`'s meaning** (W0's slot): the `Watcher` interface value's three triples. -/
def watcherAt_methods.spec : Prop := ∀ (v : GoInterface) (γ : Cluster) (who : Principal),
  Watcher.WatchTriple (v @!! go_etcd_io.etcd.client.v3.Watcher.ty @!! go!"Watch")
    (watcherAt (GF := GF) v γ who) γ who ∧
  Watcher.RequestProgressTriple (v @!! go_etcd_io.etcd.client.v3.Watcher.ty @!! go!"RequestProgress")
    (watcherAt (GF := GF) v γ who) who ∧
  Watcher.CloseTriple (v @!! go_etcd_io.etcd.client.v3.Watcher.ty @!! go!"Close")
    (watcherAt (GF := GF) v γ who)

/-- A `*watcher` meets the contract (its methods' specs, `watcher__*.lean`) once its client is ready
(`clientReady c`: the stub opens a stream through the client's stream interceptor, whose token
refresh reads `c.Auth`, which `newClient` sets after `NewWatcher`; verify-round W3).
`clientReady_null` for a watcher over a caller's stub (the in-process client). -/
def watcherHandle_watcherAt.spec : Prop := ∀ w c γ who,
  watcherHandle (GF := GF) w c γ who ∗ clientReady c ⊢
    watcherAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.watcher.ty) #w) γ who

/-- **Contexts with the same stream key are authenticated alike** (verify-round W2): `Watch` and
`RequestProgress` join the stream another context with the same key opened, whose principal the
member authenticates it as. True of every context `ctxPrin`'s introductions admit (W0's
`ctxPrin_of_noMeta`, `_token`, `_tokenSame`, `_value`, `_child`, `WithRequireLeader`'s,
`withVersion`'s): their outgoing metadata is none (the key `""`, which no map prints as), or maps
of fixed lower-case keys (`token`, `hasleader`, the version's) to one value with no space, `:`,
`[` or `]` (a token: simple tokens are letters, JWTs base64url and dots), which `%+v` prints
injectively; the principal is a function of the metadata (the token's user, else `dflt`). A
context whose metadata collides (`nonissues/etcd-watch-stream-key-collision.md`: values with
spaces) has no `ctxPrin`. Realized with the old tree's `streamKeyOf_none`, `streamKeyOf_single`
(`specs-ref/Proof/go_etcd_io/etcd/client/v3/StreamKey.lean`) over `fmt`'s boundary. -/
def ctxStreamKey_prin.spec : Prop := ∀ (dflt : Principal) (ctx ctx' : GoInterface) (p p' : Principal)
    (k : GoString),
  ctxPrin (GF := GF) dflt ctx p ∗ ctxPrin dflt ctx' p' ∗ ctxStreamKey ctx k ∗ ctxStreamKey ctx' k ⊢
    ⌜p = p'⌝

/-- **Receiving from a watch's channel** (alone, or each iteration of a `for range`): a response,
modelled, with what it says (`watchStep`, at reached states), and the consumer at the new
position; or the channel closed (no fact: a closed channel says nothing of why). -/
def watchChAt_recv.spec : Prop := ∀ (ch : Loc) (γ : Cluster) (who : Principal) (w : WatchReq)
    (p : WatchPos),
  {{ watchChAt (GF := GF) ch γ who w p }}
    (App (Val (chan.receive go_etcd_io.etcd.client.v3.WatchResponse.ty)) (Val #ch))
  {{ (v : go_etcd_io.etcd.client.v3.WatchResponse) (ok : Bool), RET (PairV #v #ok);
      if ok then ∃ (m : WatchRespM) (p' : WatchPos) (σ σa : State),
        watchRespAt v m ∗ etcdLb γ σ ∗ etcdLb γ σa ∗ ⌜watchStep who w σ σa p m p'⌝ ∗
        watchChAt ch γ who w p'
      else watchChAt ch γ who w p }}

/-- **Receiving from a watch's channel in a `select`**: the channel's receive update (Perennial's
`recvAu`), with the same outcomes as `watchChAt_recv`. -/
def watchChAt_recvAu.spec : Prop := ∀ (ch : Loc) (γ : Cluster) (who : Principal) (w : WatchReq)
    (p : WatchPos) (Φ : go_etcd_io.etcd.client.v3.WatchResponse → Bool → IProp GF),
  watchChAt (GF := GF) ch γ who w p ⊢
    ∃ (_ : Pos.Countable go_etcd_io.etcd.client.v3.WatchResponse) (γc : ChanNames),
      isChan ch γc go_etcd_io.etcd.client.v3.WatchResponse ∗
      (£ 1 ∗ £ 1 -∗
        (▷ ∀ (v : go_etcd_io.etcd.client.v3.WatchResponse) (ok : Bool),
          (if ok then ∃ (m : WatchRespM) (p' : WatchPos) (σ σa : State),
             watchRespAt v m ∗ etcdLb γ σ ∗ etcdLb γ σa ∗ ⌜watchStep who w σ σa p m p'⌝ ∗
             watchChAt ch γ who w p'
           else watchChAt ch γ who w p) -∗ Φ v ok) -∗
        recvAu γc go_etcd_io.etcd.client.v3.WatchResponse Φ)

/-- **What `watchRespAt` gives**: the exported fields (the header at `hdrDq`, the events in full),
the private `closeErr`'s kind; and back. -/
def watchRespAt_fields.spec : Prop := ∀ (v : go_etcd_io.etcd.client.v3.WatchResponse) (m : WatchRespM),
  watchRespAt (GF := GF) v m ⊣⊢
    respHeaderOwn v.Header' m.hdrDq m.hdr ∗ msgsOwn eventOwn v.Events' (DFrac.own 1) m.events ∗
    ⌜v.CompactRevision' = m.compactRev ∧ v.Canceled' = m.canceled ∧ v.Created' = m.created ∧
      v.CancelReason' = m.cancelReason⌝ ∗ closeErrOk v.closeErr' m.closeErr

/-- **A received response made read-only** (shared by many readers: the cache's demux and
history, `Election.Observe`'s forwarded header): its header and events at `DFrac.discard`. -/
def watchRespRO (v : go_etcd_io.etcd.client.v3.WatchResponse) (m : WatchRespM) : IProp GF :=
  iprop(respHeaderOwn v.Header' DFrac.discard m.hdr ∗ msgsOwn eventOwn v.Events' DFrac.discard m.events ∗
    ⌜v.CompactRevision' = m.compactRev ∧ v.Canceled' = m.canceled ∧ v.Created' = m.created ∧
      v.CancelReason' = m.cancelReason⌝ ∗ closeErrOk v.closeErr' m.closeErr)

def watchRespAt_persist.spec : Prop := ∀ (v : go_etcd_io.etcd.client.v3.WatchResponse) (m : WatchRespM),
  watchRespAt (GF := GF) v m ⊢ |==> watchRespRO v m

/-- The read-only form is persistent. -/
def watchRespRO_persistent.spec : Prop := ∀ v m, Persistent (watchRespRO (GF := GF) v m)

/-- A `nil` `closeErr` (every `WatchResponse` a caller builds itself: the cache's). -/
def closeErrOk_nil.spec : Prop := ⊢ closeErrOk (GF := GF) GoInterface.nil none

/-- **Opening a watch stream** (`v.Watch(ctx, opts...)`, 2a with the stub of 3h): a stream with both
halves, nothing sent nor received; or an error of some kind. -/
def remoteWatchAt_watch.spec : Prop := ∀ (v : GoInterface) (γ : Cluster) (who : Principal)
    (ctx : GoInterface) (p : Principal) (opts : GoSlice) (rep : Bool),
  {{ remoteWatchAt (GF := GF) v γ who ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗ callOptsOk opts rep }}
    (App (App (Val (v @!! go_etcd_io.etcd.api.v3.etcdserverpb.WatchClient.ty @!! go!"Watch"))
      (Val #ctx)) (Val #opts))
  {{ (wc : GoInterface) (err : GoInterface), RET (PairV #wc #err);
      (⌜err = GoInterface.nil ∧ wc ≠ GoInterface.nil⌝ ∗ ∃ g : WatchStreamNames,
         wireWatchSend wc γ p g [] ∗ wireWatchRecv wc γ p g WireSt.init) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ ∃ k, callErr err k) }}

/-- **Sending on a watch stream** (`wc.Send(req)`): the request read (given back), recorded as sent;
or an error (the stream broken or ended), the request still recorded as possibly sent (grpc's
`cliSend_send` counts it: the member may have read it), the half kept: later sends fail too. The
client then treats it as sent, as `run` does (a failed send is only logged). -/
def wireWatchSend_send.spec : Prop := ∀ (wc : GoInterface) (γ : Cluster) (who : Principal)
    (g : WatchStreamNames) (ss : List WireWatchReq) (p : Loc) (dq : DFrac) (r : WireWatchReq),
  {{ wireWatchSend (GF := GF) wc γ who g ss ∗ watchReqOwn p dq r }}
    (App (Val (wc @!! (google_golang_org.grpc.BidiStreamingClient.ty
        go_etcd_io.etcd.api.v3.etcdserverpb.WatchRequest.ty
        go_etcd_io.etcd.api.v3.etcdserverpb.WatchResponse.ty) @!! go!"Send")) (Val #p))
  {{ (err : GoInterface), RET #err; watchReqOwn p dq r ∗
      ((⌜err = GoInterface.nil⌝ ∗ wireWatchSend wc γ who g (ss ++ [r])) ∨
       (⌜err ≠ GoInterface.nil⌝ ∗ wireWatchSend wc γ who g (ss ++ [r]))) }}

/-- A lower bound of what was sent. -/
def wireWatchSend_lb.spec : Prop := ∀ wc γ who g ss,
  wireWatchSend (GF := GF) wc γ who g ss ⊢ wireWatchSend wc γ who g ss ∗ wireWatchSentLb g ss

/-- **Receiving on a watch stream** (`wc.Recv()`): the next response, owned, what it may be
(`wireStep`: after requests `ss` sent, at reached states), and the half at the new state; or an
error ending the stream (of some kind). -/
def wireWatchRecv_recv.spec : Prop := ∀ (wc : GoInterface) (γ : Cluster) (who : Principal)
    (g : WatchStreamNames) (st : WireSt),
  {{ wireWatchRecv (GF := GF) wc γ who g st }}
    (App (Val (wc @!! (google_golang_org.grpc.BidiStreamingClient.ty
        go_etcd_io.etcd.api.v3.etcdserverpb.WatchRequest.ty
        go_etcd_io.etcd.api.v3.etcdserverpb.WatchResponse.ty) @!! go!"Recv")) (Val #()))
  {{ (p : Loc) (err : GoInterface), RET (PairV #p #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (m : WireWatchRespM) (st' : WireSt) (ss : List WireWatchReq)
         (σ σa : State),
         wireWatchRespOwn p (DFrac.own 1) m ∗ wireWatchSentLb g ss ∗ etcdLb γ σ ∗ etcdLb γ σa ∗
         ⌜wireStep who σ σa ss st m st'⌝ ∗ wireWatchRecv wc γ who g st') ∨
      (⌜p = null ∧ err ≠ GoInterface.nil⌝ ∗ ∃ k, callErr err k) }}

/-- **The watch records' laws** (2a's; realization: ghost lists and agreeing maps keyed by `g`, the
request log and the principal allocated from grpc's `streamKey g`, the states by the server's
sending half: `watchRun_open`, `v3rpc/Api.lean`). -/
def watchSpec_records.spec : Prop :=
  (∀ g i r, Persistent (wsReq (GF := GF) g i r)) ∧ (∀ g j s, Persistent (wsSt (GF := GF) g j s)) ∧
  (∀ g w, Persistent (wsWho (GF := GF) g w)) ∧
  (∀ g i r r', wsReq (GF := GF) g i r ∗ wsReq g i r' ⊢ ⌜r = r'⌝) ∧
  (∀ g j s s', wsSt (GF := GF) g j s ∗ wsSt g j s' ⊢ ⌜s = s'⌝) ∧
  (∀ g w w', wsWho (GF := GF) g w ∗ wsWho g w' ⊢ ⌜w = w'⌝) ∧
  (∀ g, ⊢ wsSt (GF := GF) g 0 WireSt.init)

/-- The request log: allocated with the principal from the stream's key; a send appends. -/
def wsLog_alloc.spec : Prop := ∀ g who,
  Grpc.streamKey (GF := GF) g ⊢ |==> wsLog g [] ∗ wsWho g who
def wsLog_add.spec : Prop := ∀ g ss r,
  wsLog (GF := GF) g ss ⊢ |==> wsLog g (ss ++ [r]) ∗ wsReq g ss.length r
def wsLog_lb.spec : Prop := ∀ g ss,
  wsLog (GF := GF) g ss ⊢ wsLog g ss ∗ wireWatchSentLb g ss

end res

end ClientV3
end EtcdGrove
end Perennial
