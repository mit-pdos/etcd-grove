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

## Vocabulary

Pure (transparent):
* `WatchReq`: what a watch delivers (its range, normalized as the member does: an empty key is
  `"\x00"`; `prevKV`; the filters; the notification flags). `OpM.watchReq`, `OpM.watchRev`.
* `WEv` (a history event as a watch delivers it: revision, delete or put, the key-value),
  `watchEvents w h lo hi` (the range's events of revisions `lo..hi`, in order, filtered),
  `WatchReq.prevOk` (the previous key-value: the key's record at the revision before, absent only
  for a creation or below the compaction: `nonissues/etcd-watch-prevkv-nil-after-compaction.md`).
* `EventM` (an `mvccpb.Event`), `WatchRespM` (a `clientv3.WatchResponse`: its exported fields, and
  the kind of its private `closeErr`), `WatchPos`, `watchStep`.
* The wire protocol of one gRPC watch stream (**the contract with 2a/2b**): `WireWatchReq` (a
  create, a cancel, a progress request), `WireWatchRespM` (a `pb.WatchResponse`), `WireSt` (the
  stream's registrations as its responses made them) and `wireStep`: a `Created` answers the
  oldest unanswered create, a response of a registration's id is a `watchStep` of it, the id `-1`
  a progress of every registration, fragments reassemble to one response.

Resources:
* `watcherHandle w γ who` (persistent): a `*watcher` of the cluster `γ` as `who`
  (`NewWatchFromWatchClient`'s). Intended realization: its read-only fields (`remote` a
  `remoteWatchAt`, `callOpts`, the logger), and its lock `mu` over `streams` (`nil` once closed,
  else a map of `*watchGRPCStream`s, each `wgsAt`, `WatchInternal.lean`).
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
* `eventOwn p dq e`: an `mvccpb.Event` message (`eventOwn_unfold`; with W0's `keyValueOwn`).
  Offered to `api/v3/Wire.lean` (W0/3h): 2b builds these.
* `closeErrOk e k` (persistent): `e` is `nil` (`k = none`) or an error that `rpctypes.Error` maps
  to one of kind `k` (`CallErr`); `closeErrOk_nil`.
* **Slots of the gRPC boundary (2a, with 2b's handler and 3h's stub)**: `remoteWatchAt v γ who`
  (a `pb.WatchClient` whose `Watch` opens a stream, `remoteWatchAt_watch`), the stream's halves
  `wireWatchSend wc γ who g ss` (the sends so far, `wireWatchSend_send`) and `wireWatchRecv wc γ who
  g st` (the stream's state, `wireWatchRecv_recv`), `wireWatchSentLb g ss` (persistent: at least
  `ss` was sent), `watchReqOwn p dq r` (a `pb.WatchRequest`), `wireWatchRespOwn p dq m` (a
  `pb.WatchResponse`). `WatchStreamNames`: opaque ghost names of one stream.

## Requirement snippets

`examples/specreq/clientv3watch/`: `history.go` (no gap from the start revision, revision order,
values; all events of a revision in one response; filters), `progress.go` (progress notifications
monotone and meaning "nothing missed"; `RequestProgress`), `ending.go` (compaction, errors end the
watch, `Created` first, a refused watch delivers nothing, `Close`), `consume.go` (a `select` with
the context, writing the response as `Election.Observe` and the namespace wrapper do, the
previous key-value Kubernetes reads).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

/-! ## What a watch delivers -/

/-- **A watch request**: what it delivers. `range` as the member reads it (an empty key is
`"\x00"`, `v3rpc/watch.go`); the filters drop puts (`NOPUT`) or deletes (`NODELETE`). -/
structure WatchReq where
  range : KeyRange
  prevKV : Bool
  filterPut : Bool
  filterDelete : Bool
  progressNotify : Bool
  createdNotify : Bool
  fragment : Bool

/-- The watch an `Op` built by `OpWatch` asks for (`watcher.Watch`: `string(ow.key)`,
`string(ow.end)`; a `nil` end is the single key). -/
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
def WatchReq.keeps (w : WatchReq) (e : WEv) : Prop :=
  w.range.mem e.kv.key ∧ ¬ (e.del = true ∧ w.filterDelete = true) ∧
    ¬ (e.del = false ∧ w.filterPut = true)

/-- **The events the watch `w` delivers of the revisions `lo..hi`** of the history `h`, in order
(revision order, and each revision's events in their order). -/
def watchEvents (w : WatchReq) (h : KVHist) (lo hi : Nat) : List WEv :=
  ((List.range' lo (hi + 1 - lo)).flatMap (fun r => (h.eventsAt r).map (WEv.ofEvent r))).filter
    (fun e => decide (w.keeps e))

/-- **An event's previous key-value** (`WithPrevKV`; `v3rpc/watch.go`'s range at `ModRevision - 1`):
the key's record at the revision before, or none when there is none, the event is a creation
(`IsCreateEvent`: not looked up), or that revision is below the compaction. Without `prevKV`,
none. -/
def WatchReq.prevOk (w : WatchReq) (h : KVHist) (e : WEv) (pk : Option KeyValueM) : Prop :=
  if w.prevKV then
    pk = (h.storeAt (e.rev - 1) e.kv.key).map (fun r => KeyValueM.ofKV (KV.ofRec e.kv.key r)) ∨
    (pk = none ∧ (e.kv.createRevision = e.kv.modRevision ∨ e.rev - 1 < h.compacted))
  else pk = none

/-- **An `mvccpb.Event`**: `Type` (`DELETE` iff `del`), `Kv`, `PrevKv` (`none`: `nil`). -/
structure EventM where
  del : Bool
  kv : KeyValueM
  prevKv : Option KeyValueM

/-- The delivered event `m` is the history's event `e`. -/
def EventM.isOf (w : WatchReq) (h : KVHist) (m : EventM) (e : WEv) : Prop :=
  m.del = e.del ∧ m.kv = e.kv ∧ w.prevOk h e m.prevKv

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

/-- A new watch from the revision `rev`; `r0` a revision the cluster had reached when `Watch`
returned (the floor of a watch from the current revision: every event above it is delivered). -/
def WatchPos.init (rev : Int) (r0 : Nat) : WatchPos :=
  { done := if 0 < rev then some (rev.toNat - 1) else none,
    floor := if 0 < rev then none else some r0, started := false, ended := false }

/-- A watch whose channel delivers at most one error response, then closes (`Watch` on a closed
watcher, a done context, a stream that ended). -/
def WatchPos.closed (rev : Int) : WatchPos :=
  { WatchPos.init rev 0 with ended := true }

/-- **What a response of the watch `w` says**, received at the position `p` and leaving it at `p'`,
read against the reached states `σ` (the history) and `σa` (an auth state that admitted the watch
of the principal `who`: the member's applied one when it registered the watch, so any state the
cluster reached, a lagging member's included):

* every response's header revision has been reached; the floor never changes;
* after an error, only `closeErr` responses (header `0`, no compaction, no events);
* an **error** (`Err() != nil`) ends the watch; a `closeErr` one has header `0` and no compaction;
  a compaction (`CompactRevision` set, then no `closeErr`) says the next revision the watch needs
  is below a compaction of the cluster;
* a **`Created`** response only first, and only with `WithCreatedNotify`;
* a response **with events**: exactly the watch's events of the revisions from just after `p`'s
  (if `p`'s is unknown: from some revision at most the floor's + 1) to the last event's, all of
  them reached, and the principal was permitted to read the range;
* a **progress notification** (no events, a header revision `P`): nothing of the watch's since `p`'s
  revision up to `P`, and `P` is not below it (a watch whose position is still unknown learns
  nothing from it: after a reconnect such a watch resumes from its creation's header revision,
  which a progress computed before that header may be below);
* any other response (no events, header revision `0`): nothing. -/
def watchStep (who : Principal) (w : WatchReq) (σ σa : State) (p : WatchPos) (m : WatchRespM)
    (p' : WatchPos) : Prop :=
  sint.Z m.hdr.revision ≤ (σ.kv.rev : Int) ∧ p'.started = true ∧ p'.floor = p.floor ∧
  if p.ended = true then
    m.closeErr ≠ none ∧ m.compactRev = W64 0 ∧ m.hdr.revision = W64 0 ∧ m.events = [] ∧
    m.canceled = true ∧ p'.done = p.done ∧ p'.ended = true
  else if m.isErr then
    m.events = [] ∧ m.canceled = true ∧ m.created = false ∧ p'.done = p.done ∧ p'.ended = true ∧
    (m.closeErr ≠ none → m.compactRev = W64 0 ∧ m.hdr.revision = W64 0) ∧
    (m.compactRev ≠ W64 0 → m.closeErr = none ∧ ∃ cr : Nat, sint.Z m.compactRev = cr ∧
      cr ≤ σ.kv.compacted ∧ ∀ c, p.done = some c → c + 1 < cr)
  else if m.created = true then
    p.started = false ∧ w.createdNotify = true ∧ m.events = [] ∧ m.canceled = false ∧
    p'.done = p.done ∧ p'.ended = false
  else if m.events = [] then
    m.canceled = false ∧ p'.ended = false ∧
    (if m.hdr.revision = W64 0 then p'.done = p.done
     else ∃ P : Nat, sint.Z m.hdr.revision = P ∧
       (∀ c, p.done = some c → c ≤ P ∧ watchEvents w σ.kv (c + 1) P = []) ∧
       p'.done = p.done.map (fun _ => P))
  else
    m.canceled = false ∧ p'.ended = false ∧ σa.permits who [(.read, w.range)] [] ∧
    ∃ lo c' : Nat, (∀ c, p.done = some c → lo = c + 1) ∧
      (∀ f, p.done = none → p.floor = some f → lo ≤ f + 1) ∧ lo ≤ c' ∧
      (c' : Int) ≤ sint.Z m.hdr.revision ∧
      List.Forall₂ (EventM.isOf w σ.kv) m.events (watchEvents w σ.kv lo c') ∧
      m.events.getLast?.map (fun e => e.kv.modRevision) = some (W64 c') ∧ p'.done = some c'

/-! ## The wire protocol of a gRPC watch stream (the contract with 2a and 2b) -/

/-- **A `pb.WatchRequest`**: a create (the watch, its start revision as sent: the client resumes
from its position), a cancel of a watch id, a progress request. -/
inductive WireWatchReq where
  | create (w : WatchReq) (start : Int)
  | cancel (id : Int)
  | progress

/-- The creates among the requests, in order. -/
def WireWatchReq.creates (ss : List WireWatchReq) : List (WatchReq × Int) :=
  ss.filterMap fun
    | .create w s => some (w, s)
    | _ => none

/-- **A `pb.WatchResponse`** (`hdr` `none`: a `nil` header). -/
structure WireWatchRespM where
  hdr : Option HeaderM
  watchId : Int
  created : Bool
  canceled : Bool
  compactRev : w64
  cancelReason : GoString
  fragment : Bool
  events : List EventM

/-- The header as the client reads it (`ensureWatchHeader`: a `nil` header is a zero one). -/
def HeaderM.zero : HeaderM :=
  { clusterId := W64 0, memberId := W64 0, revision := W64 0, raftTerm := W64 0, leaderId := W64 0 }

/-- The client-level response a wire response (with its reassembled events `evs`) is, as
`dispatchEvent` builds it. -/
def WireWatchRespM.toResp (m : WireWatchRespM) (evs : List EventM) : WatchRespM :=
  { hdr := m.hdr.getD HeaderM.zero, events := evs, compactRev := m.compactRev,
    canceled := m.canceled, created := m.created, cancelReason := m.cancelReason,
    closeErr := none }

/-- **A stream's state** as its responses so far made it: how many creates were answered, the live
registrations (id, watch, position), the id and events of fragments not yet completed. -/
structure WireSt where
  answered : Nat
  regs : List (Int × WatchReq × WatchPos)
  frag : Option (Int × List EventM)

def WireSt.init : WireSt := { answered := 0, regs := [], frag := none }

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

* a fragment (`Fragment` set) carries part of a response's events: the next responses up to the
  first without `Fragment` are of the same id (`WireSt.frag` records it), none a creation or a
  cancel, and together they are one response;
* `Created` answers the oldest unanswered create: refused (`Canceled`, with a reason: an auth
  check, a negative start revision, an empty range), or registered under a fresh id, the principal
  permitted to read the range, at the position the start revision gives (from `0`: the floor is the
  creation's header revision: every event above it is sent);
* `Canceled` without compaction ends the id's registration (a cancel's answer);
* the id `-1` (no events, not created, canceled or compacted): a progress notification for every
  registration (each `watchStep`'s progress case at the same header);
* an id with a registration: a `watchStep` of it (events, progress, compaction);
* an id with none (canceled, or a stale one): nothing. -/
def wireStep (who : Principal) (σ σa : State) (ss : List WireWatchReq) (st : WireSt)
    (m : WireWatchRespM) (st' : WireSt) : Prop :=
  let evs := (st.frag.map (·.2)).getD [] ++ m.events
  -- a pending fragment: the next response is of its id, neither a creation nor a cancel
  (∀ id fe, st.frag = some (id, fe) → m.watchId = id ∧ m.created = false ∧ m.canceled = false) ∧
  if m.fragment = true then
    m.created = false ∧ m.canceled = false ∧ st' = { st with frag := some (m.watchId, evs) }
  else if m.created = true then
    ∃ w s, (WireWatchReq.creates ss)[st.answered]? = some (w, s) ∧ evs = [] ∧
      sint.Z (m.hdr.getD HeaderM.zero).revision ≤ (σ.kv.rev : Int) ∧
      (if m.canceled = true then
         m.watchId = -1 ∧ m.cancelReason ≠ [] ∧
         st' = { st with answered := st.answered + 1, frag := none }
       else σa.permits who [(.read, w.range)] [] ∧ st.reg m.watchId = none ∧ m.watchId ≠ -1 ∧
         st' = { answered := st.answered + 1,
                 regs := st.regs ++ [(m.watchId, w,
                   WatchPos.init s (sint.Z (m.hdr.getD HeaderM.zero).revision).toNat)],
                 frag := none })
  else if m.canceled = true ∧ m.compactRev = W64 0 then
    evs = [] ∧
    st' = { st with regs := st.regs.filter (fun r => decide (r.1 ≠ m.watchId)), frag := none }
  else if m.watchId = -1 then
    evs = [] ∧ m.canceled = false ∧ m.compactRev = W64 0 ∧
    ∃ P : Nat, sint.Z (m.hdr.getD HeaderM.zero).revision = P ∧ (P : Int) ≤ σ.kv.rev ∧
      (∀ r ∈ st.regs, ∀ c, r.2.2.done = some c → c ≤ P ∧ watchEvents r.2.1 σ.kv (c + 1) P = []) ∧
      st' = { st with
        regs := st.regs.map (fun r => (r.1, r.2.1, { r.2.2 with done := r.2.2.done.map (fun _ => P) })),
        frag := none }
  else
    match st.reg m.watchId with
    | none => st' = { st with frag := none }
    | some (w, p) => ∃ p', watchStep who w σ σa p (m.toResp evs) p' ∧
        st' = { st with regs := st.setReg m.watchId p', frag := none }

/-! ## Resources -/

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **A `*watcher`** of the cluster `γ` as `who` (persistent). -/
opaque watcherHandle (w : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)

/-- **The consumer of a watch's channel** `ch` (exclusive): the watch `w` of the principal `who`,
at the position `p`. -/
opaque watchChAt (ch : Loc) (γ : Cluster) (who : Principal) (w : WatchReq) (p : WatchPos) :
  IProp GF := iprop(True)

/-- **The `WatchResponse` value `v` is modelled by `m`** (exclusive: see the header). -/
opaque watchRespAt (v : go_etcd_io.etcd.client.v3.WatchResponse) (m : WatchRespM) : IProp GF :=
  iprop(True)

/-- **An `mvccpb.Event` message** at `p`, at the fraction `dq`. -/
opaque eventOwn (p : Loc) (dq : DFrac) (e : EventM) : IProp GF := iprop(True)

/-- **`e` is a watch response's `closeErr`** of kind `k` (persistent): `nil` (`none`), or an error
`rpctypes.Error` maps to one of kind `k`. -/
opaque closeErrOk (e : GoInterface) (k : Option CallErr) : IProp GF := iprop(True)

/-- **Slot (2a)**: the `pb.WatchClient` value `v` opens watch streams to members of `γ` as `who`. -/
opaque remoteWatchAt (v : GoInterface) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)

/-- Ghost names of one gRPC watch stream. -/
opaque WatchStreamNames : Type := Unit

/-- **Slot (2a)**: the sending half of the watch stream `wc` (exclusive), the requests `ss` sent. -/
opaque wireWatchSend (wc : GoInterface) (γ : Cluster) (who : Principal) (g : WatchStreamNames)
  (ss : List WireWatchReq) : IProp GF := iprop(True)

/-- **Slot (2a)**: the receiving half of the watch stream `wc` (exclusive), at the state `st`. -/
opaque wireWatchRecv (wc : GoInterface) (γ : Cluster) (who : Principal) (g : WatchStreamNames)
  (st : WireSt) : IProp GF := iprop(True)

/-- **Slot (2a)**: at least the requests `ss` were sent on the stream `g` (persistent). -/
opaque wireWatchSentLb (g : WatchStreamNames) (ss : List WireWatchReq) : IProp GF := iprop(True)

/-- **Slot (2a, 3h)**: a `pb.WatchRequest` message at `p` modelled by `r`. A create's key is
`w.range.key`, or `""` when that is `"\x00"` (`toPB` sends the watch's own key, which the member
normalizes). -/
opaque watchReqOwn (p : Loc) (dq : DFrac) (r : WireWatchReq) : IProp GF := iprop(True)

/-- **Slot (2a, 3h)**: a `pb.WatchResponse` message at `p` modelled by `m`. -/
opaque wireWatchRespOwn (p : Loc) (dq : DFrac) (m : WireWatchRespM) : IProp GF := iprop(True)

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
lease, no range-only option). `ctxPrin ctx who` (W0): the context names no other principal in its
metadata; the watch stream this watch joins was opened with a context of the same metadata, so the
member checks the create as `who`'s. -/
def Watcher.WatchTriple (f : val) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  ∀ (ctx : GoInterface) (key : GoString) (opts : GoSlice) (gs : List (OpM → OpM)),
  {{ P ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗ optsAt opts gs ∗ ⌜¬ (opWatchM key gs).watchPanics⌝ }}
    (App (App (App (Val f) (Val #ctx)) (Val #key)) (Val #opts))
  {{ (ch : Loc), RET #ch; ⌜ch ≠ null⌝ ∗ optsAt opts gs ∗
      ((∃ σ0 : State, etcdLb γ σ0 ∗
          watchChAt ch γ who (opWatchM key gs).watchReq
            (WatchPos.init (opWatchM key gs).watchRev σ0.kv.rev)) ∨
       watchChAt ch γ who (opWatchM key gs).watchReq (WatchPos.closed (opWatchM key gs).watchRev)) }}

/-- **`RequestProgress(ctx)`**: asks the member of the stream `ctx`'s metadata names for a progress
notification on every watch of that stream (what such a notification means is `watchStep`'s; that
one comes is liveness). The error (`nil`, the context's, the stream's, "no stream found") is not
modelled. -/
def Watcher.RequestProgressTriple (f : val) (P : IProp GF) (who : Principal) : Prop :=
  ∀ (ctx : GoInterface),
  {{ P ∗ Context.ctxOk ctx ∗ ctxPrin ctx who }}
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
  (∀ w γ who, Persistent (watcherHandle (GF := GF) w γ who)) ∧
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

/-- A `*watcher` meets the contract (its methods' specs, `watcher__*.lean`). -/
def watcherHandle_watcherAt.spec : Prop := ∀ w γ who,
  watcherHandle (GF := GF) w γ who ⊢
    watcherAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.watcher.ty) #w) γ who

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

/-- **What `eventOwn` means**: the `Event` struct's fields (`Type` `0` a put, `1` a delete). -/
def eventOwn_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (e : EventM),
  eventOwn (GF := GF) p dq e ⊣⊢
    ∃ (kv pk : Loc), protoRest go_etcd_io.etcd.api.v3.mvccpb.Event p dq ∗
    p.[go_etcd_io.etcd.api.v3.mvccpb.Event, go!"Type"] ↦{dq} (if e.del then W32 1 else W32 0) ∗
    p.[go_etcd_io.etcd.api.v3.mvccpb.Event, go!"Kv"] ↦{dq} kv ∗ keyValueOwn kv dq e.kv ∗
    p.[go_etcd_io.etcd.api.v3.mvccpb.Event, go!"PrevKv"] ↦{dq} pk ∗ optOwn keyValueOwn pk dq e.prevKv

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

/-- An event message made read-only. -/
def eventOwn_persist.spec : Prop := ∀ (p : Loc) (dq : DFrac) (e : EventM),
  eventOwn (GF := GF) p dq e ⊢ |==> eventOwn p DFrac.discard e

/-- A `nil` `closeErr` (every `WatchResponse` a caller builds itself: the cache's). -/
def closeErrOk_nil.spec : Prop := ⊢ closeErrOk (GF := GF) GoInterface.nil none

/-- **Opening a watch stream** (`v.Watch(ctx, opts...)`, 2a with the stub of 3h): a stream with both
halves, nothing sent nor received; or an error of some kind. -/
def remoteWatchAt_watch.spec : Prop := ∀ (v : GoInterface) (γ : Cluster) (who : Principal)
    (ctx : GoInterface) (opts : GoSlice) (rep : Bool),
  {{ remoteWatchAt (GF := GF) v γ who ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗ callOptsOk opts rep }}
    (App (App (Val (v @!! go_etcd_io.etcd.api.v3.etcdserverpb.WatchClient.ty @!! go!"Watch"))
      (Val #ctx)) (Val #opts))
  {{ (wc : GoInterface) (err : GoInterface), RET (PairV #wc #err);
      (⌜err = GoInterface.nil ∧ wc ≠ GoInterface.nil⌝ ∗ ∃ g : WatchStreamNames,
         wireWatchSend wc γ who g [] ∗ wireWatchRecv wc γ who g WireSt.init) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ ∃ k, callErr err k) }}

/-- **Sending on a watch stream** (`wc.Send(req)`): the request read (given back), recorded as sent;
or the stream broken (an error; the half kept: later sends fail too). -/
def wireWatchSend_send.spec : Prop := ∀ (wc : GoInterface) (γ : Cluster) (who : Principal)
    (g : WatchStreamNames) (ss : List WireWatchReq) (p : Loc) (dq : DFrac) (r : WireWatchReq),
  {{ wireWatchSend (GF := GF) wc γ who g ss ∗ watchReqOwn p dq r }}
    (App (Val (wc @!! (google_golang_org.grpc.BidiStreamingClient.ty
        go_etcd_io.etcd.api.v3.etcdserverpb.WatchRequest.ty
        go_etcd_io.etcd.api.v3.etcdserverpb.WatchResponse.ty) @!! go!"Send")) (Val #p))
  {{ (err : GoInterface), RET #err; watchReqOwn p dq r ∗
      ((⌜err = GoInterface.nil⌝ ∗ wireWatchSend wc γ who g (ss ++ [r])) ∨
       (⌜err ≠ GoInterface.nil⌝ ∗ wireWatchSend wc γ who g ss)) }}

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

end res

end ClientV3
end EtcdGrove
end Perennial
