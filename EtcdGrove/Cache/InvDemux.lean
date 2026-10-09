/-
etcd's cache `demux` (`cache/demux.go`): the shared vocabulary of `Spec/newDemux.lean` and
`Spec/demux__*.lean`. Lean-first (no Rocq counterpart).

**What the demux guarantees** (the delivery invariant): a registered watcher's channel
receives exactly the events of the broadcast stream from its starting revision on that its
key filter accepts, in revision order, with no gap and no duplicate, until it is stopped
(`Unregister`, `purge`) or canceled as compacted (`resyncLaggingWatchers`).

**The abstract state.** The single writer (the cache's watch loop, which calls `Init`,
`Broadcast`, `Purge`, `Compact`) owns half of a ghost variable with the `DemuxCore`: `minRev`,
`maxRev`, the `history` ring's batches, and the ghost `stream` of every batch broadcast since
the last reset (`purge`). A `Batch` is a non-empty list of events of one revision; the ring's
items are batches, `revOf = batchRev` (the `revisionOf` closure `newDemux` installs:
`batch[0].Kv.ModRevision`). `DemuxInv` is what the code maintains; note that `minRev` is a
*lower bound* of the history's revisions (and every stream batch at or above it is in the
history), not the oldest revision (see `DemuxInv`).

**The watchers.** The two Go maps `activeWatchers`/`laggingWatchers` (`map[*watcher]int64`,
the next revision each watcher needs) are internal to the lock. A registration is keyed by the
watcher's address `w` (ghost map `γd.reg`, `RegInfo`: the watcher's ghost names, its resolved
start revision `s`, and the name of its key filter's agreement `predIs`); the registrant
(`Cache.Watch`'s goroutine) holds the entry (`demuxRegistered`). Per registration the lock
side keeps `regRes`: the watcher's producer view (`watcherOpen`, or `watcherClosed` once
stopped/compacted), the ghost map entry of its `View` (`γd.views`: the stream and `maxRev`
it is consistent with, its next revision `n`, and its phase), and the delivery facts
`Delivered`. For a mapped (active or lagging) watcher, the view is the current state
(`RegsOk`); for a closed one it is frozen.

**Concurrency.** `mu` is a `sync.RWMutex` with Perennial's guarded, fractional spec. The lock
invariant `demuxLockInv d γd cap q` holds `q`-fractions of the fields, maps, ring, of the
ghost map auths and a `q.half` of the core ghost variable, and `q` of a "writer token"
`γd.wtok`. The per-registration resources `regRes` cannot be fractional (they hold the
exclusive `watcherOpen`), and are needed both by the write-lock holder (to broadcast) and by a
*reader*: `BroadcastProgressTo(w)` sends to `w` under `RLock`. So they live in a separate
invariant `demuxSlots`, one slot per registration: the write-lock holder takes all of them
(leaving `wtok 1`, which no reader can hold at the same time) and puts them back before
`Unlock`; the registrant of `w`, holding a read lock, borrows slot `w` (leaving half of its
`wtok` fraction and its registration entry) and returns it before `RUnlock`.
-/
import EtcdGrove.Cache.InvWatcher
import EtcdGrove.Cache.InvNotifier
import EtcdGrove.Cache.MapRangeMut
import EtcdGrove.Cache.Spec.watcher__enqueueResponse
import Perennial.Ghost.GhostMap
import Perennial.Ghost.SavedProp

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

/-! ## Batches and the stream -/

/-- A batch: the events of one revision, as the demux appends them to its history (the
`[]*mvccpb.Event` items of the ring). -/
abbrev Batch := List EvModel

/-- The revision of a batch: its first event's (`batch[0].Kv.ModRevision`); `0` for an empty
one, which `BatchOk` excludes. -/
def batchRev (b : Batch) : w64 :=
  match b with
  | e :: _ => e.rev
  | [] => W64 0

/-- A batch is non-empty and all its events have its revision. -/
def BatchOk (b : Batch) : Prop := b ≠ [] ∧ ∀ e ∈ b, e.rev = batchRev b

/-- A stream of batches: well-formed batches, strictly increasing revisions, all `≥ 1`. -/
structure StreamOk (st : List Batch) : Prop where
  batches : ∀ b ∈ st, BatchOk b
  sorted : RevSorted batchRev st
  pos : ∀ b ∈ st, 1 ≤ sint.Z (batchRev b)

/-- Events grouped into maximal runs of equal revision (`updateStoreLocked`'s batches). -/
def splitBatches : List EvModel → List Batch
  | [] => []
  | e :: es =>
    match splitBatches es with
    | [] => [[e]]
    | b :: bs => if batchRev b = e.rev then (e :: b) :: bs else [e] :: b :: bs

/-! ## The writer's state -/

/-- The demux's state as the writer sees it: `minRev`, `maxRev`, the history ring's batches
(oldest first) and the ghost stream of every batch broadcast since the last reset. -/
structure DemuxCore where
  minRev : w64
  maxRev : w64
  history : List Batch
  stream : List Batch

instance DemuxCore.countable : Pos.Countable DemuxCore :=
  .ofInjective (fun c => Pos.Countable.encode (c.minRev, c.maxRev, c.history, c.stream))
    (by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h; have h := Pos.encode_inj h; simp_all)

/-- A new (or purged) demux. -/
def DemuxCore.init : DemuxCore :=
  { minRev := W64 0, maxRev := W64 0, history := [], stream := [] }

/-- What the demux maintains, for a history of capacity `cap`:
* the stream is well-formed (`StreamOk`) and below `maxRev`; `0 ≤ maxRev < 2^63 - 1` (the
  upper bound keeps `maxRev + 1`, `lastRev + 1`, `PeekOldest() + 1` from overflowing; it is a
  precondition of `Broadcast`, on the response's revisions);
* the history is a suffix of the stream, of at most `cap` batches;
* every stream batch at or above `minRev` is in the history (what `resyncLaggingWatchers`
  needs: a lagging watcher at `n ≥ minRev` is owed only batches of the history). `minRev` is
  neither the oldest history revision (`updateStoreLocked` bumps it only before the last append
  of a response, and before the second-to-last one if the last batch is a single event, while
  earlier appends of the same response may evict too) nor even a lower bound of the history's
  revisions: `Broadcast` checks the events against `maxRev` only, so after `Init(100)` on a
  fresh demux an event at revision 5 is accepted and kept below `minRev` (etcd's watch from
  revision 100 does not send one; the demux does not check);
* `minRev = 0` (not initialized, or purged) means no stream and `maxRev = 0`. -/
structure DemuxInv (cap : Nat) (c : DemuxCore) : Prop where
  cap_pos : 0 < cap
  cap_le : cap ≤ 2 ^ 61
  stream_ok : StreamOk c.stream
  stream_le : ∀ b ∈ c.stream, sint.Z (batchRev b) ≤ sint.Z c.maxRev
  maxRev_nonneg : 0 ≤ sint.Z c.maxRev
  maxRev_lt : sint.Z c.maxRev < 2 ^ 63 - 1
  hist_suffix : c.history <:+ c.stream
  hist_len : c.history.length ≤ cap
  hist_complete : ∀ b ∈ c.stream, sint.Z c.minRev ≤ sint.Z (batchRev b) → b ∈ c.history
  uninit : c.minRev = W64 0 → c.stream = [] ∧ c.maxRev = W64 0

/-- `Init(minRev)`: the code's four cases. The second component says whether it purged
(stopped every watcher). -/
def initCore (c : DemuxCore) (m : w64) : DemuxCore × Bool :=
  if m = W64 0 then (c, false)
  else if c.minRev = W64 0 then ({ c with minRev := m }, false)
  else if c.maxRev = W64 0 then ({ DemuxCore.init with minRev := m }, true)
  else if m = c.maxRev + W64 1 then (c, false)
  else ({ DemuxCore.init with minRev := m }, true)

/-- The history after appending the batches `bs` one by one (`ringAppend`). -/
def appendAll (cap : Nat) (h : List Batch) (bs : List Batch) : List Batch :=
  bs.foldl (ringAppend cap) h

/-- What `updateStoreLocked` leaves for the (non-empty, sorted, above `maxRev`) events `evs`
of a response: their batches appended to the history and the stream, `maxRev` the last
event's revision, and `minRev` one above the revision of the batch the *last* append evicted
(if it evicted one: the history before it was full), unchanged otherwise. (The code also
bumps `minRev` before the second-to-last append in one case; the last append, which then also
evicts, overrides it.) -/
def updCore (cap : Nat) (c : DemuxCore) (evs : List EvModel) : DemuxCore :=
  let bs := splitBatches evs
  let hb := appendAll cap c.history bs.dropLast
  { minRev := if hb.length = cap then oldestRev batchRev hb + W64 1 else c.minRev
    maxRev := match evs.getLast? with
      | some e => e.rev
      | none => c.maxRev
    history := appendAll cap c.history bs
    stream := c.stream ++ bs }

/-- What `updateStoreLocked(resp)` leaves: a progress notification sets `maxRev`; events
are appended (`updCore`); anything else changes nothing. -/
def updResp (cap : Nat) (c : DemuxCore) (r : RespModel) : DemuxCore :=
  if r.isProgressNotify then { c with maxRev := r.hdrRev }
  else if r.events = [] then c
  else updCore cap c r.events

/-- `Broadcast(resp)` on state `c`: `none` for an error (nothing changes): not initialized
(`minRev = 0`), or `validateRevisions` fails; otherwise the new state (`updResp`). -/
def broadcastCore (cap : Nat) (c : DemuxCore) (r : RespModel) : Option DemuxCore :=
  if c.minRev = W64 0 then none
  else if !validRevisions r c.maxRev then none
  else some (updResp cap c r)

/-- `broadcastLocked(resp)`'s premise, after `updateStoreLocked` made the state `c` and the
registrations' views were brought up to date (`k`: the stream batches the active watchers are
known to be past): a progress notification is at `maxRev`, with nothing new in the stream;
events are sorted and are the stream's last batches, from `k` on; anything else adds nothing. -/
def BroadcastPre (c : DemuxCore) (k : Nat) (r : RespModel) : Prop :=
  if r.isProgressNotify then k = c.stream.length ∧ r.hdrRev = c.maxRev
  else if r.events = [] then k = c.stream.length
  else EvRevSorted r.events ∧ c.stream = c.stream.take k ++ splitBatches r.events

/-- The start revision `Register(w, startingRev)` resolves, when `maxRev` is `M`: `0` means
"from now" (`M + 1`, or `0` before any event). -/
def resolveStart (startingRev M : w64) : w64 :=
  if startingRev = W64 0 then (if M = W64 0 then W64 0 else M + W64 1) else startingRev

/-- `Broadcast`'s premise on the response: its revisions are below `2^63 - 1` (so that
`maxRev < 2^63 - 1` stays true; see `DemuxInv`). -/
def RespRevsBounded (r : RespModel) : Prop :=
  sint.Z r.hdrRev < 2 ^ 63 - 1 ∧ ∀ e ∈ r.events, sint.Z e.rev < 2 ^ 63 - 1

/-! ## A registered watcher -/

/-- Where a registered watcher is: in `activeWatchers`, in `laggingWatchers`, or neither
because it was closed (by `purge`: `none`; by a compaction at `n` in
`resyncLaggingWatchers`: `some n`). -/
inductive RegPhase where
  | active
  | lagging
  | closed (c : Option w64)
deriving DecidableEq

instance RegPhase.countable : Pos.Countable RegPhase :=
  .ofInjective (fun
      | .active => Pos.Countable.encode (none : Option (Option (Option w64)))
      | .lagging => Pos.Countable.encode (some none : Option (Option (Option w64)))
      | .closed c => Pos.Countable.encode (some (some c) : Option (Option (Option w64))))
    (by
      rintro (_ | _ | c1) (_ | _ | c2) h <;> have h := Pos.encode_inj h <;> simp_all)

/-- `phase` is active or lagging (the watcher is in one of the maps). -/
def RegPhase.mapped : RegPhase → Bool
  | .active => true
  | .lagging => true
  | .closed _ => false

/-- The watcher's producer phase (`WatcherPhase`, `InvWatcher.lean`). -/
def RegPhase.toWatcher : RegPhase → WatcherPhase
  | .active => .opened
  | .lagging => .opened
  | .closed c => .closed c

/-- What a registered watcher's delivery facts are about: the stream and `maxRev` (the
current ones while it is mapped, frozen once closed), its next revision `n` (the maps'
value), and its phase. -/
structure View where
  stream : List Batch
  maxRev : w64
  n : w64
  phase : RegPhase

instance View.countable : Pos.Countable View :=
  .ofInjective (fun v => Pos.Countable.encode (v.stream, v.maxRev, v.n, v.phase))
    (by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h; have h := Pos.encode_inj h; simp_all)

instance chanNames_countable : Pos.Countable ChanNames :=
  .ofInjective (fun c => Pos.Countable.encode (c.stateName, c.offerLockName,
      c.offerParkedPropName, c.offerParkedPredName, c.offerContinuationName, c.chanCap))
    (by rintro ⟨a, b, c, d, e, f⟩ ⟨a', b', c', d', e', f'⟩ h; have h := Pos.encode_inj h; simp_all)

instance watcherNames_countable : Pos.Countable WatcherNames :=
  .ofInjective (fun w => Pos.Countable.encode (w.ch, w.sent, w.recv, w.closed, w.tok))
    (by rintro ⟨a, b, c, d, e⟩ ⟨a', b', c', d', e'⟩ h; have h := Pos.encode_inj h; simp_all)

/-- A registration: the watcher's ghost names, its start revision as `Register` resolved
it, and the name of the agreement on its key filter (`predIs`). -/
structure RegInfo where
  γ : WatcherNames
  s : w64
  pn : GName

instance RegInfo.countable : Pos.Countable RegInfo :=
  .ofInjective (fun r => Pos.Countable.encode (r.γ, r.s, r.pn))
    (by rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h; have h := Pos.encode_inj h; simp_all)

/-! ## The delivery facts -/

/-- The key filter as a Boolean test on an event (`none`: keep everything). -/
def keepEv (pred : Option (GoString → Bool)) (e : EvModel) : Bool :=
  match pred with
  | none => true
  | some p => p e.key

/-- The events of a log of responses, in order (responses without events contribute none). -/
def eventsOf (sent : List RespModel) : List EvModel := (sent.map RespModel.events).flatten

/-- The batches of `st` with `s ≤ revision < n`. -/
def streamRange (s n : w64) (st : List Batch) : List Batch :=
  st.filter (fun b => decide (sint.Z s ≤ sint.Z (batchRev b) ∧ sint.Z (batchRev b) < sint.Z n))

/-- Response `r` is sent before `r'`: every event of `r` is below every event of `r'`; a
response without events (a progress notification, header revision `hdrRev`) is below every
event of a later response and at or above every event of an earlier one. -/
def RespBefore (r r' : RespModel) : Prop :=
  (∀ e ∈ r.events, ∀ e' ∈ r'.events, sint.Z e.rev < sint.Z e'.rev) ∧
  (r.events = [] → ∀ e' ∈ r'.events, sint.Z r.hdrRev < sint.Z e'.rev) ∧
  (r'.events = [] → ∀ e ∈ r.events, sint.Z e.rev ≤ sint.Z r'.hdrRev)

/-- A log of responses is in order: pairwise `RespBefore`, and each response's events by
non-decreasing revision. A consumer can thus trust a progress notification: no later event
is at or below it. -/
def SentOrdered (sent : List RespModel) : Prop :=
  sent.Pairwise RespBefore ∧ ∀ r ∈ sent, EvRevSorted r.events

/-- **The delivery facts** of a watcher with key filter `pred`, start revision `s` and view
`v`, whose producer log is `sent`:
* `events`: the events sent are exactly the events of the stream batches with
  `s ≤ revision < v.n`, in stream order, filtered by `pred` (no gap, no duplicate);
* `ordered`: the log is in order (`SentOrdered`);
* `progress`: a progress notification sent is at most `maxRev` and below every stream batch
  still owed (revision `≥ v.n`), so that what is sent later stays above it;
* `start_le`, `near`: `s ≤ v.n`, and `v.n ≤ maxRev + 1` unless nothing was sent yet
  (`v.n = s`, a start in the future): the batches broadcast later, above `maxRev`, are then
  not in `[s, v.n)`;
* `cancel`: a compaction cancel is at `v.n` (the log covers `[s, v.n)`);
* the stream is well-formed and below `maxRev`. -/
structure Delivered (pred : Option (GoString → Bool)) (s : w64) (v : View)
    (sent : List RespModel) : Prop where
  stream_ok : StreamOk v.stream
  stream_le : ∀ b ∈ v.stream, sint.Z (batchRev b) ≤ sint.Z v.maxRev
  events : eventsOf sent = ((streamRange s v.n v.stream).flatten).filter (keepEv pred)
  ordered : SentOrdered sent
  progress : ∀ r ∈ sent, r.events = [] →
    sint.Z r.hdrRev ≤ sint.Z v.maxRev ∧
    ∀ b ∈ v.stream, sint.Z v.n ≤ sint.Z (batchRev b) → sint.Z r.hdrRev < sint.Z (batchRev b)
  start_le : sint.Z s ≤ sint.Z v.n
  near : sint.Z v.n ≤ sint.Z v.maxRev + 1 ∨ v.n = s
  cancel : ∀ m, v.phase = .closed (some m) → m = v.n

/-- The next revision of a lagging watcher with next revision `n` after `resyncLaggingWatchers`
resent the first `i` of the batches `vis` it visits: one above the last one resent, `n` if
none. -/
def resyncNext (n : w64) (vis : List Batch) (i : Nat) : w64 :=
  match i with
  | 0 => n
  | j + 1 => match vis[j]? with
    | some b => batchRev b + W64 1
    | none => n

/-- What `resyncLaggingWatchers` (state `c`, initialized) does to a lagging watcher with view
`v` (new view `v'`, same stream and `maxRev`):
* `v.n < minRev`: compacted at `v.n` (closed with cancel `some v.n`);
* otherwise it resends the history batches from `v.n` on (`vis`, `ascendGeVisited`) until a
  send fails: if none fails, it is active with next revision one above the last batch resent
  (`v.n` if none), or `maxRev + 1` if that is below `maxRev` and a progress notification was
  then sent; if the send of the `i`-th fails, it stays lagging with next revision one above the
  last batch resent before it (`v.n` if `i = 0`). -/
def ResyncOutcome (c : DemuxCore) (v v' : View) : Prop :=
  v'.stream = v.stream ∧ v'.maxRev = v.maxRev ∧
  if sint.Z v.n < sint.Z c.minRev then v'.n = v.n ∧ v'.phase = .closed (some v.n)
  else
    let vis := ascendGeVisited batchRev v.n c.history
    (v'.phase = .active ∧
      (v'.n = resyncNext v.n vis vis.length ∨
        (sint.Z (resyncNext v.n vis vis.length) < sint.Z c.maxRev ∧ v'.n = c.maxRev + W64 1))) ∨
    (v'.phase = .lagging ∧ ∃ i, i < vis.length ∧ v'.n = resyncNext v.n vis i)

/-- `resyncLaggingWatchers` took the registrations' views from `views` to `views'` (state
`c`): nothing if not initialized; otherwise every lagging watcher as `ResyncOutcome` says, and
the others unchanged. -/
def ResyncStep (c : DemuxCore) (views views' : GMap Loc View) : Prop :=
  (∀ w, (views !! w).isSome = (views' !! w).isSome) ∧
  ∀ w v, views !! w = some v →
    if c.minRev = W64 0 ∨ v.phase ≠ .lagging then views' !! w = some v
    else ∃ v', views' !! w = some v' ∧ ResyncOutcome c v v'

/-- The active watchers' next revisions, from the views (the content of `activeWatchers`). -/
def actOf (views : GMap Loc View) : GMap Loc w64 :=
  (views.filter (fun _ v => decide (v.phase = .active))).fmap View.n

/-- The lagging watchers' next revisions, from the views (`laggingWatchers`). -/
def lagOf (views : GMap Loc View) : GMap Loc w64 :=
  (views.filter (fun _ v => decide (v.phase = .lagging))).fmap View.n

/-- A mapped view brought up to the state `c` (its stream and `maxRev`); closed views stay
frozen. -/
def refreshView (c : DemuxCore) (v : View) : View :=
  if v.phase.mapped then { v with stream := c.stream, maxRev := c.maxRev } else v

/-- `c'` extends `c` the way `Broadcast` does: batches appended, all above the old `maxRev`;
`maxRev` not decreasing; the new stream well-formed and below the new `maxRev`. -/
def StreamExt (c c' : DemuxCore) : Prop :=
  ∃ bs : List Batch, c'.stream = c.stream ++ bs ∧ sint.Z c.maxRev ≤ sint.Z c'.maxRev ∧
    (∀ b ∈ bs, sint.Z c.maxRev < sint.Z (batchRev b)) ∧ StreamOk c'.stream ∧
    (∀ b ∈ c'.stream, sint.Z (batchRev b) ≤ sint.Z c'.maxRev)

/-- The registrations and views of the lock, against the writer's state `c`:
* the registrations and the views have the same domain;
* a mapped watcher's view is the current stream and `maxRev`;
* an active watcher is up to date: no batch among the first `k` of the stream is at or above
  its `n` (`k` is the stream's length except inside `Broadcast`, between appending a
  response's batches and broadcasting them).
(The maps are `actOf views` and `lagOf views`.) -/
structure RegsOk (c : DemuxCore) (k : Nat) (regs : GMap Loc RegInfo) (views : GMap Loc View) :
    Prop where
  dom : ∀ w, (regs !! w).isSome = (views !! w).isSome
  mapped : ∀ w v, views !! w = some v → v.phase.mapped = true →
    v.stream = c.stream ∧ v.maxRev = c.maxRev
  active_up : ∀ w v, views !! w = some v → v.phase = .active →
    ∀ b ∈ c.stream.take k, sint.Z (batchRev b) < sint.Z v.n

/-! ## Predicates -/

/-- The ghost names of a demux. -/
structure DemuxNames where
  /-- `ghostVar DemuxCore`: half the writer's (`demuxWriter`), half in the lock -/
  core : GName
  /-- `ghostVar Unit`, fractional: the lock's "writer token"; all of it in the slots while
  the write-lock holder has taken them -/
  wtok : GName
  /-- `ghostMap Loc RegInfo`: the registrations (an entry is `demuxRegistered`); half of the
  auth in the lock, half in the slots -/
  reg : GName
  /-- `ghostMap Loc View`: the registrations' views (auth in the lock, an entry in each
  registration's `regRes`) -/
  views : GName

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The address of `d.mu`. -/
abbrev demuxMuAddr (d : Loc) : Loc := structFieldRef demux go!"mu" d
/-- The address of `d.activeWatchers`. -/
abbrev demuxActAddr (d : Loc) : Loc := structFieldRef demux go!"activeWatchers" d
/-- The address of `d.laggingWatchers`. -/
abbrev demuxLagAddr (d : Loc) : Loc := structFieldRef demux go!"laggingWatchers" d
/-- The address of `d.minRev`. -/
abbrev demuxMinRevAddr (d : Loc) : Loc := structFieldRef demux go!"minRev" d
/-- The address of `d.maxRev`. -/
abbrev demuxMaxRevAddr (d : Loc) : Loc := structFieldRef demux go!"maxRev" d
/-- The address of `d.history`. -/
abbrev demuxHistAddr (d : Loc) : Loc := structFieldRef demux go!"history" d
/-- The address of `d.resyncInterval`. -/
abbrev demuxResyncIntervalAddr (d : Loc) : Loc := structFieldRef demux go!"resyncInterval" d
/-- The address of `d.resynced`. -/
abbrev demuxResyncedAddr (d : Loc) : Loc := structFieldRef demux go!"resynced" d

end addrs

/-- The namespace of the slots invariant. -/
def demuxN : Namespace := nroot.@"demux"

/-- The key filter as a Boolean function on `Option GoString`, for its agreement (`predIs`):
`none` answers whether there is a filter, `some k` whether it accepts `k`. -/
def predCode (pred : Option (GoString → Bool)) : Option GoString → Bool
  | none => pred.isSome
  | some k => match pred with
    | none => false
    | some p => p k

theorem predCode_inj {p1 p2 : Option (GoString → Bool)} (h : predCode p1 = predCode p2) :
    p1 = p2 := by
  have h0 := congrFun h none
  cases p1 with
  | none =>
    cases p2 with
    | none => rfl
    | some _ => simp [predCode] at h0
  | some f1 =>
    cases p2 with
    | none => simp [predCode] at h0
    | some f2 =>
      congr 1
      funext k
      simpa [predCode] using congrFun h (some k)

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- The slice `sl` of `*mvccpb.Event` is the batch `b` (read-only): an item of the history
ring. -/
def batchAt (sl : GoSlice) (b : Batch) : IProp GF := iprop(eventsAt sl b ∗ ⌜BatchOk b⌝)

instance batchAt_persistent (sl : GoSlice) (b : Batch) : Persistent (batchAt (GF := GF) sl b) := by
  unfold batchAt; infer_instance

/-- The registration's key filter is `pred` (persistent agreement, `savedPred`). -/
def predIs (pn : GName) (pred : Option (GoString → Bool)) : IProp GF :=
  savedPredOwn pn DFrac.discard (fun k : Option GoString => iprop(⌜predCode pred k = true⌝))

instance predIs_persistent (pn : GName) (pred : Option (GoString → Bool)) :
    Persistent (predIs (GF := GF) pn pred) := by
  unfold predIs; infer_instance

/-- The lock side of a registration at `w` (see the module docstring): the watcher, its
filter, its view's entry, its producer view in the phase of the view, and the delivery
facts. -/
def regRes (γd : DemuxNames) (w : Loc) (ri : RegInfo) : IProp GF :=
  iprop(∃ (sent : List RespModel) (v : View) (pred : Option (GoString → Bool)),
    "#Hw" ∷ isWatcher w ri.γ pred ∗
    "#Hpred" ∷ predIs ri.pn pred ∗
    "Hview" ∷ w ↪[γd.views] v ∗
    "Hwat" ∷ watcherAt ri.γ sent v.phase.toWatcher ∗
    "%Hdel" ∷ ⌜Delivered pred ri.s v sent⌝)

/-- A slot of the slots invariant: the registration's resources, or (borrowed by its
registrant under a read lock) half of the registrant's writer-token fraction and half of its
registration entry. -/
def slotRes (γd : DemuxNames) (w : Loc) (ri : RegInfo) : IProp GF :=
  iprop(regRes γd w ri ∨ (ghostVar γd.wtok sync.rfrac.half () ∗ w ↪[γd.reg]{#(1 : Qp).half} ri))

/-- The slots invariant: taken by the write-lock holder (`wtok 1`), or the slots of all
registrations with half of the registrations' auth. -/
def demuxSlots (γd : DemuxNames) : IProp GF :=
  iprop(ghostVar γd.wtok 1 () ∨
    ∃ regs : GMap Loc RegInfo, ghostMapAuth γd.reg (1 : Qp).half regs ∗
      [∗map] w ↦ ri ∈ regs, slotRes γd w ri)

/-- The lock invariant `P q` of `d.mu` without the writer token (see the module docstring). -/
def demuxLockRest (d : Loc) (γd : DemuxNames) (cap : Nat) (q : Qp) : IProp GF :=
  iprop(∃ (c : DemuxCore) (regs : GMap Loc RegInfo) (views : GMap Loc View) (actP lagP : Loc),
    "Hcore" ∷ ghostVar γd.core q.half c ∗
    "Hregs" ∷ ghostMapAuth γd.reg q.half regs ∗
    "Hviews" ∷ ghostMapAuth γd.views q views ∗
    "HminRev" ∷ demuxMinRevAddr d ↦{DFrac.own q} c.minRev ∗
    "HmaxRev" ∷ demuxMaxRevAddr d ↦{DFrac.own q} c.maxRev ∗
    "HactF" ∷ demuxActAddr d ↦{DFrac.own q} actP ∗
    "HlagF" ∷ demuxLagAddr d ↦{DFrac.own q} lagP ∗
    "Hact" ∷ actP ↦${DFrac.own q} (actOf views) ∗
    "Hlag" ∷ lagP ↦${DFrac.own q} (lagOf views) ∗
    "Hhist" ∷ ownRingBuffer (demuxHistAddr d) cap (batchAt (hG := hG)) batchRev c.history
      (DFrac.own q) ∗
    "%Hinv" ∷ ⌜DemuxInv cap c⌝ ∗
    "%Hok" ∷ ⌜RegsOk c c.stream.length regs views⌝)

/-- The lock invariant `P q` of `d.mu`: `q` of the writer token and the rest. -/
def demuxLockInv (d : Loc) (γd : DemuxNames) (cap : Nat) (q : Qp) : IProp GF :=
  iprop(ghostVar γd.wtok q () ∗ demuxLockRest d γd cap q)

/-- What `w`'s registrant (registration `ri`) holds while it has borrowed its slot under a
read lock: the read lock's `P rfrac` less half of its writer-token fraction, and half of its
registration entry (the other halves are in the slot). -/
def demuxLoan (d : Loc) (γd : DemuxNames) (cap : Nat) (w : Loc) (ri : RegInfo) : IProp GF :=
  iprop(ghostVar γd.wtok sync.rfrac.half () ∗ w ↪[γd.reg]{#(1 : Qp).half} ri ∗
    demuxLockRest d γd cap sync.rfrac)

/-- `d` is a demux with a history of capacity `cap` (persistent): its slots invariant, the
fields nobody writes (`resyncInterval`, `resynced`: the notifier, whose spec is not needed
here), and the capacity's bounds. -/
def isDemux (d : Loc) (γd : DemuxNames) (cap : Nat) : IProp GF :=
  iprop(∃ (ri : time.Duration) (n : Loc),
    "#HresyncInterval" ∷ demuxResyncIntervalAddr d ↦□ ri ∗
    "#Hresynced" ∷ demuxResyncedAddr d ↦□ n ∗
    "#Hslots" ∷ inv demuxN (demuxSlots γd) ∗
    "%Hcap" ∷ ⌜0 < cap ∧ cap ≤ 2 ^ 61⌝)

instance isDemux_persistent (d : Loc) (γd : DemuxNames) (cap : Nat) :
    Persistent (isDemux (GF := GF) d γd cap) := by
  unfold isDemux; infer_instance

/-- One of the `RWMutex`'s tokens (`RLock` and `Lock` need one): every goroutine that calls
the demux holds one. -/
def demuxHandle (d : Loc) (γd : DemuxNames) (cap : Nat) : IProp GF :=
  sync.ownRWMutex (demuxMuAddr d) (demuxLockInv (hG := hG) d γd cap)

/-- The single writer's view (the cache's watch loop, which calls `Init`, `Broadcast`,
`Purge` and `Compact`): the state is `c`. Half of the core ghost variable, its own token. -/
def demuxWriter (d : Loc) (γd : DemuxNames) (cap : Nat) (c : DemuxCore) : IProp GF :=
  iprop(ghostVar γd.core (1 : Qp).half c ∗ demuxHandle d γd cap ∗ ⌜DemuxInv cap c⌝)

/-- The registrant's token: `w` is registered with ghost names `γ`, key filter `pred` and
start revision `s` (exclusive). -/
def demuxRegistered (γd : DemuxNames) (w : Loc) (γ : WatcherNames)
    (pred : Option (GoString → Bool)) (s : w64) : IProp GF :=
  iprop(∃ pn : GName, w ↪[γd.reg] (RegInfo.mk γ s pn) ∗ predIs pn pred)

/-- The demux while its write lock is held (taken from the lock invariant and the slots, less
the core ghost variable, which the specs handle): the fields, maps and ring in full, both
ghost auths, every registration's resources, and `RegsOk` with the first `k` stream batches
covered by `active_up`. -/
def demuxLocked (d : Loc) (γd : DemuxNames) (cap : Nat) (c : DemuxCore) (k : Nat)
    (regs : GMap Loc RegInfo) (views : GMap Loc View) : IProp GF :=
  iprop(∃ (actP lagP : Loc),
    "Hregs" ∷ ghostMapAuth γd.reg 1 regs ∗
    "Hviews" ∷ ghostMapAuth γd.views 1 views ∗
    "HminRev" ∷ demuxMinRevAddr d ↦ c.minRev ∗
    "HmaxRev" ∷ demuxMaxRevAddr d ↦ c.maxRev ∗
    "HactF" ∷ demuxActAddr d ↦ actP ∗
    "HlagF" ∷ demuxLagAddr d ↦ lagP ∗
    "Hact" ∷ actP ↦$ (actOf views) ∗
    "Hlag" ∷ lagP ↦$ (lagOf views) ∗
    "Hhist" ∷ ownRingBuffer (demuxHistAddr d) cap (batchAt (hG := hG)) batchRev c.history ∗
    "Hres" ∷ ([∗map] w ↦ ri ∈ regs, regRes γd w ri) ∗
    "%Hok" ∷ ⌜RegsOk c k regs views⌝)

/-- `γ` is the only ghost name of the watcher at `w`: two watchers at one address are the
same one. What `Register` needs to know that `w` is not registered yet (with `watcherOpen γ
[]`). Not derivable from `isWatcher` (ghost names are not tied to addresses); a client gets
it from `w`'s allocation (`newWatcher`'s full points-to of `w.respCh` excludes any earlier
`isWatcher w`, whose `respCh` is persistent). -/
def watcherUnique (w : Loc) (γ : WatcherNames) : IProp GF :=
  iprop(□ ∀ (γ' : WatcherNames) (pred' : Option (GoString → Bool)),
    isWatcher w γ' pred' -∗ ⌜γ' = γ⌝)

instance watcherUnique_persistent (w : Loc) (γ : WatcherNames) :
    Persistent (watcherUnique (GF := GF) w γ) := by
  unfold watcherUnique; infer_instance

end defs

/-- What `Unregister` (and `demux_watcher_delivered`) report of a watcher with filter `pred`
and start `s` whose producer log is `sent`, closed with cancel `c` (`none` if open): the
delivery facts for some view, a compaction cancel being at the view's `n`. -/
def DeliveredLog (pred : Option (GoString → Bool)) (s : w64) (sent : List RespModel)
    (c : Option w64) : Prop :=
  ∃ v : View, Delivered pred s v sent ∧ ∀ m, c = some m → m = v.n

/-! ## The responses the demux sends -/

/-- The model of `WatchResponse{Events: evs}` (a nil header). -/
def eventsResp (evs : List EvModel) : RespModel :=
  { events := evs, compactRev := W64 0, canceled := false, created := false, hdrRev := W64 0 }

/-- The model of `WatchResponse{Header: &ResponseHeader{Revision: p}}`. -/
def progressResp (p : w64) : RespModel :=
  { events := [], compactRev := W64 0, canceled := false, created := false, hdrRev := p }

/-! ## Pure lemmas: batches -/

theorem batchRev_of_mem {b : Batch} (hb : BatchOk b) {e : EvModel} (he : e ∈ b) :
    e.rev = batchRev b := hb.2 e he

theorem splitBatches_flatten (evs : List EvModel) : (splitBatches evs).flatten = evs := by
  induction evs with
  | nil => rfl
  | cons e es ih =>
    simp only [splitBatches]
    split
    · rename_i h; rw [h] at ih; simp at ih; subst ih; rfl
    · rename_i b bs h
      rw [h] at ih
      split
      · simp only [List.flatten_cons, List.cons_append] at ih ⊢; rw [ih]
      · simp only [List.flatten_cons] at ih ⊢; simp [ih]

theorem splitBatches_eq_nil_iff (evs : List EvModel) : splitBatches evs = [] ↔ evs = [] := by
  constructor
  · intro h
    cases evs with
    | nil => rfl
    | cons e es =>
      simp only [splitBatches] at h
      split at h
      · simp at h
      · split at h <;> simp at h
  · rintro rfl; rfl

/-- The first batch starts with the first event. -/
theorem splitBatches_cons (e : EvModel) (es : List EvModel) :
    ∃ b bs, splitBatches (e :: es) = (e :: b) :: bs := by
  simp only [splitBatches]
  split
  · exact ⟨[], [], rfl⟩
  · rename_i b bs _
    split
    · exact ⟨b, bs, rfl⟩
    · exact ⟨[], b :: bs, rfl⟩

theorem splitBatches_ok (evs : List EvModel) : ∀ b ∈ splitBatches evs, BatchOk b := by
  induction evs with
  | nil => intro b hb; simp [splitBatches] at hb
  | cons e es ih =>
    intro x hx
    simp only [splitBatches] at hx
    split at hx
    · simp only [List.mem_singleton] at hx; subst hx
      exact ⟨by simp, by intro y hy; simp at hy; subst hy; rfl⟩
    · rename_i b bs h
      have hb : BatchOk b := ih b (by rw [h]; simp)
      split at hx
      · rename_i heq
        rcases List.mem_cons.1 hx with rfl | hx
        · refine ⟨by simp, fun y hy => ?_⟩
          rcases List.mem_cons.1 hy with rfl | hy
          · rfl
          · rw [hb.2 y hy, heq]; rfl
        · exact ih x (by rw [h]; exact List.mem_cons_of_mem _ hx)
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨by simp, by intro y hy; simp at hy; subst hy; rfl⟩
        · exact ih x (by rw [h]; exact hx)

/-- A batch's revision is the revision of one of the events. -/
theorem splitBatches_rev_mem (evs : List EvModel) (b : Batch) (hb : b ∈ splitBatches evs) :
    ∃ x ∈ evs, x.rev = batchRev b := by
  have hok := splitBatches_ok evs b hb
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hok.1
  refine ⟨x, ?_, rfl⟩
  rw [← splitBatches_flatten evs]
  exact List.mem_flatten.2 ⟨_, hb, List.mem_cons_self ..⟩

theorem splitBatches_sorted (evs : List EvModel) (hs : EvRevSorted evs) :
    RevSorted batchRev (splitBatches evs) := by
  induction evs with
  | nil => exact List.Pairwise.nil
  | cons e es ih =>
    unfold EvRevSorted at hs
    rw [List.pairwise_cons] at hs
    have ih := ih hs.2
    unfold RevSorted at ih ⊢
    simp only [splitBatches]
    split
    · exact List.pairwise_singleton _ _
    · rename_i b bs h
      rw [h] at ih
      split
      · rename_i heq
        rw [List.pairwise_cons] at ih ⊢
        refine ⟨fun y hy => ?_, ih.2⟩
        have := ih.1 y hy
        show sint.Z e.rev < sint.Z (batchRev y)
        rw [← heq]; exact this
      · rename_i hne
        rw [List.pairwise_cons]
        refine ⟨fun y hy => ?_, ih⟩
        obtain ⟨x, hx, hxr⟩ := splitBatches_rev_mem es y (by rw [h]; exact hy)
        have hle : sint.Z e.rev ≤ sint.Z (batchRev y) := hxr ▸ hs.1 x hx
        show sint.Z e.rev < sint.Z (batchRev y)
        rcases List.mem_cons.1 hy with rfl | hy
        · have : sint.Z (batchRev y) ≠ sint.Z e.rev := fun h' => hne (BitVec.eq_of_toInt_eq h')
          omega
        · have := (List.pairwise_cons.1 ih).1 y hy
          obtain ⟨x0, hx0, hx0r⟩ := splitBatches_rev_mem es b (by rw [h]; exact List.mem_cons_self ..)
          have hle0 : sint.Z e.rev ≤ sint.Z (batchRev b) := hx0r ▸ hs.1 x0 hx0
          omega

/-- Splitting at a revision boundary. -/
theorem splitBatches_append (xs ys : List EvModel)
    (h : ∀ x y, xs.getLast? = some x → ys.head? = some y → x.rev ≠ y.rev) :
    splitBatches (xs ++ ys) = splitBatches xs ++ splitBatches ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil =>
      -- `[x] ++ ys`
      cases ys with
      | nil => rfl
      | cons y ys =>
        have hxy : x.rev ≠ y.rev := h x y rfl rfl
        obtain ⟨b, bs, hb⟩ := splitBatches_cons y ys
        show splitBatches (x :: y :: ys) = [[x]] ++ splitBatches (y :: ys)
        simp only [splitBatches] at hb ⊢
        rw [hb]
        have : batchRev (y :: b) ≠ x.rev := fun h' => hxy h'.symm
        simp [this]
    | cons x' xs' =>
      have ih' := ih (fun a b ha hb => h a b (by simpa using ha) hb)
      show splitBatches (x :: ((x' :: xs') ++ ys)) = splitBatches (x :: x' :: xs') ++ splitBatches ys
      obtain ⟨b, bs, hb⟩ := splitBatches_cons x' xs'
      simp only [splitBatches] at ih' hb ⊢
      rw [ih', hb]
      simp only [List.cons_append]
      split <;> rfl

/-- A non-empty run of one revision is one batch. -/
theorem splitBatches_run (b : List EvModel) (hb : b ≠ []) (r : w64)
    (h : ∀ e ∈ b, e.rev = r) : splitBatches b = [b] := by
  induction b with
  | nil => exact absurd rfl hb
  | cons e es ih =>
    cases es with
    | nil => rfl
    | cons e' es' =>
      have ih' := ih (by simp) (fun x hx => h x (List.mem_cons_of_mem _ hx))
      simp only [splitBatches] at ih' ⊢
      rw [ih']
      have : batchRev (e' :: es') = e.rev := by
        show e'.rev = e.rev
        rw [h e' (by simp), h e (by simp)]
      simp [this]

/-- The first batch's revision is the first event's, the last batch's the last event's. -/
theorem splitBatches_head_rev (evs : List EvModel) (e : EvModel) (h : evs.head? = some e) :
    ∃ b, (splitBatches evs).head? = some b ∧ batchRev b = e.rev := by
  cases evs with
  | nil => simp at h
  | cons x xs =>
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    obtain ⟨b, bs, hb⟩ := splitBatches_cons x xs
    exact ⟨x :: b, by rw [hb]; rfl, rfl⟩

theorem splitBatches_last_rev (evs : List EvModel) (e : EvModel) (h : evs.getLast? = some e) :
    ∃ b, (splitBatches evs).getLast? = some b ∧ batchRev b = e.rev := by
  have hne : evs ≠ [] := by intro h'; subst h'; simp at h
  have hsne : splitBatches evs ≠ [] := fun h' => hne ((splitBatches_eq_nil_iff evs).1 h')
  obtain ⟨b, hb⟩ : ∃ b, (splitBatches evs).getLast? = some b := by
    cases hl : (splitBatches evs).getLast? with
    | none => simp [List.getLast?_eq_none_iff] at hl; exact absurd hl hsne
    | some b => exact ⟨b, rfl⟩
  refine ⟨b, hb, ?_⟩
  have hmem : b ∈ splitBatches evs := List.mem_of_getLast? hb
  have hok := splitBatches_ok evs b hmem
  have hsplit : splitBatches evs = (splitBatches evs).dropLast ++ [b] := by
    have hb' := hb
    rw [List.getLast?_eq_some_iff] at hb'
    obtain ⟨ys, hys⟩ := hb'
    rw [hys]; simp
  have hflat : evs = ((splitBatches evs).dropLast).flatten ++ b := by
    conv => lhs; rw [← splitBatches_flatten evs]
    rw [hsplit]; simp
  have hlast : evs.getLast? = b.getLast? := by
    rw [hflat, List.getLast?_append]
    cases hbl : b.getLast? with
    | none => simp [List.getLast?_eq_none_iff] at hbl; exact absurd hbl hok.1
    | some y => simp
  rw [hlast] at h
  exact (hok.2 e (List.mem_of_getLast? h)).symm

/-! ## Pure lemmas: the maps -/

theorem actOf_lookup (views : GMap Loc View) (w : Loc) :
    actOf views !! w =
      (views !! w).bind (fun v => if v.phase = .active then some v.n else none) := by
  unfold actOf
  simp only [GMap.lookup_fmap, GMap.lookup_filter]
  cases views !! w with
  | none => rfl
  | some v => by_cases h : v.phase = .active <;> simp [h]; exact ⟨v, ⟨rfl, h⟩, rfl⟩

theorem lagOf_lookup (views : GMap Loc View) (w : Loc) :
    lagOf views !! w =
      (views !! w).bind (fun v => if v.phase = .lagging then some v.n else none) := by
  unfold lagOf
  simp only [GMap.lookup_fmap, GMap.lookup_filter]
  cases views !! w with
  | none => rfl
  | some v => by_cases h : v.phase = .lagging <;> simp [h]; exact ⟨v, ⟨rfl, h⟩, rfl⟩

theorem actOf_insert (views : GMap Loc View) (w : Loc) (v : View) :
    actOf (GMap.insert w v views) =
      if v.phase = .active then GMap.insert w v.n (actOf views) else GMap.delete w (actOf views) := by
  apply GMap.ext; intro k
  show actOf (GMap.insert w v views) !! k = _
  rw [actOf_lookup]
  by_cases hk : w = k
  · subst hk
    split
    · rename_i h; simp [h]
    · rename_i h; simp [h]
  · rw [GMap.lookup_insert_ne _ _ hk]
    split
    · rw [GMap.lookup_insert_ne _ _ hk, actOf_lookup]
    · rw [GMap.lookup_delete_ne _ hk, actOf_lookup]

theorem lagOf_insert (views : GMap Loc View) (w : Loc) (v : View) :
    lagOf (GMap.insert w v views) =
      if v.phase = .lagging then GMap.insert w v.n (lagOf views) else GMap.delete w (lagOf views) := by
  apply GMap.ext; intro k
  show lagOf (GMap.insert w v views) !! k = _
  rw [lagOf_lookup]
  by_cases hk : w = k
  · subst hk
    split
    · rename_i h; simp [h]
    · rename_i h; simp [h]
  · rw [GMap.lookup_insert_ne _ _ hk]
    split
    · rw [GMap.lookup_insert_ne _ _ hk, lagOf_lookup]
    · rw [GMap.lookup_delete_ne _ hk, lagOf_lookup]

theorem actOf_delete (views : GMap Loc View) (w : Loc) :
    actOf (GMap.delete w views) = GMap.delete w (actOf views) := by
  apply GMap.ext; intro k
  show actOf (GMap.delete w views) !! k = (GMap.delete w (actOf views)) !! k
  rw [actOf_lookup]
  by_cases hk : w = k
  · subst hk; simp
  · rw [GMap.lookup_delete_ne _ hk, GMap.lookup_delete_ne _ hk, actOf_lookup]

theorem lagOf_delete (views : GMap Loc View) (w : Loc) :
    lagOf (GMap.delete w views) = GMap.delete w (lagOf views) := by
  apply GMap.ext; intro k
  show lagOf (GMap.delete w views) !! k = (GMap.delete w (lagOf views)) !! k
  rw [lagOf_lookup]
  by_cases hk : w = k
  · subst hk; simp
  · rw [GMap.lookup_delete_ne _ hk, GMap.lookup_delete_ne _ hk, lagOf_lookup]

theorem actOf_refresh (views : GMap Loc View) (c : DemuxCore) :
    actOf (views.fmap (refreshView c)) = actOf views := by
  apply GMap.ext; intro k
  show actOf (views.fmap (refreshView c)) !! k = actOf views !! k
  rw [actOf_lookup, actOf_lookup, GMap.lookup_fmap]
  cases views !! k with
  | none => rfl
  | some v => simp only [Option.map_some, Option.bind_some, refreshView]; split <;> rfl

theorem lagOf_refresh (views : GMap Loc View) (c : DemuxCore) :
    lagOf (views.fmap (refreshView c)) = lagOf views := by
  apply GMap.ext; intro k
  show lagOf (views.fmap (refreshView c)) !! k = lagOf views !! k
  rw [lagOf_lookup, lagOf_lookup, GMap.lookup_fmap]
  cases views !! k with
  | none => rfl
  | some v => simp only [Option.map_some, Option.bind_some, refreshView]; split <;> rfl

/-- No view is mapped: both maps are empty. -/
theorem actOf_lagOf_unmapped (views : GMap Loc View)
    (h : ∀ w v, views !! w = some v → v.phase.mapped = false) :
    actOf views = ∅ ∧ lagOf views = ∅ := by
  constructor
  · apply GMap.ext; intro k
    show actOf views !! k = none
    rw [actOf_lookup]
    cases hk : views !! k with
    | none => rfl
    | some v =>
      have := h k v hk
      simp only [Option.bind_some]
      split
      · rename_i hp; rw [hp] at this; simp [RegPhase.mapped] at this
      · rfl
  · apply GMap.ext; intro k
    show lagOf views !! k = none
    rw [lagOf_lookup]
    cases hk : views !! k with
    | none => rfl
    | some v =>
      have := h k v hk
      simp only [Option.bind_some]
      split
      · rename_i hp; rw [hp] at this; simp [RegPhase.mapped] at this
      · rfl

/-! ## Pure lemmas: `RegsOk` -/

theorem RegsOk.refresh {c c' : DemuxCore} {k : Nat} {regs : GMap Loc RegInfo}
    {views : GMap Loc View} (h : RegsOk c k regs views) (hk : k ≤ c.stream.length)
    (hext : StreamExt c c') : RegsOk c' k regs (views.fmap (refreshView c')) := by
  obtain ⟨bs, hs, -, -, -, -⟩ := hext
  have htake : c'.stream.take k = c.stream.take k := by
    rw [hs, List.take_append_of_le_length hk]
  refine ⟨fun w => ?_, fun w v hv hm => ?_, fun w v hv ha => ?_⟩
  · rw [GMap.lookup_fmap, h.dom w]; cases views !! w <;> rfl
  · rw [GMap.lookup_fmap] at hv
    cases hw : views !! w with
    | none => rw [hw] at hv; cases hv
    | some v0 =>
      rw [hw, Option.map_some, Option.some.injEq] at hv
      subst hv
      unfold refreshView at hm ⊢
      split at hm
      · rename_i h0; simp only [h0, ↓reduceIte]; exact ⟨trivial, trivial⟩
      · rename_i h0; exact absurd hm h0
  · rw [GMap.lookup_fmap] at hv
    cases hw : views !! w with
    | none => rw [hw] at hv; cases hv
    | some v0 =>
      rw [hw, Option.map_some, Option.some.injEq] at hv
      subst hv
      have hph : (refreshView c' v0).phase = v0.phase := by unfold refreshView; split <;> rfl
      have hn : (refreshView c' v0).n = v0.n := by unfold refreshView; split <;> rfl
      rw [hph] at ha
      rw [htake, hn]
      exact h.active_up w v0 hw ha

/-- Changing the view of a registered watcher. -/
theorem RegsOk.insert {c : DemuxCore} {k : Nat} {regs : GMap Loc RegInfo}
    {views : GMap Loc View} (h : RegsOk c k regs views) {w : Loc} (hw : (regs !! w).isSome)
    (v' : View) (hm : v'.phase.mapped = true → v'.stream = c.stream ∧ v'.maxRev = c.maxRev)
    (hup : v'.phase = .active → ∀ b ∈ c.stream.take k, sint.Z (batchRev b) < sint.Z v'.n) :
    RegsOk c k regs (GMap.insert w v' views) := by
  refine ⟨fun w' => ?_, fun w' v hv hmv => ?_, fun w' v hv ha => ?_⟩
  · by_cases hw' : w = w'
    · subst hw'; rw [GMap.lookup_insert]; simpa using hw
    · rw [GMap.lookup_insert_ne _ _ hw']; exact h.dom w'
  · by_cases hw' : w = w'
    · subst hw'; rw [GMap.lookup_insert] at hv; cases hv; exact hm hmv
    · rw [GMap.lookup_insert_ne _ _ hw'] at hv; exact h.mapped w' v hv hmv
  · by_cases hw' : w = w'
    · subst hw'; rw [GMap.lookup_insert] at hv; cases hv; exact hup ha
    · rw [GMap.lookup_insert_ne _ _ hw'] at hv; exact h.active_up w' v hv ha

/-- A new registration. -/
theorem RegsOk.register {c : DemuxCore} {k : Nat} {regs : GMap Loc RegInfo}
    {views : GMap Loc View} (h : RegsOk c k regs views) (w : Loc) (ri : RegInfo) (v : View)
    (hm : v.phase.mapped = true → v.stream = c.stream ∧ v.maxRev = c.maxRev)
    (hup : v.phase = .active → ∀ b ∈ c.stream.take k, sint.Z (batchRev b) < sint.Z v.n) :
    RegsOk c k (GMap.insert w ri regs) (GMap.insert w v views) := by
  refine ⟨fun w' => ?_, fun w' v' hv hmv => ?_, fun w' v' hv ha => ?_⟩
  · by_cases hw' : w = w'
    · subst hw'; rw [GMap.lookup_insert, GMap.lookup_insert]; rfl
    · rw [GMap.lookup_insert_ne _ _ hw', GMap.lookup_insert_ne _ _ hw']; exact h.dom w'
  · by_cases hw' : w = w'
    · subst hw'; rw [GMap.lookup_insert] at hv; cases hv; exact hm hmv
    · rw [GMap.lookup_insert_ne _ _ hw'] at hv; exact h.mapped w' v' hv hmv
  · by_cases hw' : w = w'
    · subst hw'; rw [GMap.lookup_insert] at hv; cases hv; exact hup ha
    · rw [GMap.lookup_insert_ne _ _ hw'] at hv; exact h.active_up w' v' hv ha

/-- A registration removed. -/
theorem RegsOk.unregister {c : DemuxCore} {k : Nat} {regs : GMap Loc RegInfo}
    {views : GMap Loc View} (h : RegsOk c k regs views) (w : Loc) :
    RegsOk c k (GMap.delete w regs) (GMap.delete w views) := by
  refine ⟨fun w' => ?_, fun w' v' hv hmv => ?_, fun w' v' hv ha => ?_⟩
  · by_cases hw' : w = w'
    · subst hw'; rw [GMap.lookup_delete, GMap.lookup_delete]; rfl
    · rw [GMap.lookup_delete_ne _ hw', GMap.lookup_delete_ne _ hw']; exact h.dom w'
  · by_cases hw' : w = w'
    · subst hw'; rw [GMap.lookup_delete] at hv; cases hv
    · rw [GMap.lookup_delete_ne _ hw'] at hv; exact h.mapped w' v' hv hmv
  · by_cases hw' : w = w'
    · subst hw'; rw [GMap.lookup_delete] at hv; cases hv
    · rw [GMap.lookup_delete_ne _ hw'] at hv; exact h.active_up w' v' hv ha

/-! ## Pure lemmas: the delivery facts -/

theorem streamRange_append (s n : w64) (st1 st2 : List Batch) :
    streamRange s n (st1 ++ st2) = streamRange s n st1 ++ streamRange s n st2 := by
  unfold streamRange; exact List.filter_append ..

theorem streamRange_mem {s n : w64} {st : List Batch} {b : Batch} (h : b ∈ streamRange s n st) :
    b ∈ st ∧ sint.Z s ≤ sint.Z (batchRev b) ∧ sint.Z (batchRev b) < sint.Z n := by
  unfold streamRange at h
  rw [List.mem_filter] at h
  simpa using h

/-- In a sorted stream, `[s, n')` is `[s, n)` then `[n, n')`. -/
theorem streamRange_split {s n n' : w64} {st : List Batch} (hsorted : RevSorted batchRev st)
    (hs : sint.Z s ≤ sint.Z n) (hn : sint.Z n ≤ sint.Z n') :
    streamRange s n' st = streamRange s n st ++ streamRange n n' st := by
  induction st with
  | nil => rfl
  | cons b bs ih =>
    unfold RevSorted at hsorted
    rw [List.pairwise_cons] at hsorted
    have ih := ih hsorted.2
    have hall : ∀ b' ∈ bs, sint.Z (batchRev b) < sint.Z (batchRev b') := hsorted.1
    unfold streamRange at ih ⊢
    simp only [List.filter_cons]
    by_cases h1 : sint.Z (batchRev b) < sint.Z n
    · by_cases h0 : sint.Z s ≤ sint.Z (batchRev b)
      · have e1 : decide (sint.Z s ≤ sint.Z (batchRev b) ∧ sint.Z (batchRev b) < sint.Z n') = true := by
          simp; omega
        have e2 : decide (sint.Z s ≤ sint.Z (batchRev b) ∧ sint.Z (batchRev b) < sint.Z n) = true := by
          simp; omega
        have e3 : decide (sint.Z n ≤ sint.Z (batchRev b) ∧ sint.Z (batchRev b) < sint.Z n') = false := by
          simp; omega
        rw [e1, e2, e3]; simp only [↓reduceIte, Bool.false_eq_true, List.cons_append, ih]
      · have e1 : decide (sint.Z s ≤ sint.Z (batchRev b) ∧ sint.Z (batchRev b) < sint.Z n') = false := by
          simp; omega
        have e2 : decide (sint.Z s ≤ sint.Z (batchRev b) ∧ sint.Z (batchRev b) < sint.Z n) = false := by
          simp; omega
        have e3 : decide (sint.Z n ≤ sint.Z (batchRev b) ∧ sint.Z (batchRev b) < sint.Z n') = false := by
          simp; omega
        rw [e1, e2, e3]; simp only [Bool.false_eq_true, ↓reduceIte, ih]
    · -- `b` and everything after it are at or above `n`: nothing more in `[s, n)`
      have hnone : List.filter
          (fun b => decide (sint.Z s ≤ sint.Z (batchRev b) ∧ sint.Z (batchRev b) < sint.Z n)) bs = [] := by
        rw [List.filter_eq_nil_iff]
        intro b' hb'
        have := hall b' hb'
        simp; omega
      have e2 : decide (sint.Z s ≤ sint.Z (batchRev b) ∧ sint.Z (batchRev b) < sint.Z n) = false := by
        simp; omega
      rw [e2, hnone]
      simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
      rw [hnone, List.nil_append] at ih
      by_cases h2 : sint.Z (batchRev b) < sint.Z n'
      · have e1 : decide (sint.Z s ≤ sint.Z (batchRev b) ∧ sint.Z (batchRev b) < sint.Z n') = true := by
          simp; omega
        have e3 : decide (sint.Z n ≤ sint.Z (batchRev b) ∧ sint.Z (batchRev b) < sint.Z n') = true := by
          simp; omega
        rw [e1, e3]; simp only [↓reduceIte, ih]
      · have e1 : decide (sint.Z s ≤ sint.Z (batchRev b) ∧ sint.Z (batchRev b) < sint.Z n') = false := by
          simp; omega
        have e3 : decide (sint.Z n ≤ sint.Z (batchRev b) ∧ sint.Z (batchRev b) < sint.Z n') = false := by
          simp; omega
        rw [e1, e3]; simp only [Bool.false_eq_true, ↓reduceIte, ih]

/-- Nothing at or above `n`: `[s, n')` is `[s, n)` for `n ≤ n'`. -/
theorem streamRange_up {s n n' : w64} {st : List Batch}
    (hup : ∀ b ∈ st, sint.Z (batchRev b) < sint.Z n) (hn : sint.Z n ≤ sint.Z n') :
    streamRange s n' st = streamRange s n st := by
  unfold streamRange
  apply List.filter_congr
  intro b hb
  have := hup b hb
  simp only [decide_eq_decide]
  omega

theorem eventsOf_append (sent : List RespModel) (r : RespModel) :
    eventsOf (sent ++ [r]) = eventsOf sent ++ r.events := by
  simp [eventsOf]

/-- An event sent is an event of a stream batch in `[s, n)`. -/
theorem Delivered.mem_events {pred : Option (GoString → Bool)} {s : w64} {v : View}
    {sent : List RespModel} (hD : Delivered pred s v sent) {r : RespModel} (hr : r ∈ sent)
    {e : EvModel} (he : e ∈ r.events) :
    ∃ b ∈ v.stream, e ∈ b ∧ e.rev = batchRev b ∧ sint.Z s ≤ sint.Z (batchRev b) ∧
      sint.Z (batchRev b) < sint.Z v.n := by
  have he' : e ∈ eventsOf sent := List.mem_flatten.2 ⟨r.events, List.mem_map.2 ⟨r, hr, rfl⟩, he⟩
  rw [hD.events, List.mem_filter] at he'
  obtain ⟨b, hb, heb⟩ := List.mem_flatten.1 he'.1
  obtain ⟨hbst, h1, h2⟩ := streamRange_mem hb
  exact ⟨b, hbst, heb, (hD.stream_ok.batches b hbst).2 e heb, h1, h2⟩

/-- The events of sorted batches are sorted. -/
theorem StreamOk.flatten_sorted {st : List Batch} (h : StreamOk st) :
    EvRevSorted st.flatten := by
  unfold EvRevSorted
  rw [List.pairwise_flatten]
  refine ⟨fun b hb => ?_, ?_⟩
  · have hok := h.batches b hb
    exact List.Pairwise.imp_of_mem (R := fun _ _ => True) (fun {x y} hx hy _ => by
      rw [hok.2 x hx, hok.2 y hy]; exact Int.le_refl _) (List.pairwise_of_forall (fun _ _ => trivial))
  · have := h.sorted
    unfold RevSorted at this
    exact List.Pairwise.imp_of_mem (fun {a b} ha hb hab x hx y hy => by
      rw [(h.batches a ha).2 x hx, (h.batches b hb).2 y hy]; omega) this

theorem StreamOk.sublist {st st' : List Batch} (h : StreamOk st) (hs : List.Sublist st' st) :
    StreamOk st' where
  batches b hb := h.batches b (hs.subset hb)
  sorted := h.sorted.sublist hs
  pos b hb := h.pos b (hs.subset hb)

/-- What `enqueueResponse` did with `WatchResponse{Events: evs}` (non-empty): nothing sent
(failure, or every event filtered out: reported delivered), or one response with the
filtered events. -/
theorem enqueue_events_cases {pred : Option (GoString → Bool)} {evs : List EvModel}
    {sent sent' : List RespModel} {ok : Bool} (hne : evs ≠ [])
    (henq : enqueueResult pred (eventsResp evs) sent ok sent') :
    (ok = false ∧ sent' = sent) ∨
    (ok = true ∧ evs.filter (keepEv pred) = [] ∧ sent' = sent) ∨
    (ok = true ∧ ∃ r', sent' = sent ++ [r'] ∧ r'.events = evs.filter (keepEv pred) ∧
      r'.events ≠ []) := by
  have hnp : (eventsResp evs).isProgressNotify = false := by
    cases evs with
    | nil => exact absurd rfl hne
    | cons _ _ => rfl
  unfold enqueueResult filterResp at henq
  cases pred with
  | none =>
    have hf : evs.filter (keepEv none) = evs := List.filter_eq_self.2 (fun _ _ => rfl)
    simp only at henq
    cases ok
    · exact Or.inl ⟨rfl, henq⟩
    · exact Or.inr (Or.inr ⟨rfl, eventsResp evs, henq, by rw [hf]; rfl, hne⟩)
  | some p =>
    simp only [eventsResp] at henq hnp
    by_cases hemp : (evs.filter (fun e => p e.key)).isEmpty = true
    · simp only [hnp, Bool.false_eq_true, ↓reduceIte, hemp] at henq
      exact Or.inr (Or.inl ⟨henq.1, List.isEmpty_iff.1 hemp, henq.2⟩)
    · simp only [hnp, Bool.false_eq_true, ↓reduceIte, hemp] at henq
      cases ok
      · exact Or.inl ⟨rfl, henq⟩
      · refine Or.inr (Or.inr ⟨rfl, _, henq, rfl, ?_⟩)
        intro h; apply hemp; rw [List.isEmpty_iff]; exact h

/-- What `enqueueResponse` did with a progress notification at `p`: nothing sent, or it. -/
theorem enqueue_progress_cases {pred : Option (GoString → Bool)} {p : w64}
    {sent sent' : List RespModel} {ok : Bool}
    (henq : enqueueResult pred (progressResp p) sent ok sent') :
    sent' = sent ∨ (ok = true ∧ sent' = sent ++ [progressResp p]) := by
  unfold enqueueResult filterResp at henq
  cases pred with
  | none =>
    simp only at henq
    cases ok
    · exact Or.inl henq
    · exact Or.inr ⟨rfl, henq⟩
  | some f =>
    by_cases hpn : (progressResp p).isProgressNotify = true
    · simp only [hpn, ↓reduceIte] at henq
      cases ok
      · exact Or.inl henq
      · exact Or.inr ⟨rfl, henq⟩
    · have hemp : ((progressResp p).events.filter fun e => f e.key).isEmpty = true := rfl
      simp only [hpn, Bool.false_eq_true, ↓reduceIte, hemp] at henq
      exact Or.inl henq.2

/-- A view's phase changes (active and lagging, or closed with a cancel at `n`). -/
theorem Delivered.phase {pred : Option (GoString → Bool)} {s : w64} {v : View}
    {sent : List RespModel} (hD : Delivered pred s v sent) (ph : RegPhase)
    (hph : ∀ m, ph = .closed (some m) → m = v.n) :
    Delivered pred s { v with phase := ph } sent := by
  exact { stream_ok := hD.stream_ok, stream_le := hD.stream_le, events := hD.events,
            ordered := hD.ordered, progress := hD.progress, start_le := hD.start_le,
            near := hD.near, cancel := hph }

/-- A mapped view brought up to a state extending its own (`Broadcast`): the batches added,
above the old `maxRev`, are not in `[s, n)` (`near`), and notifications sent stay below them. -/
theorem Delivered.refresh {pred : Option (GoString → Bool)} {s : w64} {v : View}
    {sent : List RespModel} {c c' : DemuxCore} (hD : Delivered pred s v sent)
    (hm : v.phase.mapped = true → v.stream = c.stream ∧ v.maxRev = c.maxRev)
    (hext : StreamExt c c') : Delivered pred s (refreshView c' v) sent := by
  unfold refreshView
  split
  · rename_i hmap
    obtain ⟨hst, hmx⟩ := hm hmap
    obtain ⟨bs, hs, hle, habove, hok, hle'⟩ := hext
    have hmxZ : sint.Z v.maxRev = sint.Z c.maxRev := by rw [hmx]
    have hbs : streamRange s v.n bs = [] := by
      unfold streamRange
      rw [List.filter_eq_nil_iff]
      intro b hb
      have := habove b hb
      rw [← hmx] at this
      simp only [decide_eq_true_eq, not_and, Int.not_lt]
      intro h1
      rcases hD.near with h | h
      · omega
      · rw [h]; omega
    exact { stream_ok := hok, stream_le := hle'
            events := by rw [hD.events, hs, ← hst, streamRange_append, hbs, List.append_nil]
            ordered := hD.ordered
            progress := fun r hr he => by
              obtain ⟨h1, h2⟩ := hD.progress r hr he
              refine ⟨by simp only; omega, fun b hb hnb => ?_⟩
              simp only at hb hnb ⊢
              rw [hs] at hb
              rcases List.mem_append.1 hb with hb | hb
              · exact h2 b (hst ▸ hb) hnb
              · have := habove b hb; omega
            start_le := hD.start_le
            near := by
              rcases hD.near with h | h
              · left; simp only; omega
              · right; exact h
            cancel := hD.cancel }
  · exact hD

/-- Sending the stream's events in `[v.n, n')` (non-empty) to a watcher: on success the
watcher is owed from `n'` on; on failure nothing was sent. (`n' ≤ maxRev + 1`.) -/
theorem Delivered.enqueue_events {pred : Option (GoString → Bool)} {s : w64} {v : View}
    {sent sent' : List RespModel} {ok : Bool} {n' : w64} (hD : Delivered pred s v sent)
    (hph : v.phase.mapped = true)
    (hn : sint.Z v.n ≤ sint.Z n') (hn' : sint.Z n' ≤ sint.Z v.maxRev + 1)
    (hne : (streamRange v.n n' v.stream).flatten ≠ [])
    (henq : enqueueResult pred (eventsResp (streamRange v.n n' v.stream).flatten) sent ok sent') :
    (ok = true → Delivered pred s { v with n := n' } sent') ∧ (ok = false → sent' = sent) := by
  have hsorted := hD.stream_ok.sorted
  have hcases := enqueue_events_cases hne henq
  have hsplit := streamRange_split (s := s) hsorted hD.start_le hn
  -- the new events are at or above `v.n`; the old ones below
  have hnew : ∀ e ∈ ((streamRange v.n n' v.stream).flatten).filter (keepEv pred),
      sint.Z v.n ≤ sint.Z e.rev ∧ ∃ b ∈ v.stream, e ∈ b ∧ e.rev = batchRev b ∧
        sint.Z v.n ≤ sint.Z (batchRev b) := by
    intro e he
    obtain ⟨b, hb, heb⟩ := List.mem_flatten.1 (List.mem_filter.1 he).1
    obtain ⟨hbst, h1, -⟩ := streamRange_mem hb
    have her := (hD.stream_ok.batches b hbst).2 e heb
    exact ⟨her ▸ h1, b, hbst, heb, her, h1⟩
  have hfacts : ∀ sent'', eventsOf sent'' = eventsOf sent ++
        ((streamRange v.n n' v.stream).flatten).filter (keepEv pred) →
      SentOrdered sent'' → (∀ r ∈ sent'', r.events = [] → r ∈ sent) →
      Delivered pred s { v with n := n' } sent'' := by
    intro sent'' hev hord hprog
    exact { stream_ok := hD.stream_ok, stream_le := hD.stream_le
            events := by
              rw [hev, hD.events]; simp only
              rw [hsplit, List.flatten_append, List.filter_append]
            ordered := hord
            progress := fun r hr he => by
              obtain ⟨h1, h2⟩ := hD.progress r (hprog r hr he) he
              exact ⟨h1, fun b hb hnb => h2 b hb (by simp only at hnb; omega)⟩
            start_le := by simp only; have := hD.start_le; omega
            near := Or.inl hn'
            cancel := fun m hm => by
              simp only at hm
              rw [hm] at hph; simp [RegPhase.mapped] at hph }
  constructor
  · intro hok
    rcases hcases with ⟨hf, -⟩ | ⟨-, hemp, hseq⟩ | ⟨-, r', rfl, hr'ev, hr'ne⟩
    · rw [hok] at hf; cases hf
    · rw [hseq]; exact hfacts sent (by rw [hemp, List.append_nil]) hD.ordered (fun r hr _ => hr)
    · refine hfacts _ (by rw [eventsOf_append, hr'ev]) ⟨?_, ?_⟩ ?_
      · rw [List.pairwise_append]
        refine ⟨hD.ordered.1, List.pairwise_singleton _ _, fun r hr r'' hr'' => ?_⟩
        rw [List.mem_singleton] at hr''; subst hr''
        refine ⟨fun e he e' he' => ?_, fun he e' he' => ?_, fun he => absurd he hr'ne⟩
        · obtain ⟨b, -, -, her, -, hlt⟩ := hD.mem_events hr he
          have := (hnew e' (hr'ev ▸ he')).1
          rw [her]; omega
        · obtain ⟨-, b, hb, heb, her, hnb⟩ := hnew e' (hr'ev ▸ he')
          have := (hD.progress r hr he).2 b hb hnb
          rw [her]; exact this
      · intro r hr
        rcases List.mem_append.1 hr with hr | hr
        · exact hD.ordered.2 r hr
        · rw [List.mem_singleton] at hr; subst hr; rw [hr'ev]
          exact (hD.stream_ok.sublist (List.filter_sublist ..)).flatten_sorted.sublist
            (List.filter_sublist ..)
      · intro r hr he
        rcases List.mem_append.1 hr with hr | hr
        · exact hr
        · rw [List.mem_singleton] at hr; subst hr; exact absurd he hr'ne
  · intro hok
    rcases hcases with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · rw [hok] at h; cases h
    · rw [hok] at h; cases h

/-- Sending a progress notification at `maxRev` to a watcher owed nothing (every stream batch is
below its `n`): the facts hold for the new log, and, on success, also with next revision `n'`
(`n ≤ n' ≤ maxRev + 1`: `broadcastProgressLocked`'s `progressRev + 1`, the resync's
`maxRev + 1`). -/
theorem Delivered.enqueue_progress {pred : Option (GoString → Bool)} {s : w64} {v : View}
    {sent sent' : List RespModel} {ok : Bool} {n' : w64} (hD : Delivered pred s v sent)
    (hph : v.phase.mapped = true)
    (hup : ∀ b ∈ v.stream, sint.Z (batchRev b) < sint.Z v.n)
    (hn : sint.Z v.n ≤ sint.Z n') (hn' : sint.Z n' ≤ sint.Z v.maxRev + 1)
    (henq : enqueueResult pred (progressResp v.maxRev) sent ok sent') :
    Delivered pred s v sent' ∧ (ok = true → Delivered pred s { v with n := n' } sent') := by
  have hcases := enqueue_progress_cases henq
  have hsame := streamRange_up (s := s) hup hn
  have hD' : Delivered pred s v sent' := by
    rcases hcases with rfl | ⟨-, rfl⟩
    · exact hD
    · exact { stream_ok := hD.stream_ok, stream_le := hD.stream_le
              events := by rw [eventsOf_append, hD.events]; simp [progressResp]
              ordered := by
                refine ⟨?_, ?_⟩
                · rw [List.pairwise_append]
                  refine ⟨hD.ordered.1, List.pairwise_singleton _ _, fun r hr r'' hr'' => ?_⟩
                  rw [List.mem_singleton] at hr''; subst hr''
                  refine ⟨fun _ _ e' he' => by simp [progressResp] at he',
                    fun _ e' he' => by simp [progressResp] at he', fun _ e he => ?_⟩
                  obtain ⟨b, hb, -, her, -, -⟩ := hD.mem_events hr he
                  have := hD.stream_le b hb
                  rw [her]; exact this
                · intro r hr
                  rcases List.mem_append.1 hr with hr | hr
                  · exact hD.ordered.2 r hr
                  · rw [List.mem_singleton] at hr; subst hr; exact List.Pairwise.nil
              progress := fun r hr he => by
                rcases List.mem_append.1 hr with hr | hr
                · exact hD.progress r hr he
                · rw [List.mem_singleton] at hr; subst hr
                  refine ⟨Int.le_refl _, fun b hb hnb => ?_⟩
                  have := hup b hb; omega
              start_le := hD.start_le, near := hD.near, cancel := hD.cancel }
  refine ⟨hD', fun _ => ?_⟩
  exact { stream_ok := hD'.stream_ok, stream_le := hD'.stream_le
          events := by rw [hD'.events]; simp only; rw [hsame]
          ordered := hD'.ordered
          progress := fun r hr he => by
            obtain ⟨h1, -⟩ := hD'.progress r hr he
            refine ⟨h1, fun b hb hnb => ?_⟩
            have := hup b hb; simp only at hnb; omega
          start_le := by simp only; have := hD.start_le; omega
          near := Or.inl hn'
          cancel := fun m hm => by
            simp only at hm
            rw [hm] at hph; simp [RegPhase.mapped] at hph }

/-- Sending a progress notification at `maxRev` to a watcher owed nothing: the facts hold for
the new log, with the same view (for a watcher whose next revision does not change, which may
be above `maxRev + 1`: a start in the future). -/
theorem Delivered.enqueue_progress_same {pred : Option (GoString → Bool)} {s : w64} {v : View}
    {sent sent' : List RespModel} {ok : Bool} (hD : Delivered pred s v sent)
    (hup : ∀ b ∈ v.stream, sint.Z (batchRev b) < sint.Z v.n)
    (henq : enqueueResult pred (progressResp v.maxRev) sent ok sent') :
    Delivered pred s v sent' := by
  rcases enqueue_progress_cases henq with rfl | ⟨-, rfl⟩
  · exact hD
  · exact { stream_ok := hD.stream_ok, stream_le := hD.stream_le
            events := by rw [eventsOf_append, hD.events]; simp [progressResp]
            ordered := by
              refine ⟨?_, ?_⟩
              · rw [List.pairwise_append]
                refine ⟨hD.ordered.1, List.pairwise_singleton _ _, fun r hr r'' hr'' => ?_⟩
                rw [List.mem_singleton] at hr''; subst hr''
                refine ⟨fun _ _ e' he' => by simp [progressResp] at he',
                  fun _ e' he' => by simp [progressResp] at he', fun _ e he => ?_⟩
                obtain ⟨b, hb, -, her, -, -⟩ := hD.mem_events hr he
                have := hD.stream_le b hb
                rw [her]; exact this
              · intro r hr
                rcases List.mem_append.1 hr with hr | hr
                · exact hD.ordered.2 r hr
                · rw [List.mem_singleton] at hr; subst hr; exact List.Pairwise.nil
            progress := fun r hr he => by
              rcases List.mem_append.1 hr with hr | hr
              · exact hD.progress r hr he
              · rw [List.mem_singleton] at hr; subst hr
                refine ⟨Int.le_refl _, fun b hb hnb => ?_⟩
                have := hup b hb; omega
            start_le := hD.start_le, near := hD.near, cancel := hD.cancel }

/-- A new registration's facts: nothing sent, view at the current state, next revision `n`
with `s ≤ n` and `n ≤ maxRev + 1 ∨ n = s`. -/
theorem Delivered.init (pred : Option (GoString → Bool)) (s : w64) (v : View)
    (hst : StreamOk v.stream) (hle : ∀ b ∈ v.stream, sint.Z (batchRev b) ≤ sint.Z v.maxRev)
    (hn : v.n = s) (hph : ∀ m, v.phase ≠ .closed (some m)) :
    Delivered pred s v [] := by
  subst hn
  exact { stream_ok := hst, stream_le := hle
          events := by
            show [] = _
            symm
            rw [List.filter_eq_nil_iff]
            intro e he
            obtain ⟨b, hb, -⟩ := List.mem_flatten.1 he
            obtain ⟨-, h1, h2⟩ := streamRange_mem hb
            omega
          ordered := ⟨List.Pairwise.nil, fun _ h => by cases h⟩
          progress := fun _ h => by cases h
          start_le := Int.le_refl _
          near := Or.inr rfl
          cancel := fun m h => absurd h (hph m) }

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-! ## Ghost lemmas -/

/-- The key filter's agreement. -/
theorem predIs_agree (pn : GName) (p1 p2 : Option (GoString → Bool)) :
    predIs (GF := GF) pn p1 ∗ predIs pn p2 ⊢ ▷ ⌜p1 = p2⌝ := by
  have himp : ∀ (a b : Bool), (internalEq (iprop(⌜a = true⌝) : IProp GF) iprop(⌜b = true⌝) : IProp GF) ⊢ ⌜a = b⌝ :=
    fun a b => (internalEq_iff _ _).trans (((and_mono pure_imp.2 pure_imp.2).trans pure_and.1).trans
      (pure_mono (fun ⟨h1, h2⟩ => by cases a <;> cases b <;> simp_all)))
  have hk : ∀ k : Option GoString, (predIs (GF := GF) pn p1 ∗ predIs pn p2 : IProp GF) ⊢
      ▷ ⌜predCode p1 k = predCode p2 k⌝ := by
    intro k
    unfold predIs
    iintro ⟨H1, H2⟩
    ihave Hk := saved_pred_agree pn _ _
      (fun k : Option GoString => iprop(⌜predCode p1 k = true⌝))
      (fun k : Option GoString => iprop(⌜predCode p2 k = true⌝)) k $$ H1 H2
    iapply (later_mono (himp _ _)) $$ Hk
  exact (forall_intro hk).trans (later_forall_2.trans (later_mono (pure_forall.2.trans
    (pure_mono (fun h => predCode_inj (funext h))))))

/-- An existential of fractional predicates whose witnesses agree is fractional. -/
theorem fractional_exists_agree {X : Type} (Φ : X → Qp → IProp GF) (hfrac : ∀ x, Fractional (Φ x))
    (hagree : ∀ x y q1 q2, Φ x q1 ∗ Φ y q2 ⊢ ⌜x = y⌝) :
    Fractional (fun q => iprop(∃ x, Φ x q)) where
  fractional p q := by
    constructor
    · iintro ⟨%x, H⟩
      icases ((hfrac x).fractional p q).1 $$ H with ⟨H1, H2⟩
      isplitl [H1]
      · iexists x; iexact H1
      · iexists x; iexact H2
    · refine (sep_exists_right.1).trans (exists_elim fun x => ?_)
      refine (sep_exists_left.1).trans (exists_elim fun y => ?_)
      refine (and_intro (hagree x y p q) .rfl).trans (pure_elim_left fun h => ?_)
      subst h
      exact ((hfrac x).fractional p q).2.trans (exists_intro (Ψ := fun x => Φ x (p + q)) x)

theorem ghostVar_half_fractional {A : Type} [Pos.Countable A] (γ : GName) (a : A) :
    Fractional (fun q : Qp => ghostVar (GF := GF) γ q.half a) where
  fractional p q := by
    rw [qp_half_add]
    exact (ghostVar_fractional γ a).fractional p.half q.half

theorem ghostMapAuth_half_fractional {K V : Type} [DecidableEq K] [Pos.Countable K]
    [Pos.Countable V] (γ : GName) (m : GMap K V) :
    Fractional (fun q : Qp => ghostMapAuth (GF := GF) γ q.half m) where
  fractional p q := by
    rw [qp_half_add]
    exact (ghostMapAuth_fractional γ m).fractional p.half q.half

theorem ownMap_fractional {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]
    (mref : Loc) (m : GMap K V) :
    Fractional (fun q : Qp => (ownMap (GF := GF) mref (DFrac.own q) m : IProp GF)) where
  fractional p q := by
    rw [ownMap_unseal]
    have hh := fun mv => (heapPointsto_fractional mref mv).fractional p q
    constructor
    · iintro H
      unfold ownMapDef
      iNamed H
      icases (hh mv).1 $$ Hown with ⟨H1, H2⟩
      isplitl [H1]
      · iexists mv, mp; simp only [named]; iframe H1; ipureintro; exact ⟨His_map, Hagree, Hdom, Hdefault⟩
      · iexists mv, mp; simp only [named]; iframe H2; ipureintro; exact ⟨His_map, Hagree, Hdom, Hdefault⟩
    · iintro ⟨H1, H2⟩
      unfold ownMapDef
      iNamedSuffix H1 "1"
      iNamedSuffix H2 "2"
      icombine Hown1 Hown2 gives % ⟨_, Hmv⟩
      subst Hmv
      iexists mv, mp
      simp only [named]
      isplitl [Hown1 Hown2]
      · iapply (hh mv).2; iframe
      ipureintro; exact ⟨His_map2, Hagree2, Hdom2, Hdefault2⟩

/-- `demuxLockRest`'s body, for a tuple of its witnesses. -/
def demuxRestBody (d : Loc) (γd : DemuxNames) (cap : Nat)
    (x : DemuxCore × GMap Loc RegInfo × GMap Loc View × Loc × Loc) (q : Qp) : IProp GF :=
  iprop(ghostVar γd.core q.half x.1 ∗ ghostMapAuth γd.reg q.half x.2.1 ∗
    ghostMapAuth γd.views q x.2.2.1 ∗
    demuxMinRevAddr d ↦{DFrac.own q} x.1.minRev ∗ demuxMaxRevAddr d ↦{DFrac.own q} x.1.maxRev ∗
    demuxActAddr d ↦{DFrac.own q} x.2.2.2.1 ∗ demuxLagAddr d ↦{DFrac.own q} x.2.2.2.2 ∗
    x.2.2.2.1 ↦${DFrac.own q} (actOf x.2.2.1) ∗ x.2.2.2.2 ↦${DFrac.own q} (lagOf x.2.2.1) ∗
    ownRingBuffer (demuxHistAddr d) cap (batchAt (hG := hG)) batchRev x.1.history (DFrac.own q) ∗
    ⌜DemuxInv cap x.1⌝ ∗ ⌜RegsOk x.1 x.1.stream.length x.2.1 x.2.2.1⌝)

theorem demuxLockRest_equiv (d : Loc) (γd : DemuxNames) (cap : Nat) (q : Qp) :
    demuxLockRest (hG := hG) d γd cap q ⊣⊢ iprop(∃ x, demuxRestBody d γd cap x q) := by
  constructor
  · iintro H
    unfold demuxLockRest
    iNamed H
    iexists (c, regs, views, actP, lagP)
    unfold demuxRestBody
    iframe
    ipureintro; exact ⟨Hinv, Hok⟩
  · iintro ⟨%x, H⟩
    unfold demuxRestBody
    icases H with ⟨Hcore, Hregs, Hviews, HminRev, HmaxRev, HactF, HlagF, Hact, Hlag, Hhist, %Hinv, %Hok⟩
    unfold demuxLockRest
    iexists x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2
    simp only [named]
    iframe
    ipureintro; exact ⟨Hinv, Hok⟩

theorem fractional_of_equiv {Φ Ψ : Qp → IProp GF} (h : ∀ q, Φ q ⊣⊢ Ψ q) [hΨ : Fractional Ψ] :
    Fractional Φ where
  fractional p q :=
    (h (p + q)).trans ((hΨ.fractional p q).trans (sep_congr (h p).symm (h q).symm))

theorem demuxRestBody_fractional (d : Loc) (γd : DemuxNames) (cap : Nat)
    (x : DemuxCore × GMap Loc RegInfo × GMap Loc View × Loc × Loc) :
    Fractional (demuxRestBody (hG := hG) d γd cap x) := by
  unfold demuxRestBody
  haveI := ghostVar_half_fractional (GF := GF) γd.core x.1
  haveI := ghostMapAuth_half_fractional (GF := GF) γd.reg x.2.1
  haveI : ∀ (l : Loc) (v : w64), Fractional (fun q : Qp => typedPointsto (GF := GF) l v (DFrac.own q)) :=
    fun l v => fractional_of_dfractional (fun dq => typedPointsto l v dq)
  haveI : ∀ (l : Loc) (v : Loc), Fractional (fun q : Qp => typedPointsto (GF := GF) l v (DFrac.own q)) :=
    fun l v => fractional_of_dfractional (fun dq => typedPointsto l v dq)
  haveI := ownMap_fractional (GF := GF) x.2.2.2.1 (actOf x.2.2.1)
  haveI := ownMap_fractional (GF := GF) x.2.2.2.2 (lagOf x.2.2.1)
  haveI := ownRingBuffer_fractional (GF := GF) (demuxHistAddr d) cap (batchAt (hG := hG)) batchRev
    x.1.history
  infer_instance

instance demuxLockRest_fractional (d : Loc) (γd : DemuxNames) (cap : Nat) :
    Fractional (demuxLockRest (hG := hG) d γd cap) := by
  haveI := fractional_exists_agree (demuxRestBody (hG := hG) d γd cap)
    (demuxRestBody_fractional d γd cap) (fun x y q1 q2 => by
      unfold demuxRestBody
      iintro ⟨⟨H1, R1, V1, -, -, A1, L1, -⟩, ⟨H2, R2, V2, -, -, A2, L2, -⟩⟩
      ihave %e1 := ghostVar_agree _ _ _ _ _ $$ H1 H2
      ihave %e2 := ghostMapAuth_agree _ _ _ _ _ $$ R1 R2
      ihave %e3 := ghostMapAuth_agree _ _ _ _ _ $$ V1 V2
      icombine A1 A2 gives %e4
      icombine L1 L2 gives %e5
      ipureintro
      obtain ⟨a1, b1, c1, d1, e1'⟩ := x
      obtain ⟨a2, b2, c2, d2, e2'⟩ := y
      simp_all)
  exact fractional_of_equiv (demuxLockRest_equiv d γd cap)

instance demuxLockInv_fractional (d : Loc) (γd : DemuxNames) (cap : Nat) :
    Fractional (demuxLockInv (hG := hG) d γd cap) := by
  unfold demuxLockInv
  haveI := demuxLockRest_fractional (hG := hG) d γd cap
  infer_instance

theorem qp_one_add_not_le (q : Qp) : ¬ ((1 : Qp) + q ≤ 1) := by
  intro h
  have h' : ((1 : Qp) + q).val ≤ (1 : Qp).val := h
  have := q.2
  simp at h'
  grind

theorem qp_add_one_not_le (q : Qp) : ¬ (q + (1 : Qp) ≤ 1) := by
  intro h
  have h' : (q + (1 : Qp)).val ≤ (1 : Qp).val := h
  have := q.2
  simp at h'
  grind

theorem ghostMapAuth_halves {K V : Type} [DecidableEq K] [Pos.Countable K] [Pos.Countable V]
    (γ : GName) (m : GMap K V) :
    (ghostMapAuth (GF := GF) γ 1 m : IProp GF) ⊣⊢
      ghostMapAuth γ (1 : Qp).half m ∗ ghostMapAuth γ (1 : Qp).half m := by
  conv => lhs; rw [← Qp.half_add_half 1]
  exact (ghostMapAuth_fractional γ m).fractional _ _

theorem ghostVar_halves {A : Type} [Pos.Countable A] (γ : GName) (q : Qp) (a : A) :
    (ghostVar (GF := GF) γ q a : IProp GF) ⊣⊢ ghostVar γ q.half a ∗ ghostVar γ q.half a := by
  conv => lhs; rw [← Qp.half_add_half q]
  exact (ghostVar_fractional γ a).fractional _ _

theorem ghostMapElem_halves {K V : Type} [DecidableEq K] [Pos.Countable K] [Pos.Countable V]
    (γ : GName) (k : K) (v : V) :
    (k ↪[γ] v : IProp GF) ⊣⊢ k ↪[γ]{#(1 : Qp).half} v ∗ k ↪[γ]{#(1 : Qp).half} v := by
  conv => lhs; rw [← Qp.half_add_half 1]
  exact (ghostMapElem_fractional k γ v).fractional _ _

theorem dfrac_own_one_op_invalid (dq : DFrac) : ¬ ✓ (DFrac.own 1 • dq) := by
  intro h
  have := DFrac.valid_own_op h
  have : (1 : Qp).val = 1 := rfl
  grind

/-- With the whole writer token, no slot is borrowed: take every registration's resources. -/
theorem slots_take_all (γd : DemuxNames) (regs : GMap Loc RegInfo) :
    ghostVar γd.wtok 1 () ∗ ([∗map] w ↦ ri ∈ regs, slotRes (hG := hG) γd w ri) ⊢
      ghostVar γd.wtok 1 () ∗ ([∗map] w ↦ ri ∈ regs, regRes γd w ri) := by
  induction regs using Std.LawfulFiniteMap.induction_on with
  | hemp =>
    iintro ⟨Hw, -⟩
    iframe Hw
    iapply BigSepM.bigSepM_empty.2
    iempintro
  | hins i x m hi IH =>
    rw [(BigSepM.bigSepM_insert (Φ := fun w ri => slotRes (hG := hG) γd w ri) hi).to_eq,
      (BigSepM.bigSepM_insert (Φ := fun w ri => regRes (hG := hG) γd w ri) hi).to_eq]
    iintro ⟨Hw, Hs, Hrest⟩
    unfold slotRes
    icases Hs with (Hr | ⟨Hb, -⟩)
    · icases IH $$ [Hw Hrest] with ⟨Hw, Hrest⟩
      · iframe
      iframe
    · ihave %Hv := ghostVar_valid_2 _ _ _ _ _ $$ Hw Hb
      exact absurd Hv.1 (qp_one_add_not_le _)

/-- Put every registration's resources back in the slots. -/
theorem slots_put_all (γd : DemuxNames) (regs : GMap Loc RegInfo) :
    ([∗map] w ↦ ri ∈ regs, regRes (hG := hG) γd w ri) ⊢
      ([∗map] w ↦ ri ∈ regs, slotRes γd w ri) := by
  apply BigSepM.bigSepM_mono
  intro w ri _
  unfold slotRes
  iintro H
  ileft
  iexact H

/-- After `Lock`: take every registration's resources from the slots (leaving the writer token
there), the core ghost variable's lock half, and the rest of `P 1`. -/
theorem demux_lock_acquire (d : Loc) (γd : DemuxNames) (cap : Nat) :
    isDemux (hG := hG) d γd cap ∗ ▷ demuxLockInv d γd cap 1 ∗ £ 2 ⊢
      |={⊤}=> ∃ (c : DemuxCore) (regs : GMap Loc RegInfo) (views : GMap Loc View),
        ghostVar γd.core (1 : Qp).half c ∗ demuxLocked d γd cap c c.stream.length regs views ∗
        ⌜DemuxInv cap c⌝ := by
  iintro ⟨#Hd, HP, Hlc⟩
  icases lc_split (n := 1) (m := 1) |>.1 $$ Hlc with ⟨Hlc1, Hlc2⟩
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 HP with HP
  unfold demuxLockInv
  icases HP with ⟨Hwtok, HR⟩
  unfold demuxLockRest
  iNamed HR
  unfold isDemux
  iNamed Hd
  iinv Hslots with Hs Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑demuxN) $$ Hlc2 Hs with Hs
  unfold demuxSlots
  icases Hs with (Hw1 | ⟨%regs', Hregs', Hsl⟩)
  · ihave %Hv := ghostVar_valid_2 _ _ _ _ _ $$ Hwtok Hw1
    exact absurd Hv.1 (qp_one_add_not_le _)
  ihave %Heq := ghostMapAuth_agree _ _ _ _ _ $$ Hregs Hregs'
  subst Heq
  icases slots_take_all γd regs $$ [Hwtok Hsl] with ⟨Hwtok, Hres⟩
  · iframe
  imod Hclose $$ [Hwtok] with -
  · inext; ileft; iexact Hwtok
  imodintro
  iexists c, regs, views
  iframe Hcore
  isplitl [Hregs Hregs' Hviews HminRev HmaxRev HactF HlagF Hact Hlag Hhist Hres]
  · unfold demuxLocked
    iexists actP, lagP
    simp only [named]
    iframe
    isplitl [Hregs Hregs']
    · icombine Hregs Hregs' as H
      iexact H
    ipureintro; exact Hok
  ipureintro; exact Hinv

/-- Before `Unlock`: put the registrations' resources back in the slots and take the writer
token. -/
theorem demux_lock_release (d : Loc) (γd : DemuxNames) (cap : Nat) (c : DemuxCore)
    (regs : GMap Loc RegInfo) (views : GMap Loc View) :
    isDemux (hG := hG) d γd cap ∗ ghostVar γd.core (1 : Qp).half c ∗
      demuxLocked d γd cap c c.stream.length regs views ∗ ⌜DemuxInv cap c⌝ ∗ £ 1 ⊢
      |={⊤}=> demuxLockInv d γd cap 1 := by
  iintro ⟨#Hd, Hcore, HL, %Hinv, Hlc⟩
  unfold demuxLocked
  iNamed HL
  unfold isDemux
  iNamed Hd
  iinv Hslots with Hs Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑demuxN) $$ Hlc Hs with Hs
  unfold demuxSlots
  icases Hs with (Hw1 | ⟨%regs', Hregs', Hsl⟩)
  · icases (ghostMapAuth_halves γd.reg regs).1 $$ Hregs with ⟨Hregs1, Hregs2⟩
    imod Hclose $$ [Hregs2 Hres] with -
    · inext; iright; iexists regs; iframe Hregs2; iapply slots_put_all; iexact Hres
    imodintro
    unfold demuxLockInv demuxLockRest
    iframe Hw1
    iexists c, regs, views, actP, lagP
    simp only [named]
    iframe
    ipureintro; exact ⟨Hinv, Hok⟩
  · ihave %Hv := ghostMapAuth_valid_2 _ _ _ _ _ $$ Hregs Hregs'
    exact absurd Hv.1 (qp_one_add_not_le _)

/-- Under a read lock (`P rfrac`), `w`'s registrant borrows its slot. -/
theorem demux_slot_borrow (d : Loc) (γd : DemuxNames) (cap : Nat) (w : Loc) (γ : WatcherNames)
    (pred : Option (GoString → Bool)) (s : w64) :
    isDemux (hG := hG) d γd cap ∗ demuxRegistered γd w γ pred s ∗
      ▷ demuxLockInv d γd cap sync.rfrac ∗ £ 2 ⊢
      |={⊤}=> ∃ pn : GName, predIs pn pred ∗ regRes γd w (RegInfo.mk γ s pn) ∗
        demuxLoan d γd cap w (RegInfo.mk γ s pn) := by
  iintro ⟨#Hd, Hreg, HP, Hlc⟩
  icases lc_split (n := 1) (m := 1) |>.1 $$ Hlc with ⟨Hlc1, Hlc2⟩
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 HP with HP
  unfold demuxLockInv
  icases HP with ⟨Hwtok, HR⟩
  icases (ghostVar_halves γd.wtok sync.rfrac ()).1 $$ Hwtok with ⟨Hwt1, Hwt2⟩
  unfold demuxRegistered
  icases Hreg with ⟨%pn, Hel, #Hpred⟩
  icases (ghostMapElem_halves γd.reg w (RegInfo.mk γ s pn)).1 $$ Hel with ⟨Hel1, Hel2⟩
  unfold isDemux
  iNamed Hd
  iinv Hslots with Hs Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑demuxN) $$ Hlc2 Hs with Hs
  unfold demuxSlots
  icases Hs with (Hw1 | ⟨%regs', Hregs', Hsl⟩)
  · ihave %Hv := ghostVar_valid_2 _ _ _ _ _ $$ Hw1 Hwt1
    exact absurd Hv.1 (qp_one_add_not_le _)
  ihave %Hlk := ghost_map_lookup $$ Hregs' Hel1
  icases (BigSepM.bigSepM_delete (Φ := fun w ri => slotRes (hG := hG) γd w ri) (m := regs') Hlk).1
    $$ Hsl with ⟨Hslot, Hsl⟩
  iunfold slotRes at Hslot
  icases Hslot with (Hr | ⟨-, Hbel⟩)
  · imod Hclose $$ [Hregs' Hsl Hwt2 Hel2] with -
    · inext; iright; iexists regs'; iframe Hregs'
      iapply (BigSepM.bigSepM_delete (Φ := fun w ri => slotRes (hG := hG) γd w ri) (m := regs') Hlk).2
      iframe Hsl
      iunfold slotRes
      iright; iframe
    imodintro
    iexists pn
    iframe Hpred Hr
    unfold demuxLoan
    iframe
  · icombine Hel1 Hel2 as Hel
    icombine Hel Hbel gives % ⟨Hv, -⟩
    exact absurd Hv (dfrac_own_one_op_invalid _)

/-- The registrant gives its slot back. -/
theorem demux_slot_return (d : Loc) (γd : DemuxNames) (cap : Nat) (w : Loc) (γ : WatcherNames)
    (pred : Option (GoString → Bool)) (s : w64) (pn : GName) :
    isDemux (hG := hG) d γd cap ∗ predIs pn pred ∗ regRes γd w (RegInfo.mk γ s pn) ∗
      demuxLoan d γd cap w (RegInfo.mk γ s pn) ∗ £ 1 ⊢
      |={⊤}=> demuxRegistered γd w γ pred s ∗ demuxLockInv d γd cap sync.rfrac := by
  iintro ⟨#Hd, #Hpred, Hr, HL, Hlc⟩
  unfold demuxLoan
  icases HL with ⟨Hwt1, Hel1, HR⟩
  unfold isDemux
  iNamed Hd
  iinv Hslots with Hs Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑demuxN) $$ Hlc Hs with Hs
  unfold demuxSlots
  icases Hs with (Hw1 | ⟨%regs', Hregs', Hsl⟩)
  · ihave %Hv := ghostVar_valid_2 _ _ _ _ _ $$ Hw1 Hwt1
    exact absurd Hv.1 (qp_one_add_not_le _)
  ihave %Hlk := ghost_map_lookup $$ Hregs' Hel1
  icases (BigSepM.bigSepM_delete (Φ := fun w ri => slotRes (hG := hG) γd w ri) (m := regs') Hlk).1
    $$ Hsl with ⟨Hslot, Hsl⟩
  iunfold slotRes at Hslot
  icases Hslot with (Hr' | ⟨Hwt2, Hel2⟩)
  · iunfold regRes at Hr Hr'
    iNamedSuffix Hr "1"
    iNamedSuffix Hr' "2"
    icombine Hview1 Hview2 gives % ⟨Hv, -⟩
    exact absurd Hv (dfrac_own_one_op_invalid _)
  imod Hclose $$ [Hregs' Hsl Hr] with -
  · inext; iright; iexists regs'; iframe Hregs'
    iapply (BigSepM.bigSepM_delete (Φ := fun w ri => slotRes (hG := hG) γd w ri) (m := regs') Hlk).2
    iframe Hsl
    iunfold slotRes
    ileft; iexact Hr
  imodintro
  unfold demuxRegistered demuxLockInv
  isplitl [Hel1 Hel2]
  · iexists pn
    iframe Hpred
    iapply (ghostMapElem_halves γd.reg w (RegInfo.mk γ s pn)).2
    iframe
  isplitl [Hwt1 Hwt2]
  · iapply (ghostVar_halves γd.wtok sync.rfrac ()).2
    iframe
  iexact HR

theorem refreshView_phase (c : DemuxCore) (v : View) : (refreshView c v).phase = v.phase := by
  unfold refreshView; split <;> rfl

/-- `regRes_refresh`, by induction on the registrations. -/
theorem regRes_refresh_gen (γd : DemuxNames) (c c' : DemuxCore) (hext : StreamExt c c')
    (regs : GMap Loc RegInfo) : ∀ (views : GMap Loc View),
    (∀ w v, views !! w = some v → v.phase.mapped = true →
      v.stream = c.stream ∧ v.maxRev = c.maxRev) →
    ghostMapAuth γd.views 1 views ∗ ([∗map] w ↦ ri ∈ regs, regRes (hG := hG) γd w ri) ⊢ |==>
      ∃ views', ghostMapAuth γd.views 1 views' ∗ ([∗map] w ↦ ri ∈ regs, regRes γd w ri) ∗
        ⌜∀ w, views' !! w = if (regs !! w).isSome then (views !! w).map (refreshView c')
          else views !! w⌝ := by
  induction regs using Std.LawfulFiniteMap.induction_on with
  | hemp =>
    intro views _
    iintro ⟨Ha, Hr⟩
    imodintro
    iexists views
    iframe
    ipureintro; intro w; rfl
  | hins i x m hi IH =>
    intro views hm
    have hi' : m !! i = none := hi
    rw [(BigSepM.bigSepM_insert (Φ := fun w ri => regRes (hG := hG) γd w ri) hi).to_eq]
    iintro ⟨Ha, Hx, Hm⟩
    imod IH views hm $$ [Ha Hm] with ⟨%views'', Ha, Hm, %Hv''⟩
    · iframe
    iunfold regRes at Hx
    iNamed Hx
    ihave %Hlk := ghost_map_lookup $$ Ha Hview
    have Hvi : views !! i = some v := by rw [Hv'' i, hi'] at Hlk; simpa using Hlk
    imod ghost_map_update (refreshView c' v) $$ Ha Hview with ⟨Ha, Hview⟩
    imodintro
    iexists GMap.insert i (refreshView c' v) views''
    iframe Ha
    isplitl [Hview Hwat Hm]
    · iframe Hm
      iunfold regRes
      iexists sent, refreshView c' v, pred
      simp only [named]
      rw [refreshView_phase]
      iframe
      iframe #
      ipureintro
      exact Hdel.refresh (hm i v Hvi) hext
    ipureintro
    intro w
    by_cases hw : i = w
    · subst hw
      rw [GMap.lookup_insert]
      have : (Std.PartialMap.insert m i x : GMap Loc RegInfo) !! i = some x :=
        GMap.lookup_insert _ _ _
      rw [this, Hvi]; rfl
    · rw [GMap.lookup_insert_ne _ _ hw, Hv'' w]
      have : (Std.PartialMap.insert m i x : GMap Loc RegInfo) !! w = m !! w :=
        GMap.lookup_insert_ne _ _ hw
      rw [this]

/-- The bulk update of `Broadcast`: every mapped watcher's view brought up to the new state. -/
theorem regRes_refresh (γd : DemuxNames) (regs : GMap Loc RegInfo) (views : GMap Loc View)
    (c c' : DemuxCore) (hdom : ∀ w, (regs !! w).isSome = (views !! w).isSome)
    (hm : ∀ w v, views !! w = some v → v.phase.mapped = true →
      v.stream = c.stream ∧ v.maxRev = c.maxRev)
    (hext : StreamExt c c') :
    ghostMapAuth γd.views 1 views ∗ ([∗map] w ↦ ri ∈ regs, regRes (hG := hG) γd w ri) ⊢ |==>
      (ghostMapAuth γd.views 1 (views.fmap (refreshView c')) ∗
        ([∗map] w ↦ ri ∈ regs, regRes γd w ri)) := by
  iintro H
  imod regRes_refresh_gen γd c c' hext regs views hm $$ H with ⟨%views', Ha, Hr, %Hv'⟩
  have heq : views' = views.fmap (refreshView c') := by
    apply GMap.ext; intro w
    show views' !! w = (views.fmap (refreshView c')) !! w
    rw [Hv' w, GMap.lookup_fmap, hdom w]
    cases views !! w <;> rfl
  subst heq
  imodintro
  iframe

/-- **The delivery fact at any time** (for `Cache.Watch`): under a read lock, `w`'s registrant
learns that what its consumer has received is a prefix of a log with the delivery facts. -/
theorem demux_watcher_delivered (d : Loc) (γd : DemuxNames) (cap : Nat) (w : Loc)
    (γ : WatcherNames) (pred : Option (GoString → Bool)) (s : w64)
    (received : List RespModel) :
    isDemux (hG := hG) d γd cap ∗ demuxRegistered γd w γ pred s ∗
      demuxLockInv d γd cap sync.rfrac ∗ watcherConsumer γ received ∗ £ 4 ⊢
      |={⊤}=> demuxRegistered γd w γ pred s ∗ demuxLockInv d γd cap sync.rfrac ∗
        watcherConsumer γ received ∗
        ⌜∃ (sent : List RespModel) (c : Option w64), received <+: sent ∧
          DeliveredLog pred s sent c⌝ := by
  iintro ⟨#Hd, Hreg, HP, Hcons, Hlc⟩
  icases lc_split (n := 2) (m := 2) |>.1 $$ Hlc with ⟨Hlc2, Hlc⟩
  icases lc_split (n := 1) (m := 1) |>.1 $$ Hlc with ⟨Hlc3, Hlc4⟩
  imod demux_slot_borrow d γd cap w γ pred s $$ [Hd Hreg HP Hlc2] with ⟨%pn, #Hpred, Hr, Hloan⟩
  · iframe Hd Hreg Hlc2; inext; iexact HP
  iunfold regRes at Hr
  icases Hr with ⟨%sent', %v', %pred', #Hw', #Hpred', Hview', Hwat', %Hdel'⟩
  ihave Heq : iprop(▷ ⌜pred = pred'⌝) $$ []
  · iapply predIs_agree pn pred pred'
    isplitl
    · iexact Hpred
    · iexact Hpred'
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc3 Heq with %Heq
  subst Heq
  -- the consumer's prefix, in the view's phase
  iunfold named at Hw' Hpred' Hview' Hwat'
  ihave Hpfx : iprop(|={⊤}=> watcherAt γ sent' v'.phase.toWatcher ∗ watcherConsumer γ received ∗
      ⌜∃ c, List.IsPrefix received sent' ∧ ∀ m, c = some m → m = v'.n⌝) $$ [Hwat' Hcons]
  · dsimp only
    cases hph : v'.phase with
    | active =>
      simp only [RegPhase.toWatcher, watcherAt]
      imod watcher_received_prefix w γ pred sent' received $$ [Hw' Hwat' Hcons]
        with ⟨Hwat', Hcons, %Hpre⟩
      · iframe Hwat' Hcons; iexact Hw'
      imodintro; iframe; ipureintro; exact ⟨none, Hpre, fun m h => by cases h⟩
    | lagging =>
      simp only [RegPhase.toWatcher, watcherAt]
      imod watcher_received_prefix w γ pred sent' received $$ [Hw' Hwat' Hcons]
        with ⟨Hwat', Hcons, %Hpre⟩
      · iframe Hwat' Hcons; iexact Hw'
      imodintro; iframe; ipureintro; exact ⟨none, Hpre, fun m h => by cases h⟩
    | closed c0 =>
      simp only [RegPhase.toWatcher, watcherAt]
      ihave #Hcl := Hwat'
      imod watcher_received_prefix_closed w γ pred sent' received c0 $$ [Hcons]
        with ⟨Hcons, %Hpre⟩
      · iframe Hcons; iframe #
      imodintro; iframe; iframe #; ipureintro
      exact ⟨c0, Hpre, fun m h => Hdel'.cancel m (by rw [hph, h])⟩
  imod Hpfx with ⟨Hwat', Hcons, %Hpfx⟩
  obtain ⟨c, Hpre, Hc⟩ := Hpfx
  imod demux_slot_return d γd cap w γ pred s pn $$ [Hd Hpred Hview' Hwat' Hloan Hlc4] with ⟨Hreg, HP⟩
  · iframe Hd Hpred Hloan Hlc4
    iunfold regRes
    iexists sent', v', pred
    simp only [named]
    iframe
    iframe #
    ipureintro; exact Hdel'
  imodintro
  iframe
  ipureintro
  exact ⟨sent', c, Hpre, v', Hdel', Hc⟩

end lemmas

end EtcdGrove
end Perennial
