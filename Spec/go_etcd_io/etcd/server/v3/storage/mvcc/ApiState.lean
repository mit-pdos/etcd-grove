/-
**mvcc's API, its pure part** (frozen 2026-11-03, `notes/mvcc-api-candidate.md`; the statements
`Api.lean` states over it): the store's abstract state and its steps, a transaction's view, a watch
response, a watcher in the stream's state, the stream's state, the watch guarantee (`wsRecvOk`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WatchRecv
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

/-! ## The abstract state (pure) -/

/-- **The store's abstract state**: the changes of every committed revision (the first two,
revisions `0` and `1`, `NewStore`'s, empty), the compaction revision (`-1`: never compacted), and
the revision being committed (notified to the watchers, not yet visible to reads). -/
structure MvccState where
  log : Log
  crev : Int
  pending : Option (List Change)

/-- The current (committed) revision. -/
def MvccState.rev (σ : MvccState) : Nat := σ.log.length - 1

/-- The history the watchers were sent: the log with the pending revision. -/
def MvccState.notifiedLog (σ : MvccState) : Log :=
  match σ.pending with
  | none => σ.log
  | some p => σ.log ++ [p]

/-- **A commit's first step**: the changes `pend` sent to the watchers (none: nothing pending). -/
def MvccState.notify (σ : MvccState) (pend : List Change) : MvccState :=
  { σ with pending := if pend = [] then none else some pend }

/-- **A commit's second step**: the pending revision committed (visible to reads). -/
def MvccState.commitPending (σ : MvccState) : MvccState :=
  { σ with log := commitLog σ.log (σ.pending.getD []), pending := none }

/-- A compaction at `r`. -/
def MvccState.compactTo (σ : MvccState) (r : Int) : MvccState := { σ with crev := r }

/-- A new store's state: revisions `0` and `1`, both empty, never compacted, nothing pending. -/
def mvccStart : MvccState := ⟨[[], []], -1, none⟩

/-- **The states a store goes through**: from `mvccStart`, a commit's two steps (of well-formed
changes, each delete of a key present: `LogWf`), compactions to a revision above the last and at
most the current one. -/
inductive MvccReachable : MvccState → Prop
  | start : MvccReachable mvccStart
  | notify (σ : MvccState) (pend : List Change) :
      MvccReachable σ → σ.pending = none → LogWf (σ.log ++ [pend]) → MvccReachable (σ.notify pend)
  | commit (σ : MvccState) : MvccReachable σ → MvccReachable σ.commitPending
  | compact (σ : MvccState) (r : Int) :
      MvccReachable σ → σ.pending = none → σ.crev < r → r ≤ (σ.rev : Int) →
      MvccReachable (σ.compactTo r)

/-- **A transaction's view**: a read transaction at the state `σ`, or a write transaction begun at
`σ` with the pending changes `pend`. -/
inductive MTxn where
  | read (σ : MvccState)
  | write (σ : MvccState) (pend : List Change)

/-- The state the transaction began at. -/
def MTxn.state : MTxn → MvccState
  | .read σ => σ
  | .write σ _ => σ

/-- Its pending changes (none for a read transaction). -/
def MTxn.pend : MTxn → List Change
  | .read _ => []
  | .write _ pend => pend

/-- The log its reads read: a write transaction's has its pending revision appended. -/
def MTxn.readLog : MTxn → Log
  | .read σ => σ.log
  | .write σ pend => σ.log ++ [pend]

/-- The revision its reads read at (`writeRev`: the pending one once it has a change). -/
def MTxn.readRev : MTxn → w64
  | .read σ => W64 (σ.rev : Int)
  | .write σ pend => W64 ((writeRev σ.log pend : Nat) : Int)

/-- **A watch response**, as the client sees it: its watcher's id (`-1`: the whole stream's
progress), its events, its revision and its compaction revision (`0`: none). -/
structure WResp where
  id : w64
  evs : List EvM
  rev : w64
  compactRev : w64

/-- The events the responses `rs` carried for the watcher `id`, in order. -/
def recvEvs (rs : List WResp) (id : w64) : List EvM :=
  ((rs.filter fun r => decide (r.id = id)).map WResp.evs).flatten

/-- **A watcher, in the stream's state**: its range, its filters' predicates (an event a predicate
holds of is not sent), its first revision, the number of responses the stream had sent when it
registered, and whether it is live (not cancelled). -/
structure WInfo where
  rg : WatchRange
  fs : List (EvM → Bool)
  lo : Nat
  k : Nat
  live : Bool

/-- **The watch stream's state**: its watchers by id, and whether it is closed. -/
structure StreamState where
  ws : GMap w64 WInfo
  closed : Bool

def StreamState.register (S : StreamState) (id : w64) (w : WInfo) : StreamState :=
  { S with ws := S.ws.insert id w }
def StreamState.close (S : StreamState) : StreamState := { S with closed := true }
def wsStart : StreamState := ⟨∅, false⟩
/-- A cancel of `id`: the watcher, if any, not live. -/
def StreamState.cancel (S : StreamState) (id : w64) : StreamState :=
  match S.ws !! id with
  | some w => { S with ws := S.ws.insert id { w with live := false } }
  | none => S

/-- **A watch's first revision**: the start revision, or at `0` the one after the state's. -/
def watchLo (σ : MvccState) (startRev : w64) : Nat :=
  if startRev = W64 0 then σ.log.length else sint.nat startRev

/-- **The revisions `[lo, c]` of `L` change each key at most once** (vacuous when `c < lo`). -/
def onceUpTo (L : Log) (lo : Nat) (c : Int) : Prop :=
  ∀ r : Nat, lo ≤ r → (r : Int) ≤ c → ((L.getD r []).map Change.key).Nodup

/-- **The watch guarantee** of the responses `rs` a consumer received, against the store's state
`σ` and the stream's `S` (the history the watchers see is the notified log `L`, with the revision
being committed):

1. each response: a watcher's (an id the stream has) unless it is the stream's `-1`; its events at
   or below its revision; its revision a revision of `L` (but a compaction response's); a compaction
   response a watcher's, without events, at revision `0`, its compaction revision positive and at
   most the store's (round 14, A3: client/v3 relies on the `0`); each event's revision positive, a
   put's creation revision and version too (round 16: the value facts the clients' models need, at
   the result, in place of a size bound on the history); a
   `-1` response is progress, at a positive revision;
2. each watcher (while `onceUpTo L w.lo σ.crev`) has received exactly its range's events of the
   revisions `[lo, hi)` of `L`, for some `hi`, those its filters keep;
3. such a watcher's progress (a response without events and not a compaction's, the `j`-th
   received, at revision `P`, its own, or the stream's `-1` when the watcher is live and registered
   before it was sent) comes after exactly its kept events up to `P`.

The condition of 2-3 is the case the code delivers exactly: a compaction at `c` keeps only the last
change of a key at `c`, and a watcher reading revision `c` after it gets only that one
(`issues/etcd-mvcc-watch-compact-rev-subrev-lost.md`); it holds for every watcher of a store whose
transactions change each key at most once (etcd's, whose gRPC layer rejects others), and while the
compaction revision is below the watcher's first (the tester, which never compacts). etcd's cost:
the history's revisions change each key at most once because its gRPC layer checks each request
(`checkIntervals`), a fact its proof must carry through raft to the apply. (Margin: when it fails,
the code still delivers a sub-list; not stated.) -/
def wsRecvOk (σ : MvccState) (S : StreamState) (rs : List WResp) : Prop :=
  (∀ r ∈ rs,
    (r.id ≠ W64 (-1) → (S.ws !! r.id).isSome) ∧
    (∀ ev ∈ r.evs, sint.Z ev.kv.modRev ≤ sint.Z r.rev) ∧
    (r.compactRev = W64 0 → sint.nat r.rev < σ.notifiedLog.length) ∧
    (r.compactRev ≠ W64 0 → r.evs = [] ∧ r.id ≠ W64 (-1) ∧ r.rev = W64 0 ∧
      0 < sint.Z r.compactRev ∧ sint.Z r.compactRev ≤ σ.crev) ∧
    (r.id = W64 (-1) → r.evs = [] ∧ r.compactRev = W64 0 ∧ 1 ≤ sint.Z r.rev) ∧
    (∀ ev ∈ r.evs, 0 < sint.Z ev.kv.modRev ∧
      (ev.del = false → 0 < sint.Z ev.kv.createRev ∧ 0 < sint.Z ev.kv.version))) ∧
  (∀ (id : w64) (w : WInfo), S.ws !! id = some w → onceUpTo σ.notifiedLog w.lo σ.crev →
    ∃ hi, hi ≤ σ.notifiedLog.length ∧
      recvEvs rs id = filtered w.fs (watchEvents σ.notifiedLog w.rg w.lo hi)) ∧
  (∀ (j : Nat) (r : WResp) (id : w64) (w : WInfo), rs[j]? = some r → r.evs = [] →
    r.compactRev = W64 0 → S.ws !! id = some w → onceUpTo σ.notifiedLog w.lo σ.crev →
    (r.id = id ∨ (r.id = W64 (-1) ∧ w.live = true ∧ w.k ≤ j)) →
    recvEvs (rs.take (j + 1)) id =
      filtered w.fs (watchEvents σ.notifiedLog w.rg w.lo (sint.nat r.rev + 1)))

/-- **A live key-value's values are positive** (round 16: its creation and modification revisions
and its version, a count of its puts since its creation, none wrapped): what makes etcd's own
comparators, which subtract (`txn/range.go:214-226`), order it, and what the clients' models of a
key-value assume (client/v3's `0 < version`). True of every live key-value of the store's states:
mvcc's own receipt bounds the changes it ever made. -/
def kvSortOk (e : EtcdKv) : Prop :=
  0 < sint.Z e.createRev ∧ 0 < sint.Z e.modRev ∧ 0 < sint.Z e.version

/-- **A state safe to sort** (round 15): at most `2 ^ 62` key-values (the premise of Perennial's
sort spec, its heapsort fallback's index arithmetic), each safe to sort. **The size bound is a temporary, local
assumption**: it exists only because of that limitation of Perennial's spec
(`notes/perennial-changes.md`, "`sort.Sort`'s size premise"), to go when Perennial's sort spec drops
it, so it is stated at the one place a range's results are produced (the `Range` contracts), not as
a law of the store's state that every client would thread (the user, 2026-11-03). The values' part
(`kvSortOk`) is not temporary: it is true of the store's values, and what makes etcd's own
comparators, which subtract, a strict weak order. -/
def stateOk (s : List EtcdKv) : Prop := s.length ≤ 2 ^ 62 ∧ ∀ e ∈ s, kvSortOk e

/-- **A backend, as the store sees it**: its ghost names, parameters and location. -/
structure BkRef where
  γB : backend.BNames
  P : backend.BParams
  b : Loc

/-- The namespace an implementation reserves (a stated departure from "no internal namespaces in
masks": a library with invariants must reserve one). -/
def mvccN : Namespace := nroot .@ "mvcc"


end api
end mvcc
end EtcdGrove
end Perennial
