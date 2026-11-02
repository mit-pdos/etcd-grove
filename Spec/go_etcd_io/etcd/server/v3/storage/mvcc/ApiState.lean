/-
mvcc's candidate API, its pure part (`Api.lean`'s vocabulary is over it): the store's abstract
state, a transaction's view, a watch response, a watcher in the registrar's view.
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

/-- **What the watchers must have been taken care of for** (`mvccWatchersOk`): a commit of
`pend` after `σ` (notified), or a restore (reset). -/
inductive MvccOp where
  | commit (σ : MvccState) (pend : List Change)
  | restore

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

/-- **A watcher, in the registrar's view**: its range (`watchRangeOf`), its filters' predicates,
its first revision, its registration after the first `k` responses the stream sent, and whether it
is live (not cancelled). Its id is its position in the view (the stream assigns ids `0, 1, ...`). -/
structure WInfo where
  rg : WatchRange
  fs : List (EvM → Bool)
  lo : Nat
  k : Nat
  live : Bool

/-- **The registrar's view after a cancel of `id`**: the watcher, if any, not live. -/
def wsCancel (W : GMap w64 WInfo) (id : w64) : GMap w64 WInfo :=
  match W !! id with
  | some w => W.insert id { w with live := false }
  | none => W

/-- The namespace an implementation reserves for its invariants. -/
def mvccN : Namespace := nroot .@ "mvcc"

end mvcc
end EtcdGrove
end Perennial
