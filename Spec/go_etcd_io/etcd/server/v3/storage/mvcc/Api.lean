/-
**Candidate API of etcd's mvcc store** (2026-11-01, branch `worktree-mvcc-rand-tester`; for
review, not proved, no proof uses it): the vocabulary the candidate specs `<F>.specC` of this
directory's spec files are written in, and the laws an implementation must prove of it
(`<name>.law : Prop`, stated, not assumed: no axiom). Design and decisions:
`notes/mvcc-api-candidate.md`.

The vocabulary is abstract: no ghost name, certificate, revision token or reader slot of the
implementation. Linearizability is the caller's atomic update over the store's abstract state
(`mvccState γ σ`, owned by the client, as the server's `kvState`):

* **the state** `σ : MvccState`: the history of every revision (`σ.log`, mvcc's `Log`: revision
  `r`'s changes at `σ.log[r]`, the state at `r` is `stateAt σ.log r`, the current revision
  `σ.rev = σ.log.length - 1`) and the compaction revision `σ.crev` (`-1`: none). A write commits
  the next revision's changes (`σ.commit pend`); a compaction raises `crev` (`σ.compactTo r`).
  Compacted revisions stay in the model (reads of them fail with `ErrCompacted`).
* **a read** (`Read`, `Rev`) fires the caller's update at the state it reads, unchanged;
* **a write transaction** (`Write` ... `End`) holds the writer's lock: it is pinned to the state
  `σ` it began at (`mvccTxn_write_agree`: no other write, no compaction, can change the state
  before its `End`), its operations extend its pending changes, and its `End` commits them by the
  caller's update;
* **watch events** may be ahead of the committed state by the revision being committed (the
  watchable store notifies before it bumps the revision: a read that starts after an event was
  received may still see the revision before it): they come from a log the client **announced**
  (`mvccAnn`, the client's own map from revisions to logs; `watchableStoreTxnWrite.End` takes the
  announcement of the log it commits), so the client relates them to its own records.
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

/-- **The store's abstract state**: the changes of every revision, the first two (revisions `0`
and `1`, `NewStore`'s) empty, and the compaction revision (`-1`: never compacted). -/
structure MvccState where
  log : Log
  crev : Int

/-- The current revision. -/
def MvccState.rev (σ : MvccState) : Nat := σ.log.length - 1

/-- A write transaction's commit of its pending changes `pend` (no revision if there are none). -/
def MvccState.commit (σ : MvccState) (pend : List Change) : MvccState :=
  { σ with log := commitLog σ.log pend }

/-- A compaction at `r`. -/
def MvccState.compactTo (σ : MvccState) (r : Int) : MvccState := { σ with crev := r }

/-- A new store's state: revisions `0` and `1`, both empty, never compacted. -/
def mvccStart : MvccState := ⟨[[], []], -1⟩

/-- **The states a store goes through**: from `mvccStart`, commits of well-formed changes (each
delete of a key present: `LogWf`) and compactions to a revision above the last and at most the
current one. -/
inductive MvccReachable : MvccState → Prop
  | start : MvccReachable mvccStart
  | commit (σ : MvccState) (pend : List Change) :
      MvccReachable σ → LogWf (σ.log ++ [pend]) → MvccReachable (σ.commit pend)
  | compact (σ : MvccState) (r : Int) :
      MvccReachable σ → σ.crev < r → r ≤ (σ.rev : Int) → MvccReachable (σ.compactTo r)

/-- **A transaction's view**: a read transaction at the state `σ`, or a write transaction begun
at `σ` with the pending changes `pend`. -/
inductive MTxn where
  | read (σ : MvccState)
  | write (σ : MvccState) (pend : List Change)

/-- The state the transaction began at. -/
def MTxn.state : MTxn → MvccState
  | .read σ => σ
  | .write σ _ => σ

/-- The log its reads read: a write transaction's has its pending revision appended. -/
def MTxn.readLog : MTxn → Log
  | .read σ => σ.log
  | .write σ pend => σ.log ++ [pend]

/-- Its pending changes (none for a read transaction). -/
def MTxn.pend : MTxn → List Change
  | .read _ => []
  | .write _ pend => pend

/-- The revision its reads read at (`writeRev`: the pending one once it has a change). -/
def MTxn.readRev : MTxn → w64
  | .read σ => W64 (σ.rev : Int)
  | .write σ pend => W64 ((writeRev σ.log pend : Nat) : Int)

/-- **What a `Cancel`'s caller knows of the id**: a live watcher whose token it holds, an id its
registrar's view does not have, or a watcher already cancelled. -/
inductive CancelBy where
  | live
  | unknown
  | dead

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

/-! ## The vocabulary (an implementation defines it) -/

/-- A store's name: what its abstract state and its handles are indexed by. -/
opaque MvccName : Type := Unit

/-- A watch stream's name. -/
opaque WsName : Type := Unit

/-- **The store's lessor's ghost name** (its `lease.leaseOwn`). -/
opaque mvccLeases (γ : MvccName) : GName := default

/-- Some backend names (for `mvccBackend`'s declaration only). -/
local instance : Inhabited backend.BNames :=
  ⟨by constructor <;> first | exact default | (constructor <;> exact default)⟩

/-- **The store's backend's ghost names** (its `backend.wbTok`, `backend.plHookRO`). -/
opaque mvccBackend (γ : MvccName) : backend.BNames := default

/-- **Whether the store has watchers** (it is a watchable store's: `New`; or `NewStore` at the
watched mode): its mode, fixed at its creation. -/
opaque mvccWatched (γ : MvccName) : Bool := false

/-- **The hash of the revisions `(lo, hi]` of a history**, as the store computes it (a function of
the history: two stores with the same history give the same hash; its value is crc32's over the
revisions' keys and key-values, kept by the compaction at `lo`). -/
opaque mvccHashOf (log : Log) (lo hi : Int) : w32 := W32 0

/-- The namespace an implementation reserves for its invariants. -/
def mvccN : Namespace := nroot .@ "mvcc"

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The store's state is `σ`** (exclusive, timeless; the client's, what its atomic updates are
over). -/
opaque mvccState (γ : MvccName) (σ : MvccState) : IProp GF := iprop(True)

/-- **`s` (a `*store`) serves the store `γ`** (persistent). -/
opaque isMvcc (s : Loc) (γ : MvccName) : IProp GF := iprop(True)

/-- **`ws` (a `*watchableStore`) serves the store `γ`** (persistent). -/
opaque isWatchableMvcc (ws : Loc) (γ : MvccName) : IProp GF := iprop(True)

/-- **A share `q` of the store's open token** (fractional): `Compact` takes a share (after
`Close` the scheduler is stopped, and a compaction's `Schedule` panics); `watchableStore.Close`
takes it whole. -/
opaque mvccOpen (γ : MvccName) (q : Qp) : IProp GF := iprop(True)

/-- **The store's backend is `b`, with parameters `P` and batch-lock resource `Pk`**
(persistent; from `New`): what the backend's commit request (`backend.commitReq`) is over. -/
opaque mvccBackendIs (γ : MvccName) (P : backend.BParams) (Pk : IProp GF) (b : Loc) : IProp GF :=
  iprop(True)

/-- **The store's batch lock has invariant `P`** (persistent; fixed by its backend's creator). -/
opaque mvccHookInit (γ : MvccName) (P : IProp GF) : IProp GF := iprop(True)

/-- **The store's batch lock has invariant `P` and its post-lock hook is `f`, for good**
(persistent; `f` may be `nil`: no hook). -/
opaque mvccHook (γ : MvccName) (P : IProp GF) (f : GoFunc) : IProp GF := iprop(True)

/-- **The client's announcements**: its authority over the map `M` from a revision to the log
it announced for it (exclusive). -/
opaque mvccAnnAuth (γ : MvccName) (M : GMap Nat Log) : IProp GF := iprop(True)

/-- **The client announced the log `L` for the revision `r`** (persistent). -/
opaque mvccAnn (γ : MvccName) (r : Nat) (L : Log) : IProp GF := iprop(True)

/-- **`t` (a `*metricsTxnWrite`) is a transaction of `γ`** with the view `k`, holding the
caller's trace `trace` (exclusive). -/
opaque mvccTxn (t : Loc) (γ : MvccName) (trace : Loc) (k : MTxn) : IProp GF := iprop(True)

/-- **`t` (a `*txnReadWrite`) is the read-only write transaction of a read transaction at `σ`**
(`NewReadOnlyTxnWrite`; exclusive). -/
opaque mvccRoTxn (t : Loc) (γ : MvccName) (trace : Loc) (σ : MvccState) : IProp GF := iprop(True)

/-- **`tw` (a `*watchableStoreTxnWrite`) is the watchable store's write transaction over the
transaction `mw`** (persistent: its fields). -/
opaque mvccWatchTxnOf (tw mw : Loc) : IProp GF := iprop(True)

/-- **`rd` is the range deleter the store set on its lessor**: `rd()` is the store's
`Write(TODO)`, the watchable store's if it has watchers (persistent; `mvccDeleter_spec`). -/
opaque mvccDeleter (rd : GoFunc) (γ : MvccName) : IProp GF := iprop(True)

/-- **The watchers were notified of the commit of `pend` after `σ`** (or the store has none):
what a write transaction's own `End` takes. A store without watchers gives it freely
(`mvccNotified_unwatched`); a watched store's is made only by the watchable store's `End`, which
notifies: so a client of a watched store commits through that `End`. -/
opaque mvccNotified (γ : MvccName) (σ : MvccState) (pend : List Change) : IProp GF := iprop(True)

/-- **The watchers were reset for a restore** (or the store has none): what the store's own
`Restore` takes (as `mvccNotified`; the watchable store's `Restore` resets them). -/
opaque mvccRestoreOk (γ : MvccName) : IProp GF := iprop(True)

/-- **The right to wrap the store `s` in a watchable store** (exclusive; `NewStore` at the
watched mode gives it, `New`'s watchable store takes it): it holds the store's `ReadView` and
`WriteView` fields, which the watchable store overwrites with its own views. -/
opaque mvccWrapRight (γ : MvccName) (s : Loc) : IProp GF := iprop(True)

/-- **`rv` is a read view of the store `γ`** (persistent): its `kv` serves `γ` (the store, or its
watchable store). -/
opaque isReadViewOf (rv : Loc) (γ : MvccName) : IProp GF := iprop(True)

/-- **`wv` is a write view of the store `γ`** (persistent): its `kv` serves `γ`, through the
watchable store if `γ` has watchers. -/
opaque isWriteViewOf (wv : Loc) (γ : MvccName) : IProp GF := iprop(True)

/-- **The backend `b` holds the state `σ`, and the store `γ` may restore from it** (exclusive:
the backend's creator's resources, as today's `store.Restore` takes them; the backend boundary is
open, `notes/mvcc-api-candidate.md`). -/
opaque mvccRestorable (γ : MvccName) (b : Loc) (σ : MvccState) : IProp GF := iprop(True)

/-- **`hs` (a `*hashStorage`) is the store `γ`'s hash storage** (persistent). -/
opaque isHashStorage (hs : Loc) (γ : MvccName) : IProp GF := iprop(True)

/-- **`h` is a hash of the store `γ`** (persistent): of the revisions `(h.CompactRevision,
h.Revision]` of its history (`mvccHashOk_state`). -/
opaque mvccHashOk (γ : MvccName) (h : KeyValueHash) : IProp GF := iprop(True)

/-- **The backend's commit serves the request `X ⇒ Y`** (the backend's hooks; for a backend
without hooks, `X -∗ Y`). -/
opaque mvccCommitReq (γ : MvccName) (X Y : IProp GF) : IProp GF := iprop(True)

/-- **`ch` is a compaction's channel**: a receive on it returns (persistent). -/
opaque mvccCompactChan (ch : GoChan) : IProp GF := iprop(True)

/-- **`ws` (a `*watchStream`) is a watch stream of the store `γ`, named `ι`** (persistent). -/
opaque isMvccWatchStream (ws : Loc) (γ : MvccName) (ι : WsName) : IProp GF := iprop(True)

/-- **A share `q` of the stream's open token** (fractional): `Close` takes it whole; a holder of
a share knows the stream is not closed (`wsOpen_closed`). -/
opaque wsOpen (ι : WsName) (q : Qp) : IProp GF := iprop(True)

/-- **The stream was closed** (persistent; from `Close`): `Watch` then fails. -/
opaque wsClosed (ι : WsName) : IProp GF := iprop(True)

/-- **The registrar's view of the stream's watchers**: the ids `S` of every watcher `Watch`
registered on it (exclusive; the goroutine that calls `Watch`). -/
opaque wsWatchers (ι : WsName) (S : List w64) : IProp GF := iprop(True)

/-- **The watcher `id` is live** (exclusive; from `Watch`, taken by `Cancel`): a live watcher was
not cancelled (`wsLive_canceled`). -/
opaque wsLive (ι : WsName) (id : w64) : IProp GF := iprop(True)

/-- **`ch` is the stream's channel** (persistent). -/
opaque wsChan (ι : WsName) (ch : GoChan) : IProp GF := iprop(True)

/-- **The consumer has received the responses `rs`** from the stream's channel, in order
(exclusive). -/
opaque wsRecv (ι : WsName) (rs : List WResp) : IProp GF := iprop(True)

/-- **The stream's watcher `id`** (persistent): its range `rg` (`watchRangeOf`), its filters'
predicates `fs`, its first revision `lo`, and its registration after the first `k` responses
the stream sent. -/
opaque wsWatcher (ι : WsName) (id : w64) (rg : WatchRange) (fs : List (EvM → Bool)) (lo k : Nat) :
    IProp GF := iprop(True)

/-- **The watcher `id` was cancelled** (persistent). -/
opaque wsCanceled (ι : WsName) (id : w64) : IProp GF := iprop(True)

/-- **The `WatchResponse` value `v` is the response `r`**: its id, revision and compaction
revision, its events a read-only slice of `r`'s events (persistent). -/
def wrespIs (v : WatchResponse) (r : WResp) : IProp GF :=
  iprop(⌜v.WatchID' = r.id ∧ v.Revision' = r.rev ∧ v.CompactRevision' = r.compactRev⌝ ∗
    ∃ ps : List Loc, v.Events' ↦*□ ps ∗ ⌜ps.length = r.evs.length⌝ ∗
      [∗list] x ∈ ps.zip r.evs, evIs x.1 x.2)

/-- **A log the client may watch events of**: a prefix of a new store's, or one it announced. -/
def mvccLogOk (γ : MvccName) (L : Log) : IProp GF :=
  iprop(⌜L <+: mvccStart.log⌝ ∨ mvccAnn γ (L.length - 1) L)

/-- **The store's lessor** `le`, at an interface value of any type, with the lessor's ghost
name `γl` (its owner's `lease.leaseOwn γl L I`: the live leases `L`, the item map `I`):
`GetLease(item)` returns the item map's lease of `item` (`NoLease` if none), with the resource `R`
(the real lessor's: a reader slot of its lock); `Attach(id, items)` of a live lease (`id ∈ L`) of
items on no other lease, each key shorter than `2 ^ 63 - 1` (the real lessor's proof's
invariant `itemKeysShort`, not a need of its Go code), adds them to
the item map; `Detach(id, items)` of items the item map puts on `id` removes them;
`SetRangeDeleter(f)` sets the deleter, by its owner (`lease.rdOwn γl`). Today's `isLessor` with the
real `*lessor`'s pin dropped and its reader slot a parameter. The generality is nominal for now:
`lease.leaseOwn` is the real lessor's state, so another implementation (`FakeLessor`) cannot meet
it without its own owner predicate (open, `notes/mvcc-api-candidate.md`). -/
def isMvccLessor (le : GoInterface) (γl : GName) (R : IProp GF) : IProp GF :=
  iprop(∃ li : GoInterfaceOk, ⌜le = GoInterface.ok li⌝ ∗
    □ (∀ (item : go_etcd_io.etcd.server.v3.lease.LeaseItem) (L : List w64)
        (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64),
      {{ R ∗ lease.leaseOwn γl L I }}
        (App (Val #(methods li.ty go!"GetLease" li.v)) (Val #item))
      {{ RET #((I.lookup item).getD (W64 0)); R ∗ lease.leaseOwn γl L I }}) ∗
    □ (∀ (id : w64) (items : GoSlice) (l : List go_etcd_io.etcd.server.v3.lease.LeaseItem)
        (dq : DFrac) (L : List w64) (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64),
      {{ lease.leaseOwn γl L I ∗ ⌜id ∈ L⌝ ∗
          ⌜∀ it ∈ l, I.lookup it = none ∨ I.lookup it = some id⌝ ∗
          ⌜∀ it ∈ l, (it.Key'.length : Int) < 2 ^ 63 - 1⌝ ∗ items ↦*{dq} l }}
        (App (App (Val #(methods li.ty go!"Attach" li.v)) (Val #id)) (Val #items))
      {{ RET #(GoInterface.nil); lease.leaseOwn γl L (lease.insertAll I l id) ∗ items ↦*{dq} l }}) ∗
    □ (∀ (id : w64) (items : GoSlice) (l : List go_etcd_io.etcd.server.v3.lease.LeaseItem)
        (dq : DFrac) (L : List w64) (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64),
      {{ lease.leaseOwn γl L I ∗ ⌜l ≠ []⌝ ∗ ⌜∀ it ∈ l, I.lookup it = some id⌝ ∗ items ↦*{dq} l }}
        (App (App (Val #(methods li.ty go!"Detach" li.v)) (Val #id)) (Val #items))
      {{ RET #(GoInterface.nil); lease.leaseOwn γl L (lease.deleteAll I l) ∗ items ↦*{dq} l }}) ∗
    □ (∀ (f0 f : GoFunc),
      {{ lease.rdOwn γl f0 }}
        (App (Val #(methods li.ty go!"SetRangeDeleter" li.v)) (Val #f))
      {{ RET #(); lease.rdOwn γl f }}))

/-- **What a write's hook does** under the batch lock of invariant `P`, from the caller's `Pre`:
`f`'s triple to `Q`, or with no hook (`nil`), the caller's update. -/
def hookRun (P : IProp GF) (f : GoFunc) (Pre Q : IProp GF) : IProp GF :=
  if f = func.nil then iprop(P ∗ Pre ={⊤}=∗ Q)
  else iprop(□ ({{ P ∗ Pre }} (App (Val #f) (Val #())) {{ RET #(); Q }}))

end vocab

/-! ## The laws (an implementation proves them) -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The persistent, timeless and fractional predicates are. -/
abbrev mvcc.persistent.law : Prop :=
  (∀ s γ, Persistent (isMvcc (GF := GF) s γ)) ∧ (∀ ws γ, Persistent (isWatchableMvcc (GF := GF) ws γ)) ∧
  (∀ γ P, Persistent (mvccHookInit (GF := GF) γ P)) ∧ (∀ γ P f, Persistent (mvccHook (GF := GF) γ P f)) ∧
  (∀ γ P Pk b, Persistent (mvccBackendIs (GF := GF) γ P Pk b)) ∧
  (∀ γ r L, Persistent (mvccAnn (GF := GF) γ r L)) ∧ (∀ tw mw, Persistent (mvccWatchTxnOf (GF := GF) tw mw)) ∧
  (∀ rd γ, Persistent (mvccDeleter (GF := GF) rd γ)) ∧ (∀ ch, Persistent (mvccCompactChan (GF := GF) ch)) ∧
  (∀ rv γ, Persistent (isReadViewOf (GF := GF) rv γ)) ∧ (∀ wv γ, Persistent (isWriteViewOf (GF := GF) wv γ)) ∧
  (∀ hs γ, Persistent (isHashStorage (GF := GF) hs γ)) ∧ (∀ γ h, Persistent (mvccHashOk (GF := GF) γ h)) ∧
  (∀ γ σ pend, Persistent (mvccNotified (GF := GF) γ σ pend)) ∧ (∀ γ, Persistent (mvccRestoreOk (GF := GF) γ)) ∧
  (∀ ws γ ι, Persistent (isMvccWatchStream (GF := GF) ws γ ι)) ∧ (∀ ι ch, Persistent (wsChan (GF := GF) ι ch)) ∧
  (∀ ι id rg fs lo k, Persistent (wsWatcher (GF := GF) ι id rg fs lo k)) ∧
  (∀ ι id, Persistent (wsCanceled (GF := GF) ι id)) ∧ (∀ ι, Persistent (wsClosed (GF := GF) ι)) ∧
  (∀ γ σ, Timeless (mvccState (GF := GF) γ σ)) ∧ (∀ γ M, Timeless (mvccAnnAuth (GF := GF) γ M)) ∧
  (∀ ι rs, Timeless (wsRecv (GF := GF) ι rs)) ∧ (∀ ι S, Timeless (wsWatchers (GF := GF) ι S)) ∧
  (∀ ι, Fractional (wsOpen (GF := GF) ι)) ∧ (∀ γ, Fractional (mvccOpen (GF := GF) γ))

/-- The state is exclusive. -/
abbrev mvccState_excl.law : Prop :=
  ∀ γ σ σ', mvccState (GF := GF) γ σ ∗ mvccState γ σ' ⊢ False

/-- **Every state of a store is reachable**, and its revisions fit an `int64` with room to spare
(its changes are fewer than the time receipts, `New`'s `receiptBound GF ≤ 2 ^ 48`). -/
abbrev mvccState_reachable.law : Prop :=
  ∀ s γ σ, isMvcc (GF := GF) s γ ∗ mvccState γ σ ⊢ ⌜MvccReachable σ ∧ σ.log.length < 2 ^ 62⌝

/-- **A write transaction pins the state** it began at, until its `End`. -/
abbrev mvccTxn_write_agree.law : Prop :=
  ∀ t γ trace σ pend σ', mvccTxn (GF := GF) t γ trace (.write σ pend) ∗ mvccState γ σ' ⊢ ⌜σ' = σ⌝

/-- **The caller's trace, while its transaction is open** (to step and annotate it). -/
abbrev mvccTxn_trace.law : Prop :=
  (∀ t γ trace k, mvccTxn (GF := GF) t γ trace k ⊢
    (∃ te, traceutil.ownTrace trace te) ∗ ((∃ te, traceutil.ownTrace trace te) -∗ mvccTxn t γ trace k)) ∧
  (∀ t γ trace σ, mvccRoTxn (GF := GF) t γ trace σ ⊢
    (∃ te, traceutil.ownTrace trace te) ∗ ((∃ te, traceutil.ownTrace trace te) -∗ mvccRoTxn t γ trace σ))

/-- **The watchable store's store** (its embedded `*store`, which serves its promoted `Read`,
`Rev`, `Compact` and `Commit`; the store has no committing spec of its own: every write goes
through the watchable store's, which notifies the watchers). -/
abbrev isWatchableMvcc_store.law : Prop :=
  ∀ ws γ, isWatchableMvcc (GF := GF) ws γ ⊢
    ∃ s : Loc, ws.[watchableStore, go!"store"] ↦□ s ∗ isMvcc s γ

/-- **The watchable store's write transaction `tw` over `mw`**: its embedded `TxnWrite` is `mw`
(which serves its promoted `Put`, `DeleteRange`, `Range`, `Rev` and `Changes`; `mw`'s `End`, which
would commit without notifying, has no write spec). -/
abbrev mvccWatchTxnOf_field.law : Prop :=
  ∀ tw mw, mvccWatchTxnOf (GF := GF) tw mw ⊢
    tw.[watchableStoreTxnWrite, go!"TxnWrite"] ↦□
      (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw : GoInterface)

/-- **The hook frozen** on the store's backend (`backend.plHookRO`, by `plHook_persist` after
`SetTxPostLockInsideApplyHook`, or the new backend's `nil`) is the store's. -/
abbrev mvccHook_of_init.law : Prop :=
  ∀ γ P f, mvccHookInit (GF := GF) γ P ∗ backend.plHookRO (mvccBackend γ) f ⊢ mvccHook γ P f

/-- The hook is one. -/
abbrev mvccHook_agree.law : Prop :=
  ∀ γ P P' f f', mvccHook (GF := GF) γ P f ∗ mvccHook γ P' f' ⊢ ⌜f = f'⌝

/-- **The commit request**: the backend's (`backend.commitReq` over the store's backend). For a
backend without hooks, the backend gives it from a wand. -/
abbrev mvccCommitReq_of.law : Prop :=
  ∀ γ P Pk b X Y, mvccBackendIs (GF := GF) γ P Pk b ∗ backend.commitReq (mvccBackend γ) P Pk b X Y ⊢
    mvccCommitReq γ X Y

/-- **The range deleter** the store set on its lessor is the store's `Write(traceutil.TODO())`,
the watchable store's if it has watchers: a write transaction (as `store.Write.specC` or
`watchableStore.Write.specC`, at a trace of its own). -/
abbrev mvccDeleter_spec.law : Prop :=
  ∀ rd γ (P Pre Q : IProp GF) (f : GoFunc), mvccDeleter (GF := GF) rd γ ⊢
    {{ threadTok ∗ mvccHook γ P f ∗ Pre ∗ hookRun P f Pre Q }}
      (App (Val #rd) (Val #()))
    {{ (t : GoInterface), RET #t;
        (∃ (mw trace : Loc) (σ : MvccState), mvccTxn mw γ trace (.write σ []) ∗
          if mvccWatched γ then
            ∃ tw : Loc, ⌜t = interface.mkOk (go.GoType.PointerType watchableStoreTxnWrite.ty) #tw⌝ ∗
              mvccWatchTxnOf tw mw
          else ⌜t = interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw⌝) ∗
        Q }}

/-- **A store without watchers is notified of every commit.** -/
abbrev mvccNotified_unwatched.law : Prop :=
  ∀ γ σ pend, mvccWatched γ = false → ⊢ mvccNotified (GF := GF) γ σ pend

/-- **A store without watchers may restore.** -/
abbrev mvccRestoreOk_unwatched.law : Prop :=
  ∀ γ, mvccWatched γ = false → ⊢ mvccRestoreOk (GF := GF) γ

/-- **A watchable store's store has watchers.** -/
abbrev isWatchableMvcc_watched.law : Prop :=
  ∀ ws γ, isWatchableMvcc (GF := GF) ws γ ⊢ ⌜mvccWatched γ = true⌝

/-- **A store's views** (its embedded `ReadView`/`WriteView`, which serve its promoted `Range`,
`Rev`, `FirstRev`, `Put` and `DeleteRange`), set for good: a store without watchers' views, over
itself, when it was made; a watchable store's store's, over the watchable store, when the watchable
store was made (`newWatchableStore` overwrites the fields `NewStore` set: until then the right to
wrap the store, `mvccWrapRight`, holds them; round 6). -/
abbrev isMvcc_views.law : Prop :=
  (∀ s γ, mvccWatched γ = false → isMvcc (GF := GF) s γ ⊢ ∃ rv wv : Loc,
    s.[store, go!"ReadView"] ↦□ (interface.mkOk (go.GoType.PointerType readView.ty) #rv : GoInterface) ∗
    isReadViewOf rv γ ∗
    s.[store, go!"WriteView"] ↦□ (interface.mkOk (go.GoType.PointerType writeView.ty) #wv : GoInterface) ∗
    isWriteViewOf wv γ) ∧
  (∀ ws γ, isWatchableMvcc (GF := GF) ws γ ⊢ ∃ s rv wv : Loc,
    ws.[watchableStore, go!"store"] ↦□ s ∗
    s.[store, go!"ReadView"] ↦□ (interface.mkOk (go.GoType.PointerType readView.ty) #rv : GoInterface) ∗
    isReadViewOf rv γ ∗
    s.[store, go!"WriteView"] ↦□ (interface.mkOk (go.GoType.PointerType writeView.ty) #wv : GoInterface) ∗
    isWriteViewOf wv γ)

/-- **A commit of nothing needs no notification** (the code notifies nothing then). -/
abbrev mvccNotified_nil.law : Prop :=
  ∀ γ σ, ⊢ mvccNotified (GF := GF) γ σ []

/-- **A restored state is reachable**, and its revisions fit as every state's do
(`mvccState_reachable`; a restored history consumed no time receipts here, so its backend's
creator says so). -/
abbrev mvccRestorable_reachable.law : Prop :=
  ∀ γ b σ', mvccRestorable (GF := GF) γ b σ' ⊢ ⌜MvccReachable σ' ∧ σ'.log.length < 2 ^ 62⌝

/-- **A hash depends only on the history up to its revision** (what `mvccHashOk_state` needs of
`mvccHashOf`, whatever its definition). -/
abbrev mvccHashOf_prefix.law : Prop :=
  ∀ (L L' : Log) (lo hi : Int), L <+: L' → hi < (L.length : Int) →
    mvccHashOf L lo hi = mvccHashOf L' lo hi

/-- **A hash of the store is of its history**: a hash it gave or stored is of the revisions
`(CompactRevision, Revision]` of every later state's history (histories only grow). -/
abbrev mvccHashOk_state.law : Prop :=
  ∀ γ h σ, mvccHashOk (GF := GF) γ h ∗ mvccState γ σ ⊢
    ⌜h.Hash' = mvccHashOf σ.log (sint.Z h.CompactRevision') (sint.Z h.Revision') ∧
      sint.Z h.Revision' ≤ (σ.rev : Int)⌝

/-- **Announcing**: a revision not yet announced. -/
abbrev mvccAnn_alloc.law : Prop :=
  ∀ γ M r L, M.lookup r = none →
    mvccAnnAuth (GF := GF) γ M ⊢ |==> mvccAnnAuth γ (M.insert r L) ∗ mvccAnn γ r L

/-- An announcement is in the client's map. -/
abbrev mvccAnn_lookup.law : Prop :=
  ∀ γ M r L, mvccAnnAuth (GF := GF) γ M ∗ mvccAnn γ r L ⊢ ⌜M.lookup r = some L⌝

/-- A revision has one announcement. -/
abbrev mvccAnn_agree.law : Prop :=
  ∀ γ r L L', mvccAnn (GF := GF) γ r L ∗ mvccAnn γ r L' ⊢ ⌜L = L'⌝

/-- **Receiving on a compaction's channel** does not panic (a partial triple: it says nothing of
whether the receive returns). -/
abbrev mvccCompactChan_recv.law : Prop :=
  ∀ ch, {{ mvccCompactChan (GF := GF) ch }}
    (App (Val (chan.receive (go.GoType.StructType []))) (Val #ch)) {{ (v : val), RET v; True }}

/-- A watcher's registration is unique. -/
abbrev wsWatcher_agree.law : Prop :=
  ∀ ι id rg fs lo k rg' fs' lo' k',
    wsWatcher (GF := GF) ι id rg fs lo k ∗ wsWatcher ι id rg' fs' lo' k' ⊢
      ⌜rg = rg' ∧ fs = fs' ∧ lo = lo' ∧ k = k'⌝

/-- **The registrar knows every watcher.** -/
abbrev wsWatchers_mem.law : Prop :=
  ∀ ι S id rg fs lo k, wsWatchers (GF := GF) ι S ∗ wsWatcher ι id rg fs lo k ⊢ ⌜id ∈ S⌝

/-- A live watcher was not cancelled; liveness is exclusive. -/
abbrev wsLive_canceled.law : Prop :=
  (∀ ι id, wsLive (GF := GF) ι id ∗ wsCanceled ι id ⊢ False) ∧
  (∀ ι id, wsLive (GF := GF) ι id ∗ wsLive ι id ⊢ False)

/-- An open stream is not closed. -/
abbrev wsOpen_closed.law : Prop :=
  ∀ ι q, wsOpen (GF := GF) ι q ∗ wsClosed ι ⊢ False

/-- **Receiving on the stream's channel**, in the form Perennial's channel rules take (`recvAu`:
a plain receive, `chan.wp_receive`, or one in a `select`): the next response sent (the consumer's
view grown), or (`!ok`) the end of a closed and drained channel. -/
abbrev wsChan_recv.law : Prop :=
  ∀ ι ch, wsChan (GF := GF) ι ch ⊢ ∃ γch : ChanNames, isChan ch γch WatchResponse ∗
    □ (∀ (rs : List WResp) (Φ : WatchResponse → Bool → IProp GF),
      wsRecv ι rs -∗
      (∀ (v : WatchResponse) (ok : Bool),
        (if ok then ∃ r : WResp, wsRecv ι (rs ++ [r]) ∗ wrespIs v r else wsRecv ι rs) -∗ Φ v ok) -∗
      recvAu γch WatchResponse Φ)

/-- **A response's events**: of a registered watcher, each at or below the response's revision;
a compaction response has none. -/
abbrev wsRecv_resp.law : Prop :=
  ∀ ι rs, wsRecv (GF := GF) ι rs ⊢
    ⌜∀ r ∈ rs, (∀ ev ∈ r.evs, sint.Z ev.kv.modRev ≤ sint.Z r.rev) ∧
      (r.compactRev ≠ W64 0 → r.evs = [])⌝ ∗
    □ (∀ r : WResp, ⌜r ∈ rs ∧ r.evs ≠ []⌝ → ∃ rg fs lo k, wsWatcher ι r.id rg fs lo k)

/-- **A response's revision** is one of a log the client may watch (committed or announced). -/
abbrev wsRecv_rev.law : Prop :=
  ∀ ws γ ι rs, isMvccWatchStream (GF := GF) ws γ ι ∗ wsRecv ι rs ⊢
    □ (∀ r : WResp, ⌜r ∈ rs⌝ → ∃ L : Log, mvccLogOk γ L ∗ ⌜sint.nat r.rev + 1 ≤ L.length⌝)

/-- **The watch guarantee**: the events received for a watcher are its range's events, filtered,
of the revisions `[lo, hi)` of a log the client may watch. -/
abbrev wsRecv_events.law : Prop :=
  ∀ ws γ ι rs id rg fs lo k,
    isMvccWatchStream (GF := GF) ws γ ι ∗ wsRecv ι rs ∗ wsWatcher ι id rg fs lo k ⊢
      ∃ (L : Log) (hi : Nat), mvccLogOk γ L ∗
        ⌜hi ≤ L.length ∧ recvEvs rs id = filtered fs (watchEvents L rg lo hi)⌝

/-- **Progress**: a response without events, the `j`-th received, at revision `P`, for the
watcher `id`, or for the whole stream (`-1`) and a watcher registered before it was sent, comes
after every event of the watcher up to `P`, unless the watcher was cancelled (which its live
token refutes, `wsLive_canceled`). -/
abbrev wsRecv_progress.law : Prop :=
  ∀ ws γ ι rs j r id rg fs lo k,
    isMvccWatchStream (GF := GF) ws γ ι ∗ wsRecv ι rs ∗ wsWatcher ι id rg fs lo k ∗
      ⌜rs[j]? = some r ∧ r.evs = [] ∧ r.compactRev = W64 0 ∧
        (r.id = id ∨ (r.id = W64 (-1) ∧ k ≤ j))⌝ ⊢
      wsCanceled ι id ∨ ∃ L : Log, mvccLogOk γ L ∗
        ⌜sint.nat r.rev + 1 ≤ L.length ∧
          recvEvs (rs.take (j + 1)) id = filtered fs (watchEvents L rg lo (sint.nat r.rev + 1))⌝

/-- **A compaction response's revision** is positive and at most the store's compaction
revision (a watcher is compacted only when its next revision is below it). -/
abbrev wsRecv_compact.law : Prop :=
  ∀ ws γ ι rs σ, isMvccWatchStream (GF := GF) ws γ ι ∗ wsRecv ι rs ∗ mvccState γ σ ⊢
    ⌜∀ r ∈ rs, r.compactRev ≠ W64 0 → 0 < sint.Z r.compactRev ∧ sint.Z r.compactRev ≤ σ.crev⌝

end laws

end mvcc
end EtcdGrove
end Perennial
