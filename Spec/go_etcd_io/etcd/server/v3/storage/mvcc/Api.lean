/-
**Candidate API of etcd's mvcc store** (round 8, 2026-11-02, branch `worktree-mvcc-rand-tester`;
for review, not proved, no proof uses it): the vocabulary the candidate specs `<F>.specC` of this
directory's spec files are written in, and the laws an implementation must prove of it
(`<name>.law : Prop`, stated, not assumed: no axiom). Design and decisions:
`notes/mvcc-api-candidate.md`.

The vocabulary is abstract and small (the `spec` skill's measure "Abstractions": as few
predicates as the users' needs allow, one subsuming several). Linearizability is the caller's atomic
update over the store's abstract state (`mvccState γ σ`, owned by the client):

* **the state** `σ : MvccState`: the history of every committed revision (`σ.log`, mvcc's `Log`:
  revision `r`'s changes at `σ.log[r]`, the state at `r` is `stateAt σ.log r`, the current revision
  `σ.rev = σ.log.length - 1`), the compaction revision `σ.crev` (`-1`: none), and the revision being
  committed, already sent to the watchers but not yet visible to reads (`σ.pending`: the watchable
  store notifies before it bumps the revision; a read in between sees the revision before it).
* **a read** (`Read`, `Rev`, a watch's registration) fires the caller's update at the state, which
  it leaves unchanged, and answers from `σ.log`;
* **a write transaction** (`Write` ... `End`) is pinned to the state it began at
  (`mvccTxn_write_agree`); its `End` commits in two steps of the caller's updates (the second
  given by the first's commit): the notification (`σ.notify pend`), then the revision's bump
  (`σ.commitPending`);
* **watch events** are of the notified history (`σ.notifiedLog`: the log with the pending
  revision), which the watch laws relate them to, with the registrar's view of the stream's
  watchers (`wsWatchers`).
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

/-- **The store's backend's ghost names** (its `backend.plHookRO`, `backend.commitReq`). -/
opaque mvccBackend (γ : MvccName) : backend.BNames := default

/-- **Whether the store has watchers** (it is a watchable store's: `New`; or `NewStore` at the
watched mode): its mode, fixed at its creation. -/
opaque mvccWatched (γ : MvccName) : Bool := false

/-- **The stream's channel** (fixed at its creation). -/
opaque wsChanOf (ι : WsName) : GoChan := default

/-- **The hash of the revisions `(lo, hi]` of a history**, as the store computes it (a function of
the history, `mvccHashOf_prefix`: crc32's over the revisions' keys and key-values kept by the
compaction at `lo`). -/
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

/-- **A share `q` of the store's open token** (fractional): `Compact` takes a share (after `Close`
the scheduler is stopped, and a compaction's `Schedule` panics); `Close` and `Restore` (which
replaces the scheduler a concurrent `Compact` reads) take it whole. -/
opaque mvccOpen (γ : MvccName) (q : Qp) : IProp GF := iprop(True)

/-- **The store's backend is `b`, with parameters `P` and batch-lock invariant `Pk`**
(persistent; from `New`): what the backend's hook (`mvccHook`) and commit request
(`backend.commitReq` at `mvccBackend γ`) are over. -/
opaque mvccBackendIs (γ : MvccName) (P : backend.BParams) (Pk : IProp GF) (b : Loc) : IProp GF :=
  iprop(True)

/-- **The store's batch lock has invariant `P` and its post-lock hook is `f`, for good**
(persistent, as its parts are; `f` may be `nil`: no hook): the backend's own read-only share of
its hook (`backend.plHookRO`, by `plHook_persist` after `SetTxPostLockInsideApplyHook`, or the new
backend's `nil`), at the store's backend, whose lock invariant is `P`. A definition, not an
abstraction: its only maker is the backend. -/
def mvccHook (γ : MvccName) (P : IProp GF) (f : GoFunc) : IProp GF :=
  iprop(∃ (BP : backend.BParams) (b : Loc), mvccBackendIs γ BP P b ∗
    backend.plHookRO (mvccBackend γ) f)

/-- The hook is one (the backend's hook is a ghost variable). -/
theorem mvccHook_agree (γ : MvccName) (P P' : IProp GF) (f f' : GoFunc) :
    mvccHook (GF := GF) γ P f ∗ mvccHook γ P' f' ⊢ ⌜f = f'⌝ := by
  unfold mvccHook backend.plHookRO backend.plHookAt
  iintro ⟨⟨%BP, %b, -, H1⟩, ⟨%BP', %b', -, H2⟩⟩
  iapply dghostVar_agree $$ H1 H2

/-- **`t` is a transaction of `γ`** with the view `k`, holding the caller's trace `trace`
(exclusive): `t` the interface value the client holds, a `*metricsTxnWrite` (the store's
transactions), a `*txnReadWrite` (`NewReadOnlyTxnWrite`'s) or a `*watchableStoreTxnWrite` (the
watchable store's write transactions, over a `*metricsTxnWrite`: `mvccTxn_unwrap`). -/
opaque mvccTxn (t : GoInterface) (γ : MvccName) (trace : Loc) (k : MTxn) : IProp GF := iprop(True)

/-- **`rd` is the range deleter the store set on its lessor**: `rd()` is the store's
`Write(TODO)`, the watchable store's if it has watchers (persistent; `mvccDeleter_spec`). -/
opaque mvccDeleter (rd : GoFunc) (γ : MvccName) : IProp GF := iprop(True)

/-- **The watchers were taken care of for `op`** (or the store has none): notified of a commit,
reset for a restore; what a write transaction's own `End` and the store's own `Restore` take. A
store without watchers gives it freely (`mvccWatchersOk_unwatched`); a watched store's is made only
by the watchable store's `End` and `Restore`, which notify and reset: so a client of a watched store
commits and restores through them. -/
opaque mvccWatchersOk (γ : MvccName) (op : MvccOp) : IProp GF := iprop(True)

/-- **The right to wrap the store `s` in a watchable store** (exclusive; `NewStore` at the watched
mode gives it, `New`'s watchable store takes it): it holds the store's `ReadView` and `WriteView`
fields, which the watchable store overwrites with its own views. -/
opaque mvccWrapRight (γ : MvccName) (s : Loc) : IProp GF := iprop(True)

/-- **`v` is a view of the store `γ`** (persistent): `v` a `*readView` or `*writeView` (as the
interface value the store's fields hold), its `kv` serving `γ`, through the watchable store if `γ`
has watchers. -/
opaque isMvccView (v : GoInterface) (γ : MvccName) : IProp GF := iprop(True)

/-- **The backend `b` holds the state `σ`, and the store `γ` may restore from it** (exclusive:
the backend's creator's resources, as today's `store.Restore` takes them; the backend boundary is
open, `notes/mvcc-api-candidate.md`). -/
opaque mvccRestorable (γ : MvccName) (b : Loc) (σ : MvccState) : IProp GF := iprop(True)

/-- **`hs` (a `*hashStorage`) is the store `γ`'s hash storage** (persistent, as its parts are):
the hash storage in a store's `hashes` field (set by `NewStore`, for good). A definition: `isMvcc`
carries what `hs`'s methods need. -/
def isHashStorage (hs : Loc) (γ : MvccName) : IProp GF :=
  iprop(∃ s : Loc, isMvcc s γ ∗
    s.[store, go!"hashes"] ↦□ (interface.mkOk (go.GoType.PointerType hashStorage.ty) #hs : GoInterface))

/-- **`h` is a hash of the store `γ`** (persistent): of the revisions `(h.CompactRevision,
h.Revision]` of its history (`mvccHashOk_state`). -/
opaque mvccHashOk (γ : MvccName) (h : KeyValueHash) : IProp GF := iprop(True)

/-- **`ch` is a compaction's channel**: a receive on it does not panic (persistent). -/
opaque mvccCompactChan (ch : GoChan) : IProp GF := iprop(True)

/-- **`ws` (a `*watchStream`) is a watch stream of the store `γ`, named `ι`** (persistent; its
channel is `wsChanOf ι`). -/
opaque isMvccWatchStream (ws : Loc) (γ : MvccName) (ι : WsName) : IProp GF := iprop(True)

/-- **A share `q` of the stream's open token** (fractional): `Close` takes it whole; a holder of
a share refutes `Watch`'s closed-stream arm. -/
opaque wsOpen (ι : WsName) (q : Qp) : IProp GF := iprop(True)

/-- **The registrar's view of the stream's watchers** (exclusive, timeless; the client's, what
`Watch`'s and `Cancel`'s atomic updates are over): the watcher `id` is `W[id]`. -/
opaque wsWatchers (ι : WsName) (W : List WInfo) : IProp GF := iprop(True)

/-- **The consumer has received the responses `rs`** from the stream's channel, in order
(exclusive, timeless). -/
opaque wsRecv (ι : WsName) (rs : List WResp) : IProp GF := iprop(True)

/-- **The `WatchResponse` value `v` is the response `r`**: its id, revision and compaction
revision, its events a read-only slice of `r`'s events (persistent). -/
def wrespIs (v : WatchResponse) (r : WResp) : IProp GF :=
  iprop(⌜v.WatchID' = r.id ∧ v.Revision' = r.rev ∧ v.CompactRevision' = r.compactRev⌝ ∗
    ∃ ps : List Loc, v.Events' ↦*□ ps ∗ ⌜ps.length = r.evs.length⌝ ∗
      [∗list] x ∈ ps.zip r.evs, evIs x.1 x.2)

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
abbrev persistent.law : Prop :=
  (∀ s γ, Persistent (isMvcc (GF := GF) s γ)) ∧ (∀ ws γ, Persistent (isWatchableMvcc (GF := GF) ws γ)) ∧
  (∀ γ P Pk b, Persistent (mvccBackendIs (GF := GF) γ P Pk b)) ∧
  (∀ rd γ, Persistent (mvccDeleter (GF := GF) rd γ)) ∧
  (∀ γ op, Persistent (mvccWatchersOk (GF := GF) γ op)) ∧ (∀ v γ, Persistent (isMvccView (GF := GF) v γ)) ∧
  (∀ γ h, Persistent (mvccHashOk (GF := GF) γ h)) ∧
  (∀ ch, Persistent (mvccCompactChan (GF := GF) ch)) ∧
  (∀ ws γ ι, Persistent (isMvccWatchStream (GF := GF) ws γ ι)) ∧
  (∀ γ σ, Timeless (mvccState (GF := GF) γ σ)) ∧ (∀ ι W, Timeless (wsWatchers (GF := GF) ι W)) ∧
  (∀ ι rs, Timeless (wsRecv (GF := GF) ι rs)) ∧
  (∀ ι, Fractional (wsOpen (GF := GF) ι)) ∧ (∀ γ, Fractional (mvccOpen (GF := GF) γ))

/-- The state is exclusive. -/
abbrev mvccState_excl.law : Prop :=
  ∀ γ σ σ', mvccState (GF := GF) γ σ ∗ mvccState γ σ' ⊢ False

/-- The registrar's view and the consumer's are exclusive (so the `W` and `rs` the watch laws
take are the current ones). -/
abbrev ws_excl.law : Prop :=
  (∀ ι W W', wsWatchers (GF := GF) ι W ∗ wsWatchers ι W' ⊢ False) ∧
  (∀ ι rs rs', wsRecv (GF := GF) ι rs ∗ wsRecv ι rs' ⊢ False)

/-- **Every state of a store is reachable**, and its revisions fit an `int64` with room to spare
(its changes are fewer than the time receipts, `New`'s `receiptBound GF ≤ 2 ^ 48`). -/
abbrev mvccState_reachable.law : Prop :=
  ∀ s γ σ, isMvcc (GF := GF) s γ ∗ mvccState γ σ ⊢ ⌜MvccReachable σ ∧ σ.log.length < 2 ^ 62⌝

/-- **A write transaction pins the state** it began at (nothing pending), until its `End`: the
state is that one, or its notification of the transaction's changes (inside the watchable store's
`End`, which notifies before it calls the store transaction's `End`; `notify` is idempotent, so
that `End`'s first update is then no change). A sole writer refutes the second from its own
invariant (it has not notified). -/
abbrev mvccTxn_write_agree.law : Prop :=
  ∀ t γ trace σ pend σ', mvccTxn (GF := GF) t γ trace (.write σ pend) ∗ mvccState γ σ' ⊢
    ⌜σ.pending = none ∧ (σ' = σ ∨ σ' = σ.notify pend)⌝

/-- **The caller's trace, while its transaction is open** (to step and annotate it). -/
abbrev mvccTxn_trace.law : Prop :=
  ∀ t γ trace k, mvccTxn (GF := GF) t γ trace k ⊢
    (∃ te, traceutil.ownTrace trace te) ∗ ((∃ te, traceutil.ownTrace trace te) -∗ mvccTxn t γ trace k)

/-- **The watchable store's write transaction `tw` is over a store's `mw`**: its embedded
`TxnWrite` is `mw`, which serves its promoted `Put`, `DeleteRange`, `Range`, `Rev`, `FirstRev` and
`Changes` (`mw`'s `End`, which would commit without notifying, needs `mvccWatchersOk`, which a
watched store's client does not have); the client gets `tw`'s back from `mw`'s, at any view. -/
abbrev mvccTxn_unwrap.law : Prop :=
  ∀ tw γ trace k,
    mvccTxn (GF := GF) (interface.mkOk (go.GoType.PointerType watchableStoreTxnWrite.ty) #tw) γ trace k ⊢
      ∃ mw : Loc,
        tw.[watchableStoreTxnWrite, go!"TxnWrite"] ↦□
          (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw : GoInterface) ∗
        mvccTxn (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw) γ trace k ∗
        (∀ k', mvccTxn (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw) γ trace k' -∗
          mvccTxn (interface.mkOk (go.GoType.PointerType watchableStoreTxnWrite.ty) #tw) γ trace k')

/-- **The watchable store's store** (its embedded `*store`, which serves its promoted `Read`,
`Rev`, `Compact`, `Commit` and `HashStorage`), and its mode. -/
abbrev isWatchableMvcc_store.law : Prop :=
  ∀ ws γ, isWatchableMvcc (GF := GF) ws γ ⊢
    ⌜mvccWatched γ = true⌝ ∗ ∃ s : Loc, ws.[watchableStore, go!"store"] ↦□ s ∗ isMvcc s γ

/-- **A store's views** (its embedded `ReadView`/`WriteView`, which serve its promoted `Range`,
`Rev`, `FirstRev`, `Put` and `DeleteRange`), set for good: a store without watchers' views, over
itself, when it was made; a watchable store's store's, over the watchable store, when the watchable
store was made (`newWatchableStore` overwrites the fields `NewStore` set: until then
`mvccWrapRight` holds them). -/
abbrev isMvcc_views.law : Prop :=
  (∀ s γ, mvccWatched γ = false → isMvcc (GF := GF) s γ ⊢ ∃ rv wv : Loc,
    s.[store, go!"ReadView"] ↦□ (interface.mkOk (go.GoType.PointerType readView.ty) #rv : GoInterface) ∗
    isMvccView (interface.mkOk (go.GoType.PointerType readView.ty) #rv) γ ∗
    s.[store, go!"WriteView"] ↦□ (interface.mkOk (go.GoType.PointerType writeView.ty) #wv : GoInterface) ∗
    isMvccView (interface.mkOk (go.GoType.PointerType writeView.ty) #wv) γ) ∧
  (∀ ws γ, isWatchableMvcc (GF := GF) ws γ ⊢ ∃ s rv wv : Loc,
    ws.[watchableStore, go!"store"] ↦□ s ∗
    s.[store, go!"ReadView"] ↦□ (interface.mkOk (go.GoType.PointerType readView.ty) #rv : GoInterface) ∗
    isMvccView (interface.mkOk (go.GoType.PointerType readView.ty) #rv) γ ∗
    s.[store, go!"WriteView"] ↦□ (interface.mkOk (go.GoType.PointerType writeView.ty) #wv : GoInterface) ∗
    isMvccView (interface.mkOk (go.GoType.PointerType writeView.ty) #wv) γ)

/-- **The range deleter** the store set on its lessor is the store's `Write(traceutil.TODO())`,
the watchable store's if it has watchers: a write transaction (as `store.Write.specC` or
`watchableStore.Write.specC`, at a trace of its own). -/
abbrev mvccDeleter_spec.law : Prop :=
  ∀ rd γ (P Pre Q : IProp GF) (f : GoFunc), mvccDeleter (GF := GF) rd γ ⊢
    {{ threadTok ∗ mvccHook γ P f ∗ Pre ∗ hookRun P f Pre Q }}
      (App (Val #rd) (Val #()))
    {{ (t : GoInterface), RET #t;
        (∃ (trace : Loc) (σ : MvccState), mvccTxn t γ trace (.write σ []) ∗
          ⌜if mvccWatched γ then ∃ tw : Loc, t = interface.mkOk (go.GoType.PointerType watchableStoreTxnWrite.ty) #tw
           else ∃ mw : Loc, t = interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw⌝) ∗
        Q }}

/-- **A store without watchers has them taken care of**, for every commit and restore. -/
abbrev mvccWatchersOk_unwatched.law : Prop :=
  ∀ γ op, mvccWatched γ = false → ⊢ mvccWatchersOk (GF := GF) γ op

/-- **A commit of nothing needs no notification.** -/
abbrev mvccWatchersOk_nil.law : Prop :=
  ∀ γ σ, ⊢ mvccWatchersOk (GF := GF) γ (.commit σ [])

/-- **A restored state is reachable**, nothing pending, its revisions fit (its backend's creator
says so: a restored history consumed no time receipts here). -/
abbrev mvccRestorable_reachable.law : Prop :=
  ∀ γ b σ', mvccRestorable (GF := GF) γ b σ' ⊢
    ⌜MvccReachable σ' ∧ σ'.pending = none ∧ σ'.log.length < 2 ^ 62⌝

/-- **A hash of the store is of its history**: a hash it gave or stored is of the revisions
`(CompactRevision, Revision]` of every later state's history (histories only grow). -/
abbrev mvccHashOk_state.law : Prop :=
  ∀ γ h σ, mvccHashOk (GF := GF) γ h ∗ mvccState γ σ ⊢
    ⌜h.Hash' = mvccHashOf σ.log (sint.Z h.CompactRevision') (sint.Z h.Revision') ∧
      sint.Z h.Revision' ≤ (σ.rev : Int)⌝

/-- **A hash depends only on the history up to its revision** (what `mvccHashOk_state` needs of
`mvccHashOf`, whatever its definition). -/
abbrev mvccHashOf_prefix.law : Prop :=
  ∀ (L L' : Log) (lo hi : Int), L <+: L' → hi < (L.length : Int) →
    mvccHashOf L lo hi = mvccHashOf L' lo hi

/-- **Receiving on a compaction's channel** does not panic (a partial triple: it says nothing of
whether the receive returns). -/
abbrev mvccCompactChan_recv.law : Prop :=
  ∀ ch, {{ mvccCompactChan (GF := GF) ch }}
    (App (Val (chan.receive (go.GoType.StructType []))) (Val #ch)) {{ (v : val), RET v; True }}

/-- **Receiving on the stream's channel**, in the form Perennial's channel rules take (`recvAu`:
a plain receive, `chan.wp_receive`, or one in a `select`): the next response sent (the consumer's
view grown), or (`!ok`) the end of a closed and drained channel. -/
abbrev wsChan_recv.law : Prop :=
  ∀ ws γ ι, isMvccWatchStream (GF := GF) ws γ ι ⊢ ∃ γch : ChanNames,
    isChan (wsChanOf ι) γch WatchResponse ∗
    □ (∀ (rs : List WResp) (Φ : WatchResponse → Bool → IProp GF),
      wsRecv ι rs -∗
      (∀ (v : WatchResponse) (ok : Bool),
        (if ok then ∃ r : WResp, wsRecv ι (rs ++ [r]) ∗ wrespIs v r else wsRecv ι rs) -∗ Φ v ok) -∗
      recvAu γch WatchResponse Φ)

/-- **A response's events**: each at or below the response's revision, of a watcher the
registrar registered; a compaction response has none. -/
abbrev wsRecv_resp.law : Prop :=
  ∀ ι rs W, wsRecv (GF := GF) ι rs ∗ wsWatchers ι W ⊢
    ⌜∀ r ∈ rs, (∀ ev ∈ r.evs, sint.Z ev.kv.modRev ≤ sint.Z r.rev) ∧
      (r.compactRev ≠ W64 0 → r.evs = []) ∧ (r.evs ≠ [] → sint.nat r.id < W.length)⌝

/-- **The watch guarantee**: the events received for each watcher are its range's events,
filtered, of the revisions `[lo, hi)` of the notified history; each response's revision is one of
it; a compaction response's revision is positive and at most the compaction revision. -/
abbrev wsRecv_events.law : Prop :=
  ∀ ws γ ι rs W σ,
    isMvccWatchStream (GF := GF) ws γ ι ∗ wsRecv ι rs ∗ wsWatchers ι W ∗ mvccState γ σ ⊢
      ⌜(∀ (id : Nat) (w : WInfo), W[id]? = some w → ∃ hi, hi ≤ σ.notifiedLog.length ∧
          recvEvs rs (W64 (id : Int)) = filtered w.fs (watchEvents σ.notifiedLog w.rg w.lo hi)) ∧
        (∀ r ∈ rs, sint.nat r.rev < σ.notifiedLog.length) ∧
        (∀ r ∈ rs, r.compactRev ≠ W64 0 → 0 < sint.Z r.compactRev ∧ sint.Z r.compactRev ≤ σ.crev)⌝

/-- **Progress**: a response without events, the `j`-th received, at revision `P`, for the
watcher `id`, or for the whole stream (`-1`) and a live watcher registered before it was sent,
comes after every event of the watcher up to `P`. -/
abbrev wsRecv_progress.law : Prop :=
  ∀ ws γ ι rs W σ,
    isMvccWatchStream (GF := GF) ws γ ι ∗ wsRecv ι rs ∗ wsWatchers ι W ∗ mvccState γ σ ⊢
      ⌜∀ (j id : Nat) (r : WResp) (w : WInfo), rs[j]? = some r → W[id]? = some w →
        r.evs = [] → r.compactRev = W64 0 →
        (r.id = W64 (id : Int) ∨ (r.id = W64 (-1) ∧ w.k ≤ j ∧ w.live = true)) →
        sint.nat r.rev + 1 ≤ σ.notifiedLog.length ∧
        recvEvs (rs.take (j + 1)) (W64 (id : Int)) =
          filtered w.fs (watchEvents σ.notifiedLog w.rg w.lo (sint.nat r.rev + 1))⌝

end laws

end mvcc
end EtcdGrove
end Perennial
