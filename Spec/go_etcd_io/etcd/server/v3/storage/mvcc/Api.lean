/-
**mvcc's API, frozen 2026-11-03, reopened before the proof as round 14** (`notes/mvcc-api-candidate.md`,
"The freeze", "Reopened before the proof"; round 14 from the assessments of etcd's proofs over the
API: A1 the stream's sent count `wsSentLb`, given by `Watch` at a watcher's stamp, and at `0`; A2 the
non-blocking receive, in one channel law with the blocking one; A3 a compaction response's
revision `0`; A4 a read transaction's states small; A5 the lease bucket's delete inside a write
transaction, giving back `End`'s triple; all after the review of round 14,
`~/mvcc-api-candidates/review-r14.md`; round 15, the user's (D): the size facts a range's caller
needs at the `Range` contracts, `stateOk`, and the restored history's receipt on `Restore`, in place of
round 14's A4 law): the vocabulary
(opaque until the invariants stage defines each over the implementation, sealed), the contracts of
the interfaces' methods at a receiver, the canonical specs per (concrete type, method) as their
instances, the constructors' specs, and the laws an implementation proves (`<name>.law : Prop`,
stated, not assumed). Beside today's specs until the proofs are done and the clients move onto it
(then each `api.<T>.<M>.spec` replaces today's `<T>.<M>.spec` in its spec file). The candidate's
round history follows.

# mvcc's API, candidate round 13 (2026-11-03)

## Round 13 (the `spec-reviewer`'s review of round 12, `~/mvcc-api-candidates/review-r12.md`)

* **H1, `mvccBackendFor_open` was unprovable**: `newPostK` swaps the backend's payment rights for
  the caller's `K`, so at an arbitrary `K` the store's write-back tokens are not there. Now (decision
  2, the user): at any `K`, with the store's part of the payment rights as explicit premises in the
  backend's terms (write-back tokens, half the open token), so boot and the snapshot path both use it.
* **R1**: `Restore` takes the restored history's length bound (`σ'.log.length + receiptBound GF + 3 ≤
  2 ^ 63`), which `mvccState_reachable` needs after it (today's `Restore` carries it in its revision
  tokens).
* **S1, the shape laws**: a transaction, a stream and a store handle are `interface.mkOk ty v` of a
  type meeting its interface's contracts (`txn_shape`, `ws_shape`, `kv_shape`, replacing
  `bundles.law`): a client holding the `GoInterface` `Read` returned can make its first call.
* **R2**: `Restore` gives back the store's half of the old backend's open token
  (`backend.bOpen B.γB ½`, the other half the client's), so the client can close the old backend.
* **R3**: `Restore` from a compacted image: `mvccBackendFor_open` takes the image of a compacted
history (`imageOf`, its two obligations in its docstring); a restore resuming an unfinished
compaction locks the new backend with no hook yet (the client lends its `plHook B'.γB nil`, as the
server sets the new backend's hook after `Restore`: a marked scope restriction).
* **The re-review** (`review-r13.md`): `Close`'s give-back of the backend's half open token was
  false (a reader may still hold part of it: `store.Close` takes no lock), so `Close` gives nothing
  again (incomplete: the user's decision, the notes); `Restore`'s commit request was vacuous
  (`commitReq … X X` holds of every `X`), dropped.
* Docstrings: `wsRecvOk`'s condition's cost for etcd (P2); a read transaction's dynamic type is a
  write transaction's (`*metricsTxnWrite`), so the write contracts rest on `mvccTxn`'s kind.
* **Decisions 1-3 (the user, 2026-11-03)**: closing and shutdown out of scope (`Close` minimal);
  the backend law over the store's needs at any opener; `Restore` at any share of the new backend's
  hook, with the hook contract and commit request of `Compact` (spec (U), stronger than the loan
  and than a frozen-hook contract, both its instances), the backend resource recording whether its
  image has an unfinished compaction (`u`).
* **Before the freeze** (2026-11-03, the reviews `review-r13b.md`, `review-r13c.md` and a survey of
  `lean`'s internals): the backend law at `lean`'s pooled post with its write-back supply; the store
  at most `rdStockN` threads (`threadBound GF ≤ backend.rdStockN`); the open token exclusive
  (concurrent compactions out of scope, marked).
* Not taken (preference P1): the backend's share inside the write transaction from `Write` to `End`
  (it would index `mvccTxn` by the share).

(Round 12's header follows.)

Scratch file (outside the repository, never committed); typechecks against the repository's build
(`lake env lean FILE` from the worktree). Names are under `mvcc.R12` to sit beside round 9's
`Api.lean`; adopted, they drop the prefix.

## Round 12: the user's answers to rounds 10-11 (`notes/mvcc-api-candidate.md`)

* **Every verified method is back** (a principle now: "A smaller API is not a narrower scope"):
  `NewStore`, `Restore` (both stores), the store's own `Range`/`Rev`/`FirstRev`/`Put`/`DeleteRange`,
  the read-only transaction's `Put`/`DeleteRange`, `hashStorage.Store` (an axiom today), watch
  filters. Still out (no proof today): `HashByRev`, `Hash`, `Hashes`, a caller-chosen watch id.
* **A store without a hook** (the user): the hook contract's `nil` row is back (`hookRun`); the
  hook fact is the backend's own (`backend.plHookRO`, from freezing the backend's hook, `nil` for a
  fresh backend).
* **Canonical specs per (concrete type, method)** (the user: "a nice mapping from (type, method
  name) to spec"), each the instance of its interface method's contract at that type
  (`<Iface>.<M>.contract ty v`); interface values get a pure bundle of the contracts, as
  Perennial's `isLocker` (`isKV`, `isWatchableKV`, `isTxn`, `isWatchStream`), from the laws
  `*_bundle`. A promoted method is a (type, method) pair too (`watchableStore.Read`,
  `watchableStoreTxnWrite.Put`), as today's `store.Rev` already is.
* **The backend is a fractional token**, `mvccBackend γ q B Pk` (`B` its names, parameters and
  location; `Pk` its batch lock's invariant): `Restore` replaces it, so it cannot be persistent
  (round 11's `mvccBackendIs`). `Write`, `End`, `Compact`, `Commit` and the store's own writes take a
  share; `Restore` takes it whole and gives the new backend's.
* **`NewStore` needs no mode**: clients only ever hold the store `New` or `NewStore` returned (a
  watchable store's embedded store is never handed out), so no commit can skip the watchers.
* **Compaction with watches, one condition** (the user: no proof bifurcation): the watch guarantee
  holds of a watcher while every revision from its first up to the compaction revision changes each
  key at most once (`onceUpTo`; vacuous below the compaction revision): the case the code loses
  events in (`nonissues/etcd-mvcc-watch-compact-rev-subrev-lost.md`) is exactly its negation.
* **The backend's resources** (`mvccBackendFor`, sealed): what `New`, `NewStore` and `Restore`
  take, made by the law `mvccBackendFor_open` from what the backend's opener returns at the store's
  write invariant `mvccW gx` (`mvccW_alloc`); always the compacting form, so no compaction mode.
  Designed against `lean` (M2 merged there, 2026-11-01), which this branch is behind.

## The vocabulary

Opaque Iris predicates (8): `mvccState`, `isMvcc`, `mvccOpen`, `mvccBackend`, `mvccTxn`,
`isMvccWatchStream`, `wsState`, `wsRecv`; and at the backend boundary (made and consumed once each,
by the laws and the constructors): `mvccW`, `mvccWReg`, `mvccBackendFor`, `backendRest`. Opaque pure names: the types `MvccName`, `WsName`;
`mvccLeases`, `wsChanOf`. Definitions: `hookRun`, `mvccDeleter`, `compactChanOk`, `hashStoreOk`,
`wrespIs`, the contracts and bundles, the pure state and `wsRecvOk`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiState
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStream
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.RdPool
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__Snapshot
public import Perennial.ProgramLogic.Bounds

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

/-- **A store's name** (pure, opaque to clients; the implementation's ghost names, defined by the
invariants stage). -/
opaque MvccName : Type
/-- **A watch stream's name** (pure, opaque). -/
opaque WsName : Type
/-- **The store's lessor's ghost name** (its `lease.leaseOwn`). -/
opaque mvccLeases (γ : MvccName) : GName
/-- **The stream's channel** (fixed at its creation). -/
opaque wsChanOf (ι : WsName) : GoChan

/-! ## The vocabulary -/

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The store's state is `σ`** (exclusive, timeless; the client's). -/
opaque mvccState (γ : MvccName) (σ : MvccState) : IProp GF := iprop(True)

/-- **`kv` (the `KV` `New` or `NewStore` returned) serves the store `γ`** (persistent). -/
opaque isMvcc (kv : GoInterface) (γ : MvccName) : IProp GF := iprop(True)

/-- **The store's open token** (exclusive): `Compact`, `Restore` and `Close` take it, the first two
give it back. A compaction schedules its job after releasing `s.mu`, on a scheduler `Close` stops and
`Restore` replaces; and two concurrent compactions could schedule their jobs out of the order of
their revisions. **Scope restriction** (marked): compactions are not concurrent with each other or
with a restore or close (etcd compacts from its apply thread; the tester does not compact). -/
opaque mvccOpen (γ : MvccName) : IProp GF := iprop(True)

/-- **A share `q` of the store's backend: it is `B`, its batch lock's invariant `Pk`**
(fractional; `New`'s or `NewStore`'s, then `Restore`'s). -/
opaque mvccBackend (γ : MvccName) (q : Qp) (B : BkRef) (Pk : IProp GF) : IProp GF := iprop(True)

/-- **`t` is a transaction of `γ`, begun with `trace`, at `k`** (exclusive; it holds the caller's
thread token until its `End`, not the trace). -/
opaque mvccTxn (t : GoInterface) (γ : MvccName) (trace : Loc) (k : MTxn) : IProp GF := iprop(True)

/-- **`ws` (the `WatchStream` `NewWatchStream` returned) is a stream of `γ`, named `ι`**
(persistent). -/
opaque isMvccWatchStream (ws : GoInterface) (γ : MvccName) (ι : WsName) : IProp GF := iprop(True)

/-- **The stream's state is `S`** (exclusive, timeless; the client's). -/
opaque wsState (ι : WsName) (S : StreamState) : IProp GF := iprop(True)

/-- **The stream has sent at least `n` responses** (persistent; round 14, A1): `Watch` gives it at
the watcher's stamp `k`, so that a client can match a stream-wide progress response (the `j`-th
received, `j ≥ k`) with the watchers registered before it; the non-blocking receive's empty case
bounds it by what was received (`wsChan_recv`). -/
opaque wsSentLb (ι : WsName) (n : Nat) : IProp GF := iprop(True)

/-- **The consumer has received `rs`**, in order (exclusive, timeless). -/
opaque wsRecv (ι : WsName) (rs : List WResp) : IProp GF := iprop(True)

/-- **The write invariant a store's backend must be opened with**, at the registration name `gx`
(the `W` of `backend.New`/`storage.OpenSnapshotBackend`; sealed: today's `lateW gx`). -/
opaque mvccW (gx : GName) : IProp GF := iprop(True)

/-- **The right to register a store at `gx`** (exclusive; sealed: today's `lateReg gx`), allocated
before the backend is opened (`mvccW_alloc`). -/
opaque mvccWReg (gx : GName) : IProp GF := iprop(True)

/-- **The backend `B`, with batch-lock invariant `Pk`, holds the history `L` compacted at `c`, ready
for a store over it**, its image recording an unfinished compaction iff `u` (which `Restore`
resumes) (exclusive; sealed). What `New`, `NewStore` and `Restore` take of a backend;
made from what the backend's opener returns at `W := mvccW gx` (`mvccBackendFor_open`). Its body
(round 12's survey; on `lean`, which has M2's compaction model): the backend's persistent
`isBackend`, its Key bucket's view at the image of `(L, c)`, its compaction-key ownership, the
deletable keys' registration (`dlInit`), the store's two write-back tokens and the receipt-paid
supply the compaction's job needs, every reader token (`bkRTx`), the safe-range slot, the
registration `mvccWReg gx`, and the size assumption `keySized`. Always the compacting form: every
opened backend carries what compaction needs, so the API has no compaction mode. -/
opaque mvccBackendFor (B : BkRef) (Pk : IProp GF) (L : Log) (c : Int) (u : Bool) : IProp GF :=
  iprop(True)

/-- **The backend data `D` is the image of the history `L` compacted at `c`, recording an unfinished
compaction iff `u`** (the scheduled compaction above the finished one), **and every change of `L` was
made by a step of the program** (round 16, the user: the receipt `⧖ (logCh L)` hidden in this
predicate, traced from the sender's store, `mvccImage_snapshot`, through the server's image
certificate, to the receiver's `mvccBackendFor_open`; persistent; opaque; on adoption: the image
`keyImage L D` when `c = -1`, else `lean`'s restore image, with the receipt. Formerly the pure
`imageOf`). Its obligations (the review of round
13, `restore`, `kvstore.go:365-423`): when the scheduled compaction is above the finished one, `c`
is the scheduled revision (the restore resumes it, so the Key bucket may be partly compacted); and
`L`'s last revision is the largest of the Key bucket's last revision and the two compaction
revisions. -/
opaque mvccImage (D : backend.Data) (L : Log) (c : Int) (u : Bool) : IProp GF := iprop(True)

/-- **What the client keeps of an opened backend** after the store's part (a definition on
adoption; here opaque): its stop channels, its hook's exclusive half at `nil`
(to set, or to freeze at `nil`), its other buckets' rights (lease, alarm, auth, membership), the
reader pool (`rdPool`), and `K`. (The store's reader slots' open shares come back at the `Restore`
that replaces the backend; not at `Close`, shutdown being out of scope.) -/
opaque backendRest (γB : backend.BNames) (P : backend.BParams) (K : backend.BNames → IProp GF)
  (b : Loc) (D : backend.Data) : IProp GF := iprop(True)

/-- **What the post-lock hook `f` does** under the batch lock of invariant `P`, from the caller's
`Pre`: `f`'s triple to `Q`, or with no hook (`nil`), the caller's view shift. -/
def hookRun (P : IProp GF) (f : GoFunc) (Pre Q : IProp GF) : IProp GF :=
  if f = func.nil then iprop(P ∗ Pre ={⊤}=∗ Q)
  else iprop(□ {{ P ∗ Pre }} (App (Val #f) (Val #())) {{ RET #(); Q }})

/-- **The backend's hook is `f`, for good** (the backend's own fact). -/
abbrev hookIs (B : BkRef) (f : GoFunc) : IProp GF := backend.plHookRO B.γB f

/-- The `WatchResponse` value `v` is the response `r`. -/
def wrespIs (v : WatchResponse) (r : WResp) : IProp GF :=
  iprop(⌜v.WatchID' = r.id ∧ v.Revision' = r.rev ∧ v.CompactRevision' = r.compactRev⌝ ∗
    ∃ ps : List Loc, v.Events' ↦*□ ps ∗ ⌜ps.length = r.evs.length⌝ ∗
      [∗list] x ∈ ps.zip r.evs, evIs x.1 x.2)

/-- A compaction's channel: receiving on it does not panic. -/
def compactChanOk (ch : GoChan) : IProp GF :=
  iprop(□ {{ True }} (App (Val (chan.receive (go.GoType.StructType []))) (Val #ch))
    {{ (v : val), RET v; True }})

/-- The hash storage `h`'s `Store` does not panic (all that is verified of it: an axiom today). -/
def hashStoreOk (h : GoInterface) : IProp GF :=
  iprop(□ ∀ (ty : go.GoType) (v : val) (kh : KeyValueHash), ⌜h = interface.mkOk ty v⌝ -∗
    {{ True }} (App (Val #(methods ty go!"Store" v)) (Val #kh)) {{ RET #(); True }})

/-- The lessor's range deleter `rd` is the store's `Write(traceutil.TODO())`, not `nil` (the
server draft's S2: `lessor.Revoke` checks it). -/
def mvccDeleter (rd : GoFunc) (γ : MvccName) : IProp GF :=
  iprop(⌜rd ≠ func.nil⌝ ∗ □ ∀ (q : Qp) (B : BkRef) (P Pre Q : IProp GF) (f : GoFunc) (R : MvccState → IProp GF),
    {{ threadTok ∗ mvccBackend γ q B P ∗ hookIs B f ∗ Pre ∗ hookRun P f Pre Q ∗
        AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
          <{ ⌜σ.pending = none⌝ ∗ mvccState γ σ, COMM R σ }> }}
      (App (Val #rd) (Val #()))
    {{ (t : GoInterface), RET #t; mvccBackend γ q B P ∗
        (∃ (trace : Loc) (σ : MvccState), mvccTxn t γ trace (.write σ []) ∗ R σ) ∗ Q }})

end vocab

section contracts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc

/-! ## The contracts of the interfaces' methods, at a receiver `interface.mkOk ty v`

A (type, method) pair's canonical spec is its interface method's contract at that type (the list
after the contracts). -/

/-! ### `KV` (and `WatchableKV`) -/

/-- **`Read(mode, trace)`**: a read transaction at the state, by the caller's update. -/
abbrev KV.Read.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (mode : w32) (trace : Loc) (te : Bool) (Q : MvccState → IProp GF),
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗ threadTok ∗ ⌜trace ≠ null⌝ ∗
      traceutil.ownTrace trace te ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅ <{ mvccState γ σ, COMM Q σ }> }}
    (App (App (Val #(methods ty go!"Read" v)) (Val #mode)) (Val #trace))
  {{ (t : GoInterface), RET #t; traceutil.ownTrace trace te ∗
      ∃ σ : MvccState, mvccTxn t γ trace (.read σ) ∗ Q σ }}

/-- **`Write(trace)`**: a write transaction begun at the state, by the caller's update (at its
begin revision; nothing pending); the hook run under the batch lock, `Pre` to `Q`. -/
abbrev KV.Write.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (trace : Loc) (te : Bool) (q : Qp) (B : BkRef) (P Pre Q : IProp GF)
    (f : GoFunc) (R : MvccState → IProp GF),
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗ threadTok ∗ ⌜trace ≠ null⌝ ∗
      traceutil.ownTrace trace te ∗ mvccBackend γ q B P ∗ hookIs B f ∗ Pre ∗ hookRun P f Pre Q ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
        <{ ⌜σ.pending = none⌝ ∗ mvccState γ σ, COMM R σ }> }}
    (App (Val #(methods ty go!"Write" v)) (Val #trace))
  {{ (t : GoInterface), RET #t; traceutil.ownTrace trace te ∗ mvccBackend γ q B P ∗
      (∃ σ : MvccState, mvccTxn t γ trace (.write σ []) ∗ R σ) ∗ Q }}

/-- **`Rev()`**: the state's revision, by the caller's update. -/
abbrev KV.Rev.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (Q : MvccState → IProp GF),
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗ threadTok ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅ <{ mvccState γ σ, COMM Q σ }> }}
    (App (Val #(methods ty go!"Rev" v)) (Val #()))
  {{ (r : w64), RET #r; threadTok ∗ ∃ σ : MvccState, Q σ ∗ ⌜r = W64 (σ.rev : Int)⌝ }}

/-- **`FirstRev()`**: the state's compaction revision, by the caller's update. -/
abbrev KV.FirstRev.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (Q : MvccState → IProp GF),
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗ threadTok ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅ <{ mvccState γ σ, COMM Q σ }> }}
    (App (Val #(methods ty go!"FirstRev" v)) (Val #()))
  {{ (r : w64), RET #r; threadTok ∗ ∃ σ : MvccState, Q σ ∗ ⌜r = W64 σ.crev⌝ }}

/-- **`Range(ctx, key, end, ro)`** (a read transaction of one range): the outcome at the state, and
every state it could read safe to sort (`stateOk`, round 15: what the caller's sort of the results
needs). -/
abbrev KV.Range.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (todo : Bool)
    (key endk : GoSlice) (kk e : GoString) (ro : RangeOptions) (Q : MvccState → IProp GF),
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗ threadTok ∗ rangeCtx todo ctx cd ∗
      key ↦*□ kk ∗ endk ↦*□ e ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅ <{ mvccState γ σ, COMM Q σ }> }}
    (App (App (App (App (Val #(methods ty go!"Range" v)) (Val #(GoInterface.ok ctx))) (Val #key))
      (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err); threadTok ∗ ⌜todo = true → r ≠ null⌝ ∗
      ∃ σ : MvccState, Q σ ∗
        rangeOutcomeC r err σ.log (W64 (σ.rev : Int)) σ.crev (decide (endk = slice.nil)) kk e ro ∗
        ⌜∀ r' : Nat, σ.crev ≤ (r' : Int) → r' ≤ σ.rev → stateOk (stateAt σ.log r')⌝ }}

/-- **`Put(key, value, lease)`** (a write transaction of one put): the hook, then the commit's two
steps at the state the update gives (the lessor's item map that state's). -/
abbrev KV.Put.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (key value : GoSlice) (k vv : GoString) (leaseID : w64) (L : List w64)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (q : Qp) (B : BkRef)
    (P Pre Q' Post : IProp GF) (f : GoFunc) (Q : MvccState → IProp GF),
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗ threadTok ∗ key ↦*□ k ∗ value ↦*□ vv ∗
      ⌜(k.length : Int) < 2 ^ 63 - 1⌝ ∗
      lease.leaseOwn (mvccLeases γ) L I ∗ ⌜leaseID = W64 0 ∨ leaseID ∈ L⌝ ∗
      mvccBackend γ q B P ∗ hookIs B f ∗ Pre ∗ hookRun P f Pre Q' ∗ (Q' ={⊤}=∗ P ∗ Post) ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ ∗ ⌜pendItems σ.log [] = I⌝ }> @ ⊤ \ ↑mvccN, ∅
        <{ ⌜σ.pending = none⌝ ∗ mvccState γ (σ.notify [.put k vv leaseID]) ∗
            ⧖ (logCh (σ.log ++ [[.put k vv leaseID]])), COMM
            AU <{ ∃∃ (σ' : MvccState), mvccState γ σ' }> @ ⊤ \ ↑mvccN, ∅
              <{ ⌜σ' = σ.notify [.put k vv leaseID]⌝ ∗ mvccState γ σ'.commitPending,
                 COMM Q σ }> }> }}
    (App (App (App (Val #(methods ty go!"Put" v)) (Val #key)) (Val #value)) (Val #leaseID))
  {{ (rev : w64), RET #rev; threadTok ∗ mvccBackend γ q B P ∗ Post ∗ ∃ σ : MvccState, Q σ ∗
      lease.leaseOwn (mvccLeases γ) L (pendItems σ.log [.put k vv leaseID]) ∗
      ⌜rev = W64 (σ.log.length : Int)⌝ }}

/-- **`DeleteRange(key, end)`** (a write transaction of one range delete), as `Put`: the range's
present keys deleted, their number, the revision written (none if nothing was deleted). -/
abbrev KV.DeleteRange.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (key endk : GoSlice) (k e : GoString) (L : List w64)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (q : Qp) (B : BkRef)
    (P Pre Q' Post : IProp GF) (f : GoFunc) (Q : MvccState → IProp GF),
  let ds (σ : MvccState) := (delKeys σ.log [] (decide (endk = slice.nil)) k e).map Change.del
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗ threadTok ∗ key ↦*□ k ∗ endk ↦*□ e ∗
      lease.leaseOwn (mvccLeases γ) L I ∗
      mvccBackend γ q B P ∗ hookIs B f ∗ Pre ∗ hookRun P f Pre Q' ∗ (Q' ={⊤}=∗ P ∗ Post) ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ ∗ ⌜pendItems σ.log [] = I⌝ }> @ ⊤ \ ↑mvccN, ∅
        <{ ⌜σ.pending = none⌝ ∗ mvccState γ (σ.notify (ds σ)) ∗ ⧖ (logCh (σ.log ++ [ds σ])), COMM
            AU <{ ∃∃ (σ' : MvccState), mvccState γ σ' }> @ ⊤ \ ↑mvccN, ∅
              <{ ⌜σ' = σ.notify (ds σ)⌝ ∗ mvccState γ σ'.commitPending, COMM Q σ }> }> }}
    (App (App (Val #(methods ty go!"DeleteRange" v)) (Val #key)) (Val #endk))
  {{ (n rev : w64), RET (PairV #n #rev); threadTok ∗ mvccBackend γ q B P ∗ Post ∗
      ∃ σ : MvccState, Q σ ∗ lease.leaseOwn (mvccLeases γ) L (pendItems σ.log (ds σ)) ∗
      ⌜n = W64 ((ds σ).length : Int) ∧ rev = W64 ((writeRev σ.log (ds σ) : Nat) : Int)⌝ }}

/-- **`Compact(trace, rev)`**, by the caller's update at the state it compacts: above the compaction
revision and at most the current one, the hook once under the batch lock (`Pre` to `Q'`, giving `P`
back) and the backend's commit (`X` to `Y`); at or below it, `ErrCompacted`; past the current
revision, `ErrFutureRev` and no channel. -/
abbrev KV.Compact.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (trace : Loc) (te : Bool) (rev : w64) (q : Qp) (B : BkRef)
    (P : IProp GF) (f : GoFunc) (Pre Q' Post X Y : IProp GF) (Q : MvccState → IProp GF),
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗ mvccOpen γ ∗ threadTok ∗ ⌜trace ≠ null⌝ ∗
      traceutil.ownTrace trace te ∗ mvccBackend γ q B P ∗ hookIs B f ∗
      X ∗ backend.commitReq B.γB B.P P B.b X Y ∗
      Pre ∗ hookRun P f Pre Q' ∗ (Q' ={⊤}=∗ P ∗ Post) ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
        <{ mvccState γ (if σ.crev < sint.Z rev ∧ sint.Z rev ≤ (σ.rev : Int)
              then σ.compactTo (sint.Z rev) else σ), COMM Q σ }> }}
    (App (App (Val #(methods ty go!"Compact" v)) (Val #trace)) (Val #rev))
  {{ (ch : GoChan) (err : GoInterface), RET (PairV #ch #err);
      mvccOpen γ ∗ threadTok ∗ traceutil.ownTrace trace te ∗ mvccBackend γ q B P ∗
      ∃ σ : MvccState, Q σ ∗
      ((⌜err = GoInterface.nil ∧ σ.crev < sint.Z rev ∧ sint.Z rev ≤ (σ.rev : Int)⌝ ∗ Post ∗ Y ∗
          compactChanOk ch) ∨
       (⌜sint.Z rev ≤ σ.crev⌝ ∗ globalAddr ErrCompacted ↦□ err ∗ Pre ∗ X ∗ compactChanOk ch) ∨
       (⌜(σ.rev : Int) < sint.Z rev ∧ ch = chan.nil⌝ ∗ globalAddr ErrFutureRev ↦□ err ∗ Pre ∗ X)) }}

/-- **`Commit()`**: the backend's forced commit (`X` to `Y`). -/
abbrev KV.Commit.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (q : Qp) (B : BkRef) (Pk X Y : IProp GF),
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗ threadTok ∗ mvccBackend γ q B Pk ∗ X ∗
      backend.commitReq B.γB B.P Pk B.b X Y }}
    (App (Val #(methods ty go!"Commit" v)) (Val #()))
  {{ RET #(); threadTok ∗ mvccBackend γ q B Pk ∗ Y }}

/-- **`Restore(b')`** from the backend `B'` holding the history `σ'.log` compacted at `σ'.crev`
(decision 3, the user, 2026-11-03: at any share of the new backend's post-lock hook): by the
caller's update, at a state whose history `σ'`'s extends (the compaction revision not lowered), the
state `σ'`; the store's backend now `B'`, the old one's reader slots' open shares back (`Restore` waits out
every transaction, the scheduler and the sync loops); the lessor's items re-attached (the restored history's receipt is inside `mvccBackendFor`, from
the image `mvccImage`, round 16, and the update is given it, as at every step that changes the
history; the history's length bound follows from it, a committed revision never being empty). When
the image
records an unfinished compaction (`u`), `Restore` resumes it: under the new backend's batch lock,
running its post-lock hook `f` once (from `Pre` to `Q'`, giving the lock's invariant `Pk'` back), and
committing once (the new backend's commit request, `X` to `Y`); otherwise neither, and `Pre`, `X`
come back. The hook at any share `dq` (`plHookAt`), given back: unset and owned (`plHook B'.γB nil`,
etcd's order: it sets the new backend's hook after `Restore`, `server.go:1078`), or frozen at any
hook (`plHookRO`). -/
abbrev KV.Restore.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (B B' : BkRef) (Pk Pk' : IProp GF) (σ' : MvccState) (u : Bool) (L : List w64)
    (dq : DFrac) (f : GoFunc) (Pre Q' Post X Y : IProp GF) (Q : MvccState → IProp GF),
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗ threadTok ∗ mvccOpen γ ∗ mvccBackend γ 1 B Pk ∗
      mvccBackendFor B' Pk' σ'.log σ'.crev u ∗
      ⌜MvccReachable σ' ∧ σ'.pending = none⌝ ∗
      backend.plHookAt B'.γB dq f ∗ Pre ∗ hookRun Pk' f Pre Q' ∗ (Q' ={⊤}=∗ Pk' ∗ Post) ∗
      X ∗ backend.commitReq B'.γB B'.P Pk' B'.b X Y ∗
      lease.leaseOwn (mvccLeases γ) L ∅ ∗
      ⌜∀ it lid, (pendItems σ'.log []).lookup it = some lid →
        lid ∈ L ∧ (it.Key'.length : Int) < 2 ^ 63 - 1⌝ ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ ∗ ⌜σ.log <+: σ'.log ∧ σ.crev ≤ σ'.crev⌝ }>
          @ ⊤ \ ↑mvccN, ∅ <{ mvccState γ σ' ∗ ⧖ (logCh σ'.log), COMM Q σ }> }}
    (App (Val #(methods ty go!"Restore" v))
      (Val #(interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #B'.b)))
  {{ RET #(GoInterface.nil); threadTok ∗ mvccOpen γ ∗ mvccBackend γ 1 B' Pk' ∗
      ([∗list] _x ∈ List.replicate backend.rdStockN (), backend.bOpen B.γB backend.rdOpen) ∗
      backend.plHookAt B'.γB dq f ∗
      (if u then iprop(Post ∗ Y) else iprop(Pre ∗ X)) ∗
      lease.leaseOwn (mvccLeases γ) L (pendItems σ'.log []) ∗ ∃ σ : MvccState, Q σ }}

/-- **`HashStorage()`**: the store's hash storage (its `Store` does not panic). -/
abbrev KV.HashStorage.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName),
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ }}
    (App (Val #(methods ty go!"HashStorage" v)) (Val #()))
  {{ (h : GoInterface), RET #h; hashStoreOk h }}

/-- **`Close()`**: the whole open token; `nil`. **Shutdown is out of scope** (the user, 2026-11-03):
nothing about the backend comes back, so no proof closes the backend after the store. The store's
half of the backend's open token cannot come back here anyway: `store.Close` takes no lock and a
read may still hold a reader's part of it, which is etcd's shutdown crash
(`issues/etcd-read-after-backend-close-panic.md`). This minimal contract stays because etcd's linked
`NewServer` calls `kv.Close()` on its error path. -/
abbrev KV.Close.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName),
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗ mvccOpen γ }}
    (App (Val #(methods ty go!"Close" v)) (Val #()))
  {{ RET #(GoInterface.nil); True }}

/-- **`NewWatchStream()`**: a stream of the store, open, without watchers, nothing received. -/
abbrev WatchableKV.NewWatchStream.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName),
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ }}
    (App (Val #(methods ty go!"NewWatchStream" v)) (Val #()))
  {{ (ws : GoInterface), RET #ws;
      ∃ ι : WsName, isMvccWatchStream ws γ ι ∗ wsState ι wsStart ∗ wsRecv ι [] }}

/-! ### `TxnRead`, `TxnWrite` -/

abbrev Txn.Rev.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (trace : Loc) (k : MTxn),
  {{ pkgInit ∗ mvccTxn (interface.mkOk ty v) γ trace k }}
    (App (Val #(methods ty go!"Rev" v)) (Val #()))
  {{ RET #(W64 (k.state.rev : Int) : w64); mvccTxn (interface.mkOk ty v) γ trace k }}

/-- A read transaction's compaction revision; a write transaction's `0`. -/
abbrev Txn.FirstRev.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (trace : Loc) (k : MTxn),
  {{ pkgInit ∗ mvccTxn (interface.mkOk ty v) γ trace k }}
    (App (Val #(methods ty go!"FirstRev" v)) (Val #()))
  {{ RET #(match k with
      | .read σ => (W64 σ.crev : w64)
      | .write _ _ => (W64 0 : w64)); mvccTxn (interface.mkOk ty v) γ trace k }}

abbrev Txn.Range.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (trace : Loc) (te : Bool) (k : MTxn) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (todo : Bool) (key endk : GoSlice) (kk e : GoString)
    (ro : RangeOptions),
  {{ pkgInit ∗ mvccTxn (interface.mkOk ty v) γ trace k ∗ traceutil.ownTrace trace te ∗
      rangeCtx todo ctx cd ∗ key ↦*□ kk ∗ endk ↦*□ e }}
    (App (App (App (App (Val #(methods ty go!"Range" v)) (Val #(GoInterface.ok ctx))) (Val #key))
      (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      ⌜todo = true → r ≠ null⌝ ∗ mvccTxn (interface.mkOk ty v) γ trace k ∗
      traceutil.ownTrace trace te ∗
      rangeOutcomeC r err k.readLog k.readRev k.state.crev (decide (endk = slice.nil)) kk e ro ∗
      ⌜∀ r' : Nat, k.state.crev ≤ (r' : Int) → r' + 1 ≤ k.readLog.length →
        stateOk (stateAt k.readLog r')⌝ }}

abbrev Txn.Put.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (trace : Loc) (te : Bool) (σ : MvccState) (pend : List Change)
    (key value : GoSlice) (k vv : GoString) (leaseID : w64) (L : List w64),
  {{ pkgInit ∗ mvccTxn (interface.mkOk ty v) γ trace (.write σ pend) ∗ traceutil.ownTrace trace te ∗
      key ↦*□ k ∗ value ↦*□ vv ∗ ⌜(k.length : Int) < 2 ^ 63 - 1⌝ ∗
      lease.leaseOwn (mvccLeases γ) L (pendItems σ.log pend) ∗ ⌜leaseID = W64 0 ∨ leaseID ∈ L⌝ }}
    (App (App (App (Val #(methods ty go!"Put" v)) (Val #key)) (Val #value)) (Val #leaseID))
  {{ RET #(W64 (σ.log.length : Int) : w64);
      mvccTxn (interface.mkOk ty v) γ trace (.write σ (pend ++ [.put k vv leaseID])) ∗
      traceutil.ownTrace trace te ∗
      lease.leaseOwn (mvccLeases γ) L (pendItems σ.log (pend ++ [.put k vv leaseID])) }}

abbrev Txn.DeleteRange.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (trace : Loc) (σ : MvccState) (pend : List Change) (key endk : GoSlice)
    (k e : GoString) (L : List w64),
  let ds := (delKeys σ.log pend (decide (endk = slice.nil)) k e).map Change.del
  {{ pkgInit ∗ mvccTxn (interface.mkOk ty v) γ trace (.write σ pend) ∗ key ↦*□ k ∗ endk ↦*□ e ∗
      lease.leaseOwn (mvccLeases γ) L (pendItems σ.log pend) }}
    (App (App (Val #(methods ty go!"DeleteRange" v)) (Val #key)) (Val #endk))
  {{ (n rev : w64), RET (PairV #n #rev);
      mvccTxn (interface.mkOk ty v) γ trace (.write σ (pend ++ ds)) ∗
      lease.leaseOwn (mvccLeases γ) L (pendItems σ.log (pend ++ ds)) ∗
      ⌜n = W64 (ds.length : Int) ∧ rev = W64 ((writeRev σ.log (pend ++ ds) : Nat) : Int)⌝ }}

abbrev Txn.Changes.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (trace : Loc) (k : MTxn),
  {{ pkgInit ∗ mvccTxn (interface.mkOk ty v) γ trace k }}
    (App (Val #(methods ty go!"Changes" v)) (Val #()))
  {{ (chs : GoSlice), RET #chs; mvccTxn (interface.mkOk ty v) γ trace k ∗
      ⌜uint.nat chs.len = k.pend.length⌝ }}

/-- A read transaction's gives the thread token back; a write transaction's commits in two steps of
the caller's updates at the state it began at (`σ₀`), with the batch lock's invariant `P` back. The
notify step gives the update the receipt of the history it makes (`⧖ (logCh ..)`, round 16: what the
caller's model of the history needs, client/v3's `kvLogOk`, at the step that makes it; `Put`,
`DeleteRange` and `Restore` too). -/
abbrev Txn.End.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (trace : Loc) (k : MTxn) (q : Qp) (B : BkRef) (P Q : IProp GF),
  {{ pkgInit ∗ mvccTxn (interface.mkOk ty v) γ trace k ∗
      match k with
      | .read _ => iprop(True)
      | .write σ₀ pend => iprop(mvccBackend γ q B P ∗ P ∗
          AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
            <{ ⌜σ = σ₀⌝ ∗ mvccState γ (σ.notify pend) ∗ ⧖ (logCh (σ.log ++ [pend])), COMM
                AU <{ ∃∃ (σ' : MvccState), mvccState γ σ' }> @ ⊤ \ ↑mvccN, ∅
                  <{ ⌜σ' = σ₀.notify pend⌝ ∗ mvccState γ σ'.commitPending, COMM Q }> }>) }}
    (App (Val #(methods ty go!"End" v)) (Val #()))
  {{ RET #(); threadTok ∗
      match k with
      | .read _ => iprop(True)
      | .write _ _ => iprop(mvccBackend γ q B P ∗ Q) }}

/-! ### `WatchStream` -/

/-- **`Watch(ctx, 0, key, end, startRev, fcs...)`** (the id the stream's; a start revision not
negative): an empty range, `ErrEmptyWatcherRange`, the update back; else the caller's update over
the store's state (unchanged) and the stream's: closed, unchanged (`ErrEmptyWatcherRange`); open, a
watcher registered under a fresh id, of the range, filtered by `fs`, from `watchLo σ startRev`,
after the `k` responses sent so far, live. -/
abbrev WatchStream.Watch.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (ι : WsName) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key endk fcs : GoSlice) (kk e : List w8) (fs : List (EvM → Bool)) (startRev : w64)
    (Q : MvccState → StreamState → w64 → IProp GF),
  let au := iprop(AU <{ ∃∃ (σ : MvccState) (S : StreamState), mvccState γ σ ∗ wsState ι S }>
      @ ⊤ \ ↑mvccN, ∅
    <{ ∀∀ (id : w64) (k : Nat), mvccState γ σ ∗
        (if S.closed then ⌜id = W64 (-1)⌝ ∗ wsState ι S
         else ⌜S.ws !! id = none ∧ id ≠ W64 (-1) ∧ σ.pending = none⌝ ∗ wsSentLb ι k ∗
           wsState ι (S.register id
             ⟨watchRangeOf kk e endk startRev id, fs, watchLo σ startRev, k, true⟩)),
      COMM Q σ S id }>)
  {{ pkgInit ∗ isMvccWatchStream (interface.mkOk ty v) γ ι ∗ threadTok ∗ context.isContext ctx cd ∗
      key ↦*□ kk ∗ endk ↦*□ e ∗ filtersImpl fcs fs ∗ ⌜0 ≤ sint.Z startRev⌝ ∗ au }}
    (App (App (App (App (App (App (Val #(methods ty go!"Watch" v)) (Val #(GoInterface.ok ctx)))
      (Val #(W64 0))) (Val #key)) (Val #endk)) (Val #startRev)) (Val #fcs))
  {{ (id : w64) (err : GoInterface), RET (PairV #id #err); threadTok ∗
      ((⌜e ≠ [] ∧ ¬ go.GoStringLt kk e ∧ id = W64 (-1)⌝ ∗ globalAddr ErrEmptyWatcherRange ↦□ err ∗
          au) ∨
       (⌜e = [] ∨ go.GoStringLt kk e⌝ ∗ ∃ (σ : MvccState) (S : StreamState), Q σ S id ∗
          (if S.closed then globalAddr ErrEmptyWatcherRange ↦□ err
           else ⌜err = GoInterface.nil⌝))) }}

abbrev WatchStream.Chan.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (ι : WsName),
  {{ pkgInit ∗ isMvccWatchStream (interface.mkOk ty v) γ ι }}
    (App (Val #(methods ty go!"Chan" v)) (Val #()))
  {{ (ch : GoChan), RET #ch; ⌜ch = wsChanOf ι⌝ }}

abbrev WatchStream.RequestProgress.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (ι : WsName) (id : w64),
  {{ pkgInit ∗ isMvccWatchStream (interface.mkOk ty v) γ ι ∗ threadTok }}
    (App (Val #(methods ty go!"RequestProgress" v)) (Val #id))
  {{ RET #(); threadTok }}

abbrev WatchStream.RequestProgressAll.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (ι : WsName),
  {{ pkgInit ∗ isMvccWatchStream (interface.mkOk ty v) γ ι ∗ threadTok }}
    (App (Val #(methods ty go!"RequestProgressAll" v)) (Val #()))
  {{ (b : Bool), RET #b; threadTok }}

/-- By the caller's update (at its first check), the watcher `id`, if any, not live; `nil` only for
a watcher of an open stream; `ErrWatcherNotExist` never for a live watcher of an open stream. -/
abbrev WatchStream.Cancel.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (ι : WsName) (id : w64) (Q : StreamState → IProp GF),
  {{ pkgInit ∗ isMvccWatchStream (interface.mkOk ty v) γ ι ∗ threadTok ∗
      AU <{ ∃∃ (S : StreamState), wsState ι S }> @ ⊤ \ ↑mvccN, ∅
        <{ wsState ι (S.cancel id), COMM Q S }> }}
    (App (Val #(methods ty go!"Cancel" v)) (Val #id))
  {{ (err : GoInterface), RET #err; threadTok ∗ ∃ S : StreamState, Q S ∗
      ((⌜err = GoInterface.nil ∧ (S.ws !! id).isSome ∧ S.closed = false⌝) ∨
       (⌜∀ w, S.ws !! id = some w → w.live = true → S.closed = true⌝ ∗
          globalAddr ErrWatcherNotExist ↦□ err)) }}

/-- Of an open stream (a second `Close` panics), by the caller's update: closed. -/
abbrev WatchStream.Close.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (ι : WsName) (Q : StreamState → IProp GF),
  {{ pkgInit ∗ isMvccWatchStream (interface.mkOk ty v) γ ι ∗ threadTok ∗
      AU <{ ∃∃ (S : StreamState), wsState ι S ∗ ⌜S.closed = false⌝ }> @ ⊤ \ ↑mvccN, ∅
        <{ wsState ι S.close, COMM Q S }> }}
    (App (Val #(methods ty go!"Close" v)) (Val #()))
  {{ RET #(); threadTok ∗ ∃ S : StreamState, Q S }}

abbrev WatchStream.Rev.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (ι : WsName) (Q : MvccState → IProp GF),
  {{ pkgInit ∗ isMvccWatchStream (interface.mkOk ty v) γ ι ∗ threadTok ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅ <{ mvccState γ σ, COMM Q σ }> }}
    (App (Val #(methods ty go!"Rev" v)) (Val #()))
  {{ (r : w64), RET #r; threadTok ∗ ∃ σ : MvccState, Q σ ∗ ⌜r = W64 (σ.rev : Int)⌝ }}

/-! ### The bundles (an interface value's methods meet the contracts; cf. `sync.isLocker`) -/

abbrev isKV (ty : go.GoType) (v : val) : Prop :=
  KV.Read.contract (GF := GF) ty v ∧ KV.Write.contract (GF := GF) ty v ∧
  KV.Rev.contract (GF := GF) ty v ∧ KV.FirstRev.contract (GF := GF) ty v ∧
  KV.Range.contract (GF := GF) ty v ∧ KV.Put.contract (GF := GF) ty v ∧
  KV.DeleteRange.contract (GF := GF) ty v ∧ KV.Compact.contract (GF := GF) ty v ∧
  KV.Commit.contract (GF := GF) ty v ∧ KV.Restore.contract (GF := GF) ty v ∧
  KV.HashStorage.contract (GF := GF) ty v ∧ KV.Close.contract (GF := GF) ty v

abbrev isWatchableKV (ty : go.GoType) (v : val) : Prop :=
  isKV (GF := GF) ty v ∧ WatchableKV.NewWatchStream.contract (GF := GF) ty v

abbrev isTxn (ty : go.GoType) (v : val) : Prop :=
  Txn.Rev.contract (GF := GF) ty v ∧ Txn.FirstRev.contract (GF := GF) ty v ∧
  Txn.Range.contract (GF := GF) ty v ∧ Txn.Put.contract (GF := GF) ty v ∧
  Txn.DeleteRange.contract (GF := GF) ty v ∧ Txn.Changes.contract (GF := GF) ty v ∧
  Txn.End.contract (GF := GF) ty v

abbrev isWatchStream (ty : go.GoType) (v : val) : Prop :=
  WatchStream.Watch.contract (GF := GF) ty v ∧ WatchStream.Chan.contract (GF := GF) ty v ∧
  WatchStream.RequestProgress.contract (GF := GF) ty v ∧
  WatchStream.RequestProgressAll.contract (GF := GF) ty v ∧
  WatchStream.Cancel.contract (GF := GF) ty v ∧ WatchStream.Close.contract (GF := GF) ty v ∧
  WatchStream.Rev.contract (GF := GF) ty v

end contracts

/-! ## The canonical specs, per (type, method): the contract at the type

Store types `store`, `watchableStore` (`KV`'s methods; `watchableStore` also `NewWatchStream`;
`Read`, `Rev`, `FirstRev`, `Range`, `Put`, `DeleteRange`, `Compact`, `Commit`, `HashStorage` of
`watchableStore` are promoted from its `store`, and `Rev`, `FirstRev`, `Range`, `Put`,
`DeleteRange` of `store` from its views); transaction types `metricsTxnWrite`,
`watchableStoreTxnWrite`, `txnReadWrite` (`Txn`'s; promoted where Go promotes); `watchStream`.
Internal, with today's specs kept (no client holds their receivers): `readView.*`, `writeView.*`,
`hashStorage.Store` (an axiom), `NewHashStorage`, and every helper. -/

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc
local notation "PS" => go.GoType.PointerType store.ty
local notation "PW" => go.GoType.PointerType watchableStore.ty
local notation "PM" => go.GoType.PointerType metricsTxnWrite.ty
local notation "PT" => go.GoType.PointerType watchableStoreTxnWrite.ty
local notation "PR" => go.GoType.PointerType txnReadWrite.ty
local notation "PWS" => go.GoType.PointerType watchStream.ty

abbrev store.Read.spec : Prop := ∀ s : Loc, KV.Read.contract (GF := GF) PS #s
abbrev store.Write.spec : Prop := ∀ s : Loc, KV.Write.contract (GF := GF) PS #s
abbrev store.Rev.spec : Prop := ∀ s : Loc, KV.Rev.contract (GF := GF) PS #s
abbrev store.FirstRev.spec : Prop := ∀ s : Loc, KV.FirstRev.contract (GF := GF) PS #s
abbrev store.Range.spec : Prop := ∀ s : Loc, KV.Range.contract (GF := GF) PS #s
abbrev store.Put.spec : Prop := ∀ s : Loc, KV.Put.contract (GF := GF) PS #s
abbrev store.DeleteRange.spec : Prop := ∀ s : Loc, KV.DeleteRange.contract (GF := GF) PS #s
abbrev store.Compact.spec : Prop := ∀ s : Loc, KV.Compact.contract (GF := GF) PS #s
abbrev store.Commit.spec : Prop := ∀ s : Loc, KV.Commit.contract (GF := GF) PS #s
abbrev store.Restore.spec : Prop := ∀ s : Loc, KV.Restore.contract (GF := GF) PS #s
abbrev store.HashStorage.spec : Prop := ∀ s : Loc, KV.HashStorage.contract (GF := GF) PS #s
abbrev store.Close.spec : Prop := ∀ s : Loc, KV.Close.contract (GF := GF) PS #s

abbrev watchableStore.Read.spec : Prop := ∀ s : Loc, KV.Read.contract (GF := GF) PW #s
abbrev watchableStore.Write.spec : Prop := ∀ s : Loc, KV.Write.contract (GF := GF) PW #s
abbrev watchableStore.Rev.spec : Prop := ∀ s : Loc, KV.Rev.contract (GF := GF) PW #s
abbrev watchableStore.FirstRev.spec : Prop := ∀ s : Loc, KV.FirstRev.contract (GF := GF) PW #s
abbrev watchableStore.Range.spec : Prop := ∀ s : Loc, KV.Range.contract (GF := GF) PW #s
abbrev watchableStore.Put.spec : Prop := ∀ s : Loc, KV.Put.contract (GF := GF) PW #s
abbrev watchableStore.DeleteRange.spec : Prop := ∀ s : Loc, KV.DeleteRange.contract (GF := GF) PW #s
abbrev watchableStore.Compact.spec : Prop := ∀ s : Loc, KV.Compact.contract (GF := GF) PW #s
abbrev watchableStore.Commit.spec : Prop := ∀ s : Loc, KV.Commit.contract (GF := GF) PW #s
abbrev watchableStore.Restore.spec : Prop := ∀ s : Loc, KV.Restore.contract (GF := GF) PW #s
abbrev watchableStore.HashStorage.spec : Prop := ∀ s : Loc, KV.HashStorage.contract (GF := GF) PW #s
abbrev watchableStore.Close.spec : Prop := ∀ s : Loc, KV.Close.contract (GF := GF) PW #s
abbrev watchableStore.NewWatchStream.spec : Prop :=
  ∀ s : Loc, WatchableKV.NewWatchStream.contract (GF := GF) PW #s

/-- The three transaction types, each method: `Txn.<M>.contract` at the type. A read transaction's
dynamic type is a write transaction's (`*metricsTxnWrite`): the write contracts rest on the kind
`mvccTxn` records. For `txnReadWrite`'s `Put`/`DeleteRange`, which panic, the contract holds
vacuously: no read-only transaction has a write view. -/
abbrev metricsTxnWrite.Put.spec : Prop := ∀ t : Loc, Txn.Put.contract (GF := GF) PM #t
abbrev watchableStoreTxnWrite.Put.spec : Prop := ∀ t : Loc, Txn.Put.contract (GF := GF) PT #t
abbrev txnReadWrite.Put.spec : Prop := ∀ t : Loc, Txn.Put.contract (GF := GF) PR #t
abbrev metricsTxnWrite.End.spec : Prop := ∀ t : Loc, Txn.End.contract (GF := GF) PM #t
abbrev watchableStoreTxnWrite.End.spec : Prop := ∀ t : Loc, Txn.End.contract (GF := GF) PT #t
abbrev txnReadWrite.End.spec : Prop := ∀ t : Loc, Txn.End.contract (GF := GF) PR #t
-- (and likewise `Rev`, `FirstRev`, `Range`, `DeleteRange`, `Changes` of each of the three)

abbrev watchStream.Watch.spec : Prop := ∀ w : Loc, WatchStream.Watch.contract (GF := GF) PWS #w
-- (and likewise `Chan`, `RequestProgress`, `RequestProgressAll`, `Cancel`, `Close`, `Rev`)

/-- **`mvcc.New(lg, be, le, cfg)`**: the watchable store over the backend `B` (holding the empty
history), with the real lessor; the state at `mvccStart`, the open token, the backend's token, the
range deleter. Each reader of the store (a read transaction, the compaction's job, the sync
loops, a progress request's read) holds a thread token and one of the backend's counted reader
slots, of which the store has `rdStockN` (about `3 · 2 ^ 28`; the rest of the `2 ^ 30 - 1` Go's
`RWMutex` admits are the client's pool): so at most `rdStockN` threads (the review of round 13's
decisions, D1; the server has `threadBound ≤ 2 ^ 28`). -/
abbrev New.spec : Prop :=
  ∀ (lg : Loc) (le : GoInterface) (cfg : StoreConfig) (B : BkRef) (Pk : IProp GF)
    (γl : GName) (rd0 : GoFunc),
  batchLimitOk cfg.CompactionBatchLimit' → receiptBound GF ≤ 2 ^ 48 → threadBound GF ≤ backend.rdStockN →
  {{ pkgInit ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      mvccBackendFor B Pk mvccStart.log mvccStart.crev false ∗
      lease.lessorRdOf γl ∗ isLessor le γl ∗ lease.rdOwn γl rd0 }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.New)) (Val #lg))
      (Val #(interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #B.b)))
      (Val #le)) (Val #cfg))
  {{ (ws : Loc), RET #(interface.mkOk PW #ws);
      ∃ γ : MvccName, ⌜mvccLeases γ = γl⌝ ∗
        isMvcc (interface.mkOk PW #ws) γ ∗ mvccState γ mvccStart ∗ mvccOpen γ ∗
        mvccBackend γ 1 B Pk ∗ (∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvccDeleter rd γ) }}

/-- **`mvcc.NewStore(lg, be, le, cfg)`**: as `New`, a store without watchers. -/
abbrev NewStore.spec : Prop :=
  ∀ (lg : Loc) (le : GoInterface) (cfg : StoreConfig) (B : BkRef) (Pk : IProp GF)
    (γl : GName) (rd0 : GoFunc),
  batchLimitOk cfg.CompactionBatchLimit' → receiptBound GF ≤ 2 ^ 48 → threadBound GF ≤ backend.rdStockN →
  {{ pkgInit ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      mvccBackendFor B Pk mvccStart.log mvccStart.crev false ∗
      lease.lessorRdOf γl ∗ isLessor le γl ∗ lease.rdOwn γl rd0 }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewStore)) (Val #lg))
      (Val #(interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #B.b)))
      (Val #le)) (Val #cfg))
  {{ (s : Loc), RET #s;
      ∃ γ : MvccName, ⌜mvccLeases γ = γl⌝ ∗
        isMvcc (interface.mkOk PS #s) γ ∗ mvccState γ mvccStart ∗ mvccOpen γ ∗
        mvccBackend γ 1 B Pk ∗ (∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvccDeleter rd γ) }}

/-- **`mvcc.NewReadOnlyTxnWrite(t)`** of a read transaction. -/
abbrev NewReadOnlyTxnWrite.spec : Prop :=
  ∀ (t : GoInterface) (γ : MvccName) (trace : Loc) (σ : MvccState),
  {{ pkgInit ∗ mvccTxn t γ trace (.read σ) }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewReadOnlyTxnWrite)) (Val #t))
  {{ (t' : GoInterface), RET #t'; mvccTxn t' γ trace (.read σ) }}

end specs

/-! ## The laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

abbrev persistent.law : Prop :=
  (∀ kv γ, Persistent (isMvcc (GF := GF) kv γ)) ∧
  (∀ ws γ ι, Persistent (isMvccWatchStream (GF := GF) ws γ ι)) ∧
  (∀ ι n, Persistent (wsSentLb (GF := GF) ι n)) ∧
  (∀ D L c u, Persistent (mvccImage (GF := GF) D L c u)) ∧
  (∀ γ σ, Timeless (mvccState (GF := GF) γ σ)) ∧ (∀ ι S, Timeless (wsState (GF := GF) ι S)) ∧
  (∀ ι rs, Timeless (wsRecv (GF := GF) ι rs)) ∧
  (∀ γ B Pk, Fractional (fun q => mvccBackend (GF := GF) γ q B Pk))

abbrev excl.law : Prop :=
  (∀ γ σ σ', mvccState (GF := GF) γ σ ∗ mvccState γ σ' ⊢ False) ∧
  (∀ ι S S', wsState (GF := GF) ι S ∗ wsState ι S' ⊢ False) ∧
  (∀ ι rs rs', wsRecv (GF := GF) ι rs ∗ wsRecv ι rs' ⊢ False) ∧
  (∀ γ, mvccOpen (GF := GF) γ ∗ mvccOpen γ ⊢ False)

/-- **A registration name**, before the backend is opened. -/
abbrev mvccW_alloc.law : Prop := ⊢ |==> ∃ gx : GName, mvccWReg (GF := GF) gx

/-- **The store's part of an opened backend** (decision 2, the user, 2026-11-03: over the store's
needs, at any opener; the review of round 13's decisions: at the pooled post): what a backend's
opener returns with its reader slots pooled (`backend.newPostKP`, at whatever the client
keeps, `K`: `backend.New`'s at boot, `K := bFresh`; `storage.OpenSnapshotBackend`'s when applying a
snapshot, `K := snapOpenK`), opened at the store's write invariant `W := mvccW gx` over data `D` that
is the image of the history `L` compacted at `c` (`mvccImage`, with its receipt), with the
registration, and the
store's part of the backend's payment rights, in the backend's own terms: two write-back tokens (for
`NewStore`'s own writes) and the receipt-paid supply every later write-back and the compaction's job
draw on (`□ (⧗ 1 ={⊤}=∗ wbTok)`: on `lean` one stock, shared with the server's own writes, backs
it), and the open shares of the counted stock's reader slots (`rdStockN` of `bOpen rdOpen`; the
pool, `rdPool`, stays the client's), gives the store's resources and the client's rest. At boot they
come from `bFresh`; the snapshot path supplies them from where its proof holds them. `keySized` (fewer than `2 ^ 62` keys) stays an assumption,
as today. -/
abbrev mvccBackendFor_open.law : Prop :=
  ∀ (γB : backend.BNames) (P : backend.BParams) (Pk K : backend.BNames → IProp GF) (b : Loc)
    (D : backend.Data) (gx : GName) (L : Log) (c : Int) (u : Bool),
  □ (∀ γ b', keySized (GF := GF) γ P b') ∗ mvccImage D L c u ∗
    backend.newPostKP γB P (fun _ => mvccW gx) Pk K b D ∗ mvccWReg gx ∗
    backend.wbTok γB ∗ backend.wbTok γB ∗ □ (⧗ 1 ={⊤}=∗ backend.wbTok γB) ∗
    ([∗list] _x ∈ List.replicate backend.rdStockN (), backend.bOpen γB backend.rdOpen) ={⊤}=∗
    mvccBackendFor ⟨γB, P, b⟩ (Pk γB) L c u ∗ backendRest γB P K b D

/-- **A fresh backend's data is the image of the empty history** (round 16: `New`'s and
`NewStore`'s backend, `mvccBackendFor_open` at `mvccStart`): no change, so the receipt `⧖ 0`,
which Perennial allocates under an update (`preceipt_zero`; the review of round 16, F3). -/
abbrev mvccImage_fresh.law : Prop :=
  ∀ D : backend.Data, (∀ k, backend.dget D mvcc.keyName k = none) →
    backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName mvcc.schedKeyBytes = none →
    backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName mvcc.finKeyBytes = none →
    ⊢ |==> mvccImage (GF := GF) D mvccStart.log mvccStart.crev false

/-- The backend's shares agree. -/
abbrev mvccBackend_agree.law : Prop :=
  ∀ γ q q' B B' (Pk Pk' : IProp GF), mvccBackend (GF := GF) γ q B Pk ∗ mvccBackend γ q' B' Pk' ⊢ ⌜B = B'⌝

abbrev mvccState_reachable.law : Prop :=
  ∀ kv γ σ, isMvcc (GF := GF) kv γ ∗ mvccState γ σ ⊢ ⌜MvccReachable σ ∧ σ.log.length + 3 ≤ 2 ^ 63⌝

/-- **The names are inhabited** (the server draft's S3: a client builds a stand-in environment
before the store exists). -/
abbrev names_nonempty.law : Prop := Nonempty MvccName ∧ Nonempty WsName

/-- **The shapes and the bundles**, from the concrete specs (an implementation proves them as
`sync`'s `Mutex_is_Locker`): a store's handle, a transaction, a stream are an `interface.mkOk ty v`
whose type meets its interface's contracts (the watchable store `WatchableKV`'s too). -/
abbrev shapes.law : Prop :=
  (∀ kv γ, isMvcc (GF := GF) kv γ ⊢ ⌜∃ ty v, kv = interface.mkOk ty v ∧ isKV (GF := GF) ty v⌝) ∧
  (∀ ws : Loc, isWatchableKV (GF := GF) (go.GoType.PointerType watchableStore.ty) #ws) ∧
  (∀ t γ trace k, mvccTxn (GF := GF) t γ trace k ⊢
    ⌜∃ ty v, t = interface.mkOk ty v ∧ isTxn (GF := GF) ty v⌝) ∧
  (∀ w γ ι, isMvccWatchStream (GF := GF) w γ ι ⊢
    ⌜∃ ty v, w = interface.mkOk ty v ∧ isWatchStream (GF := GF) ty v⌝)

/-- **Receiving on the stream's channel** (round 14: the blocking and the non-blocking receive
in one law, over one channel name, the review of round 14's preference), in the forms Perennial's
channel rules take: a receive (`recvAu`: a plain receive or one in a `select`) gives the next
response (the consumer's view grown) or (`!ok`) the end of a closed, drained channel; a
non-blocking receive (`nonblockingRecvAuAlt`, a `select` with a `default`: v3rpc's drain, A2) gives
the same, or the channel empty, every response the stream had sent (at least `n`, from a
`wsSentLb ι n` taken before the poll) received. -/
abbrev wsChan_recv.law : Prop :=
  ∀ ws γ ι, isMvccWatchStream (GF := GF) ws γ ι ⊢ ∃ γch : ChanNames,
    isChan (wsChanOf ι) γch WatchResponse ∗
    □ (∀ (rs : List WResp) (Φ : WatchResponse → Bool → IProp GF),
      wsRecv ι rs -∗
      (∀ (v : WatchResponse) (ok : Bool),
        (if ok then ∃ r : WResp, wsRecv ι (rs ++ [r]) ∗ wrespIs v r else wsRecv ι rs) -∗ Φ v ok) -∗
      recvAu γch WatchResponse Φ) ∗
    □ (∀ (rs : List WResp) (n : Nat) (Φ : WatchResponse → Bool → IProp GF) (Ψ : IProp GF),
      wsRecv ι rs -∗ wsSentLb ι n -∗
      ((∀ (v : WatchResponse) (ok : Bool),
          (if ok then ∃ r : WResp, wsRecv ι (rs ++ [r]) ∗ wrespIs v r else wsRecv ι rs) -∗ Φ v ok) ∧
        (wsRecv ι rs -∗ ⌜n ≤ rs.length⌝ -∗ Ψ)) -∗
      nonblockingRecvAuAlt γch WatchResponse Φ Ψ)

/-- **The stream has sent at least nothing** (the review of round 14: v3rpc's drain before a
refused create, which has no stamp). -/
abbrev wsSentLb_zero.law : Prop := ∀ ι, ⊢ wsSentLb (GF := GF) ι 0

/-- **The lease bucket's delete inside a write transaction** (round 14, A5: `lessor.Revoke` deletes
the lease's record on the backend's batch transaction between the range deleter's `Write` and the
transaction's `End`, so that the keys' deletes and the lease's commit together): while the write
transaction is open (it holds the batch lock), an `UnsafeDelete` of the Lease bucket on the
backend's batch transaction, over the bucket rights the client owns (`backend.rbPart`, the
lessor's), leaves the store's backend as it was and the transaction able only to end (the
backend's batch session admits only `Unlock` after an `UnsafeDelete`, and the delete forces a commit
at `End`: the review of round 14): what comes back is `End`'s triple for the transaction, as
`Txn.End.contract` states it at a write view. -/
abbrev mvccTxn_leaseDelete.law : Prop :=
  ∀ (tw : GoInterfaceOk) γ trace σ pend (q : Qp) (B : BkRef) (Pk : IProp GF) (t : Loc)
    (b : GoInterface) (key : GoSlice) (k : GoString) (dq : DFrac) (S : GoString → Prop)
    (r : GMap GoString backend.BktData) (Φ : val → IProp GF),
  S leaseName →
  mvccTxn (GF := GF) (GoInterface.ok tw) γ trace (.write σ pend) ∗ mvccBackend γ q B Pk ∗
    backend.bF go!"batchTx" B.b ↦□ t ∗
    globalAddr go_etcd_io.etcd.server.v3.storage.schema.Lease ↦□ b ∗ key ↦*{dq} k ∗
    backend.rbPart B.γB S r ∗
    ▷ (mvccBackend γ q B Pk -∗ key ↦*{dq} k -∗ backend.rbPart B.γB S (rbDel r leaseName k) -∗
        (∀ (Q : IProp GF),
          {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
              mvccBackend γ q B Pk ∗ Pk ∗
              AU <{ ∃∃ (σ1 : MvccState), mvccState γ σ1 }> @ ⊤ \ ↑mvccN, ∅
                <{ ⌜σ1 = σ⌝ ∗ mvccState γ (σ1.notify pend) ∗ ⧖ (logCh (σ1.log ++ [pend])), COMM
                    AU <{ ∃∃ (σ2 : MvccState), mvccState γ σ2 }> @ ⊤ \ ↑mvccN, ∅
                      <{ ⌜σ2 = σ.notify pend⌝ ∗ mvccState γ σ2.commitPending, COMM Q }> }> }}
            (App (Val #(methods tw.ty go!"End" tw.v)) (Val #()))
          {{ RET #(); threadTok ∗ mvccBackend γ q B Pk ∗ Q }}) -∗ Φ #()) ⊢
  WP (App (App (Val #(methods (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty) go!"UnsafeDelete" #t))
      (Val #b)) (Val #key)) {{ Φ }}

abbrev wsRecv_ok.law : Prop :=
  ∀ ws γ ι rs S σ,
    isMvccWatchStream (GF := GF) ws γ ι ∗ wsRecv ι rs ∗ wsState ι S ∗ mvccState γ σ ⊢
      ⌜wsRecvOk σ S rs⌝

/-- **A reachable state's history is well formed, its notified history too** (round 16, pure, of the
API's own definitions: by induction on `MvccReachable`, `notify`'s `LogWf` and `commitLog`; the
server's read path and the watch path take their clients' `LogWf'` from it). -/
abbrev reach_logWf.law : Prop :=
  ∀ σ : MvccState, MvccReachable σ → LogWf' σ.log ∧ LogWf' σ.notifiedLog

end laws

section snapshot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [bk_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **A snapshot of the store's backend is the image of the store's history** (round 16, G3: the
sender's side of `mvccImage`, `createMergedSnapshotMessage`'s `s.be.Snapshot()`; derived from
`backend.Snapshot`'s triple). With the whole backend share held through the call (no step that
changes the history runs: each takes a share), by the caller's update at the state (nothing
pending; the state unchanged), the snapshot's data `D` is the image of that state's history and
compaction, with the store's receipt inside (`mvccImage`), recording an unfinished compaction iff
`u`; and the caller's own observation `Q` of the backend's hook keys `d` and tracked buckets `r`,
from its `R` and the batch lock's invariant `Pk`, as `backend.Snapshot`'s. Not a pin predicate (the
server draft's proposal): the update at the state is the API's one shape for reading it.

**For a store that never compacted** (`σ.crev = -1`; the review of round 16, F1): `backend.Snapshot`'s
triple reports nothing of the compaction keys once a `Compact` has written them, so the image of a
compacted store's snapshot needs a stronger backend axiom (`notes/mvcc-api-candidate.md`, round 16,
"F1"); the premise is that axiom's temporary limitation, kept at this one law (today's sender proof
covers the same: `txn/KeyObs.lean`, the no-compaction token), and dropping it later breaks no
client. The image's `u` stays existential for that. -/
abbrev mvccImage_snapshot.law : Prop :=
  backend.backend.Snapshot.spec (GF := GF) (hG := hG) →
  ∀ (kv : GoInterface) (γ : MvccName) (B : BkRef) (Pk : IProp GF) (qo : Qp) (R : IProp GF)
    (Q : GMap (GoString × GoString) GoString → GMap GoString backend.BktData → Prop)
    (Φ : MvccState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isMvcc kv γ ∗ mvccBackend γ 1 B Pk ∗ backend.bOpen B.γB qo ∗ backend.wbTok B.γB ∗ R ∗
      □ (∀ (d : GMap (GoString × GoString) GoString) (r : GMap GoString backend.BktData),
        R -∗ Pk -∗ backend.hkOwn B.γB d -∗ backend.rbOwn B.γB r -∗ ⌜Q d r⌝) ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ ∗ ⌜σ.pending = none ∧ σ.crev = -1⌝ }>
        @ ⊤ \ ↑mvccN, ∅ <{ mvccState γ σ, COMM Φ σ }> }}
    (App (Val (B.b @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty
      @!! go!"Snapshot")) (Val #()))
  {{ (sp : Loc) (D : backend.Data),
      RET #(interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.snapshot.ty) #sp);
      backend.snapOpen sp D ∗ backend.bOpen B.γB qo ∗ R ∗ mvccBackend γ 1 B Pk ∗
      ⌜Q (backend.hkData B.P D) (backend.rbData B.P D)⌝ ∗
      ∃ (σ : MvccState) (u : Bool), Φ σ ∗ mvccImage D σ.log σ.crev u }}

end snapshot

end api
end mvcc
end EtcdGrove
end Perennial
