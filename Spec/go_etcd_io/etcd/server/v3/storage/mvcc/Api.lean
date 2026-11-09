/-
# mvcc's store: the vocabulary, the interfaces' contracts and the laws (batch 3e)

The user-approved mvcc API (`specs-ref/notes/mvcc-api-candidate.md`, frozen 2026-11-03 and reopened
through 2026-11-07; the examples `c3-store-law`, `compaction-in-place`, `restore-modes`,
`writer-pin`, `oneshot-close`, `watch-compaction`), restated for the specs-only branch: every
predicate opaque, the pure model W0's history (`Model.lean`), the storage a contract
(`ApiStorage.lean`). The watch half (`NewWatchStream`, the stream, the watch guarantee) is batch 3f's
(`ApiWatch.lean`, over this file's `mvccState`).

## Vocabulary

* `MvccName` (opaque): a store's ghost names.
* `mvccState γ σ` (exclusive, timeless): **the store's state is `σ`** (`MvccState`: its history and
  the revision being committed). **The client's** (the server's apply invariant, the tester's
  writer): a read fires the caller's atomic update at the state it reads, unchanged; a write
  transaction's `End` fires two (notify, then commit); `Compact` and `Restore` one each. So the
  client's own invariant decides what the state may be (2d ties it to the cluster's history at the
  member's applied point: `req/..._etcdserver.md`, 2c's item 6). Intended realization: a ghost
  variable's half, the other in the store's invariant (`s.mu`/`s.revMu`'s, with the index, the
  current revision, the compaction revision and the storage's data at the image of `σ`).
* `isMvcc kv γ` (persistent): **`kv` (the `KV` interface value `NewStore` or `New` returned) serves
  the store `γ`**. Intended realization: the store's fields (read-only after `NewStore`), its locks'
  invariants, its views; of the watchable store (3f), the watchable store's too.
* `mvccLessorIs γ γl` (persistent): the store's lessor is `γl` (fixed at `NewStore`).
* `mvccOpen γ` (exclusive): **the store's open token**: `Compact` and `Restore` take it and give it
  back, `Close` takes it for good. Scope restriction (marked, the frozen API's): compactions are
  not concurrent with each other, with a restore or with a close (a compaction schedules its job
  after releasing `s.mu`: two concurrent ones could queue their jobs out of order; etcd compacts
  from its apply thread; the tester does not compact).
* `mvccReaders γ n` (exclusive, counted, splits): **`n` reader tokens** (the user's decision,
  2026-11-06/07: each carries a reader slot of the store's locks and of the storage): a call that
  reads takes one, a transaction keeps it until its `End`. `NewStore` gives `mvccTokN` (sealed).
* `mvccClosed γ` (exclusive): `Close`'s result; with every reader token, the storage's rest
  (`mvccClosed_rest`): the client may then close the storage.
* `mvccBackend γ q B Pk` (fractional): **a share of "the store's storage is `B`, its batch lock's
  invariant `Pk`"** (`NewStore`'s, then `Restore`'s): `Write`, `Put`, `DeleteRange`, `Compact`,
  `Commit` and a write transaction's `End` take a share (for the hook, the batch lock's invariant,
  the commit request), `Restore` the whole (and gives the new storage's).
* `mvccTxn t γ trace k` (exclusive): **`t` (a `TxnRead`/`TxnWrite` interface value) is a
  transaction of `γ`, begun with `trace`, at `k`** (`MTxn`: read, or write with its events). It
  holds the reader token until its `End`, not the trace (lent per call).
* `isHashStorage h γ` (persistent): `h` is the store's `HashStorage`.
* Provisional, **3c's** (the lessor; `req/go_etcd_io_etcd_server_v3_lease.md`, "from 3e"):
  `LessorName`, `lessorAt le γl` (persistent: `le` is the lessor `γl`, its `GetLease`, `Attach`,
  `Detach`, `SetRangeDeleter` safe from any goroutine), `leaseItems γl L I` (exclusive: the
  lessor's live leases are `L`, its item map is `I`, `0` for none; the holder may attach and
  detach), `rdSlot γl rd` (exclusive: the lessor's range deleter is `rd`).
* Provisional, **4b's** (traceutil; `req/go_etcd_io_etcd_pkg_v3_traceutil.md`, "from 3e"):
  `traceOwn tr` (exclusive): the trace `tr` is the caller's (its `Step` may be called).
* Definitions: `rangeResOwn` (a `*RangeResult` and error holding an outcome), `compactChanOk` (a
  receive on a compaction's channel does not panic), `mvccDeleter rd γ` (the range deleter
  `NewStore` hands the lessor: `KV.Write`'s triple), the contracts of the interfaces' methods at a
  receiver (`KV.<M>.contract ty v`, `Txn.<M>.contract`, `HashStorage.<M>.contract`) and their
  bundles (`isKV`, `isTxn`, `isHashStorageV`, as `sync.isLocker`).

Each (concrete type, method) has its canonical spec in its own file, the contract at its type
(PRINCIPLES, "Canonical specs are per (concrete type, method)"): `store__Read.lean`'s
`store.Read.spec := ∀ s, KV.Read.contract PS #s`, `metricsTxnWrite__Put.lean`, ...; the watchable
store's (3f) likewise.

## Laws

`persistent` (persistence, timelessness, fractions), `excl`, `init` (the error variables),
`mvccReaders_split`, `mvccClosed_rest`, `mvccStorageFor_rest`, `mvccBackend_agree`,
`mvccLessorIs_agree`, `mvccState_reachable`, `mvccTxn_state`, `shapes` (a handle, a transaction, a
hash storage meet their interface's contracts), `names_nonempty`, `mvccImage_obs` (what the storage's
data is at the store's state: the server's snapshot, 2d with 4a).

## Requirement snippets

`examples/specreq/mvcc/`: `store.go` (a sole writer's transaction pinned to its state, a reader's
floor, the read-only transaction coerced, the views), `compact.go` (compaction and its errors, the
channel), `restore.go` (boot over existing data, restore from a snapshot's storage, the leases
re-attached), `lease.go` (the range deleter, a put with a lease), `hash.go` (the hash storage).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiStorage
public import Spec.context.Api
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.storage.mvcc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire
open go_etcd_io.etcd.server.v3.storage.mvcc

/-- A store's ghost names (opaque). -/
opaque MvccName : Type := Unit

/-- **Provisional (3c):** a lessor's ghost names. -/
opaque LessorName : Type := Unit

/-- The namespace of the store's invariants (a library with invariants reserves one: a stated
departure from "no internal namespaces in masks"). -/
def mvccN : Namespace := nroot .@ "mvcc"

/-- **The number of reader tokens a new store gives** (sealed). -/
opaque mvccTokN : Nat

/-- **The store's configuration** (`StoreConfig`): a non-negative compaction batch limit (the
user's call, 2026-11-02: a negative one makes every compaction run forever,
`nonissues/etcd-compaction-negative-batch-limit.md`; a precondition rather than a fix). The server's
slot `EtcdServer.mvccBootCfg cfg` is this of `cfg.CompactionBatchLimit`. -/
def storeCfgOk [GooseExts] (cfg : go_etcd_io.etcd.server.v3.storage.mvcc.StoreConfig) : Prop :=
  0 ≤ sint.Z cfg.CompactionBatchLimit'

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **The store's state is `σ`** (exclusive; the client's). -/
opaque mvccState (γ : MvccName) (σ : MvccState) : IProp GF := iprop(True)

/-- **`kv` serves the store `γ`** (persistent). -/
opaque isMvcc (kv : GoInterface) (γ : MvccName) : IProp GF := iprop(True)

/-- The store's lessor is `γl` (persistent). -/
opaque mvccLessorIs (γ : MvccName) (γl : LessorName) : IProp GF := iprop(True)

/-- **The store's open token** (exclusive). -/
opaque mvccOpen (γ : MvccName) : IProp GF := iprop(True)

/-- **`n` reader tokens** (exclusive, counted). -/
opaque mvccReaders (γ : MvccName) (n : Nat) : IProp GF := iprop(True)

/-- **The store is closed** (`Close`'s result). -/
opaque mvccClosed (γ : MvccName) : IProp GF := iprop(True)

/-- **A share `q` of "the store's storage is `B`, its batch lock's invariant `Pk`"**. -/
opaque mvccBackend (γ : MvccName) (q : Qp) (B : MvccStorage) (Pk : IProp GF) : IProp GF := iprop(True)

/-- **`t` is a transaction of `γ`, begun with `trace`, at `k`** (exclusive). -/
opaque mvccTxn (t : GoInterface) (γ : MvccName) (trace : Loc) (k : MTxn) : IProp GF := iprop(True)

/-- `h` is the store's hash storage (persistent). -/
opaque isHashStorage (h : GoInterface) (γ : MvccName) : IProp GF := iprop(True)

/-- **Provisional (3c):** `le` is the lessor `γl` (persistent). -/
opaque lessorAt (le : GoInterface) (γl : LessorName) : IProp GF := iprop(True)

/-- **Provisional (3c):** the lessor's live leases are `L`, its item map `I` (exclusive). -/
opaque leaseItems (γl : LessorName) (L : List Int) (I : Key → Int) : IProp GF := iprop(True)

/-- **Provisional (3c):** the lessor's range deleter is `rd` (exclusive). -/
opaque rdSlot (γl : LessorName) (rd : GoFunc) : IProp GF := iprop(True)

/-- **Provisional (4b):** the trace `tr` is the caller's (exclusive). -/
opaque traceOwn (tr : Loc) : IProp GF := iprop(True)

/-- **A `*RangeResult` `r` and an error `err` holding the outcome `out`** of a range under the
context `ctx` (the key-values fresh, the caller's; their key and value bytes read-only: a keys-only
read shares the index's key slices). -/
def rangeResOwn (ctx : GoInterface) (r : Loc) (err : GoInterface) : RangeOut → IProp GF
  | .ok kvs count rev => iprop(⌜err = GoInterface.nil⌝ ∗ ∃ sl : GoSlice,
      r ↦ ({ KVs' := sl, Rev' := W64 rev, Count' := W64 count } : RangeResult) ∗
      msgsOwn keyValueOwn sl (DFrac.own 1) kvs)
  | .futureRev cur => iprop(globalAddr ErrFutureRev ↦□ err ∗
      r ↦ ({ KVs' := slice.nil, Rev' := W64 cur, Count' := W64 (-1) } : RangeResult))
  | .compacted => iprop(globalAddr ErrCompacted ↦□ err ∗
      r ↦ ({ KVs' := slice.nil, Rev' := W64 0, Count' := W64 (-1) } : RangeResult))
  | .ctxErr => iprop(⌜r = null ∧ err ≠ GoInterface.nil⌝ ∗ Context.ctxDone ctx)

/-- A compaction's channel: a receive on it does not panic (it is closed once the compaction's job
has run, or never: a `nil` channel, a stopped scheduler). -/
def compactChanOk (ch : GoChan) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ v : val, Φ v) -∗
    WP (App (Val (chan.receive (go.GoType.StructType []))) (Val #ch)) {{ Φ }})

/-- **The lessor's range deleter is the store's `Write(traceutil.TODO())`** (not `nil`: `Revoke`
checks it): `rd()`'s triple is `KV.Write`'s, with a fresh trace. -/
def mvccDeleter (rd : GoFunc) (γ : MvccName) : IProp GF :=
  iprop(⌜rd ≠ func.nil⌝ ∗ □ ∀ (q : Qp) (B : MvccStorage) (Pk Pre Q : IProp GF) (f : GoFunc)
      (R : MvccState → IProp GF) (Φ : val → IProp GF),
    mvccReaders γ 1 -∗ mvccBackend γ q B Pk -∗ hookIs B f -∗ Pre -∗ hookRun Pk f Pre Q -∗
    (AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
      <{ ⌜σ.pending = []⌝ ∗ mvccState γ σ, COMM R σ }>) -∗
    ▷ (∀ t : GoInterface, mvccBackend γ q B Pk -∗ Q -∗
        (∃ (trace : Loc) (σ : MvccState), traceOwn trace ∗ mvccTxn t γ trace (.write σ []) ∗ R σ) -∗
        Φ #t) -∗
    WP (App (Val #rd) (Val #())) {{ Φ }})

end vocab

/-! ## The contracts of the interfaces' methods, at a receiver `interface.mkOk ty v` -/

section contracts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc

/-- mvcc's range of `(key, end)` with `end`'s bytes `e`. -/
abbrev mrange (kk : Key) (endk : GoSlice) (e : Bytes) : MRange := ⟨kk, decide (endk = slice.nil), e⟩

/-! ### `KV` (and `WatchableKV`'s `KV` part) -/

/-- **`Read(mode, trace)`**: a read transaction at the state, by the caller's update (it reads
the current and compaction revisions under `s.revMu`, and its storage snapshot). The
transaction keeps the reader token until its `End`. -/
abbrev KV.Read.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (mode : w32) (trace : Loc) (Q : MvccState → IProp GF),
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗ mvccReaders γ 1 ∗ ⌜trace ≠ null⌝ ∗ traceOwn trace ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅ <{ mvccState γ σ, COMM Q σ }> }}
    (App (App (Val #(methods ty go!"Read" v)) (Val #mode)) (Val #trace))
  {{ (t : GoInterface), RET #t; traceOwn trace ∗ ∃ σ : MvccState, mvccTxn t γ trace (.read σ) ∗ Q σ }}

/-- **`Write(trace)`**: a write transaction begun at the state, by the caller's update (nothing
pending then); the storage's post-lock hook run under the batch lock, `Pre` to `Q`. The transaction
keeps the reader token until its `End`; the caller holds `Q` (the batch lock's invariant `Pk`
among it, which `End` takes back). -/
abbrev KV.Write.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (trace : Loc) (q : Qp) (B : MvccStorage) (Pk Pre Q : IProp GF) (f : GoFunc)
    (R : MvccState → IProp GF),
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗ mvccReaders γ 1 ∗ ⌜trace ≠ null⌝ ∗ traceOwn trace ∗
      mvccBackend γ q B Pk ∗ hookIs B f ∗ Pre ∗ hookRun Pk f Pre Q ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
        <{ ⌜σ.pending = []⌝ ∗ mvccState γ σ, COMM R σ }> }}
    (App (Val #(methods ty go!"Write" v)) (Val #trace))
  {{ (t : GoInterface), RET #t; traceOwn trace ∗ mvccBackend γ q B Pk ∗ Q ∗
      ∃ σ : MvccState, mvccTxn t γ trace (.write σ []) ∗ R σ }}

/-- **`Rev()`**: the current revision, by the caller's update. -/
abbrev KV.Rev.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (Q : MvccState → IProp GF),
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗ mvccReaders γ 1 ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅ <{ mvccState γ σ, COMM Q σ }> }}
    (App (Val #(methods ty go!"Rev" v)) (Val #()))
  {{ (r : w64), RET #r; mvccReaders γ 1 ∗ ∃ σ : MvccState, Q σ ∗ ⌜r = W64 σ.rev⌝ }}

/-- **`FirstRev()`**: the compaction revision (`-1` before any), by the caller's update. -/
abbrev KV.FirstRev.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (Q : MvccState → IProp GF),
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗ mvccReaders γ 1 ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅ <{ mvccState γ σ, COMM Q σ }> }}
    (App (Val #(methods ty go!"FirstRev" v)) (Val #()))
  {{ (r : w64), RET #r; mvccReaders γ 1 ∗ ∃ σ : MvccState, Q σ ∗ ⌜r = W64 σ.crev⌝ }}

/-- **`Range(ctx, key, end, ro)`** (a read transaction of one range): its outcome at the state, by
the caller's update (`rangeOut`: the revision checks, the result, or the context's error). -/
abbrev KV.Range.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (ctx : GoInterface) (key endk : GoSlice) (kk e : Bytes)
    (ro : go_etcd_io.etcd.server.v3.storage.mvcc.RangeOptions) (Q : MvccState → IProp GF),
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗ mvccReaders γ 1 ∗ Context.ctxOk ctx ∗
      key ↦*□ kk ∗ endk ↦*□ e ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅ <{ mvccState γ σ, COMM Q σ }> }}
    (App (App (App (App (Val #(methods ty go!"Range" v)) (Val #ctx)) (Val #key)) (Val #endk))
      (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err); mvccReaders γ 1 ∗
      ∃ (σ : MvccState) (out : RangeOut), Q σ ∗ ⌜rangeOut σ.kv σ.crev (mrange kk endk e) ro out⌝ ∗
        rangeResOwn ctx r err out }}

/-- **`Put(key, value, lease)`** (a write transaction of one put): the hook, then the commit's two
steps at the state the update gives; the lessor's item map that state's, then the new one's (the
lease live in the lessor, `Attach` panics otherwise). The key and value are kept (read-only). -/
abbrev KV.Put.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (γl : LessorName) (key value : GoSlice) (kk vv : Bytes) (lid : w64) (L : List Int)
    (I : Key → Int) (q : Qp) (B : MvccStorage) (Pk Pre Q' Post : IProp GF) (f : GoFunc)
    (Q : MvccState → IProp GF),
  let ev (σ : MvccState) := putEv σ [] kk vv (sint.Z lid)
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗ mvccLessorIs γ γl ∗ mvccReaders γ 1 ∗
      key ↦*□ kk ∗ value ↦*□ vv ∗
      leaseItems γl L I ∗ ⌜sint.Z lid = 0 ∨ sint.Z lid ∈ L⌝ ∗
      mvccBackend γ q B Pk ∗ hookIs B f ∗ Pre ∗ hookRun Pk f Pre Q' ∗ (Q' ={⊤}=∗ Pk ∗ Post) ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ ∗ ⌜storeItems σ.kv.store = I⌝ }> @ ⊤ \ ↑mvccN, ∅
        <{ ⌜σ.pending = []⌝ ∗ mvccState γ (σ.notify [ev σ]) ∗ ⧖ (evCount (σ.kv.commit [ev σ])), COMM
            AU <{ ∃∃ (σ' : MvccState), mvccState γ σ' }> @ ⊤ \ ↑mvccN, ∅
              <{ ⌜σ' = σ.notify [ev σ]⌝ ∗ mvccState γ σ'.commitPending, COMM Q σ }> }> }}
    (App (App (App (Val #(methods ty go!"Put" v)) (Val #key)) (Val #value)) (Val #lid))
  {{ (rev : w64), RET #rev; mvccReaders γ 1 ∗ mvccBackend γ q B Pk ∗ Post ∗
      ∃ σ : MvccState, Q σ ∗ leaseItems γl L (storeItems (txnStore σ [ev σ])) ∗
        ⌜rev = W64 (σ.rev + 1)⌝ }}

/-- **`DeleteRange(key, end)`** (a write transaction of one range delete), as `Put`: the range's
present keys deleted (`ds`, in key order; the commit of nothing when none), their number, the
revision written (the current one if nothing was deleted). -/
abbrev KV.DeleteRange.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (γl : LessorName) (key endk : GoSlice) (kk e : Bytes) (L : List Int)
    (I : Key → Int) (q : Qp) (B : MvccStorage) (Pk Pre Q' Post : IProp GF) (f : GoFunc)
    (Q : MvccState → List Key → IProp GF),
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗ mvccLessorIs γ γl ∗ mvccReaders γ 1 ∗
      key ↦*□ kk ∗ endk ↦*□ e ∗ leaseItems γl L I ∗
      mvccBackend γ q B Pk ∗ hookIs B f ∗ Pre ∗ hookRun Pk f Pre Q' ∗ (Q' ={⊤}=∗ Pk ∗ Post) ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ ∗ ⌜storeItems σ.kv.store = I⌝ }> @ ⊤ \ ↑mvccN, ∅
        <{ ∀∀ (ds : List Key), ⌜σ.pending = [] ∧ rangeKeys σ.kv.store (mrange kk endk e) ds⌝ ∗
            mvccState γ (σ.notify (ds.map .delete)) ∗
            ⧖ (evCount (σ.kv.commit (ds.map .delete))), COMM
            AU <{ ∃∃ (σ' : MvccState), mvccState γ σ' }> @ ⊤ \ ↑mvccN, ∅
              <{ ⌜σ' = σ.notify (ds.map .delete)⌝ ∗ mvccState γ σ'.commitPending,
                 COMM Q σ ds }> }> }}
    (App (App (Val #(methods ty go!"DeleteRange" v)) (Val #key)) (Val #endk))
  {{ (n rev : w64), RET (PairV #n #rev); mvccReaders γ 1 ∗ mvccBackend γ q B Pk ∗ Post ∗
      ∃ (σ : MvccState) (ds : List Key), Q σ ds ∗
        leaseItems γl L (storeItems (txnStore σ (ds.map .delete))) ∗
        ⌜n = W64 ds.length ∧ rev = W64 (if ds = [] then σ.rev else σ.rev + 1)⌝ }}

/-- **`Compact(trace, rev)`** (`rev ≥ 1`: a `Compact(0)` mid-job restores to compaction revision
`-1`, `issues/etcd-restore-scheduled-compact-zero.md`; the user, 2026-11-04), by the caller's
update at the state it compacts: above the compaction revision and at most the current one, the
compaction, the hook once under the batch lock (`Pre` to `Q'`, the lock's invariant back) and the
storage's commit (`X` to `Y`), and a channel closed once the job has run; at or below it,
`ErrCompacted` and a channel (closed after the jobs before it); past the current revision,
`ErrFutureRev` and no channel. -/
abbrev KV.Compact.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (trace : Loc) (rev : w64) (q : Qp) (B : MvccStorage) (Pk : IProp GF)
    (f : GoFunc) (Pre Q' Post X Y : IProp GF) (Q : MvccState → IProp GF),
  let ok (σ : MvccState) : Prop := σ.crev < sint.Z rev ∧ sint.Z rev ≤ (σ.rev : Int)
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗ mvccOpen γ ∗ ⌜trace ≠ null⌝ ∗ traceOwn trace ∗
      ⌜1 ≤ sint.Z rev⌝ ∗ mvccBackend γ q B Pk ∗ hookIs B f ∗ X ∗ storageReq B Pk X Y ∗
      Pre ∗ hookRun Pk f Pre Q' ∗ (Q' ={⊤}=∗ Pk ∗ Post) ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
        <{ mvccState γ (if ok σ then σ.compactTo (sint.Z rev).toNat else σ), COMM Q σ }> }}
    (App (App (Val #(methods ty go!"Compact" v)) (Val #trace)) (Val #rev))
  {{ (ch : GoChan) (err : GoInterface), RET (PairV #ch #err);
      mvccOpen γ ∗ traceOwn trace ∗ mvccBackend γ q B Pk ∗ ∃ σ : MvccState, Q σ ∗
      ((⌜err = GoInterface.nil ∧ ok σ⌝ ∗ Post ∗ Y ∗ compactChanOk ch) ∨
       (⌜sint.Z rev ≤ σ.crev⌝ ∗ globalAddr ErrCompacted ↦□ err ∗ Pre ∗ X ∗ compactChanOk ch) ∨
       (⌜(σ.rev : Int) < sint.Z rev ∧ ch = chan.nil⌝ ∗ globalAddr ErrFutureRev ↦□ err ∗ Pre ∗ X)) }}

/-- **`Commit()`**: the storage's forced commit (`X` to `Y`). -/
abbrev KV.Commit.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (q : Qp) (B : MvccStorage) (Pk X Y : IProp GF),
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗ mvccBackend γ q B Pk ∗ X ∗ storageReq B Pk X Y }}
    (App (Val #(methods ty go!"Commit" v)) (Val #()))
  {{ RET #(); mvccBackend γ q B Pk ∗ Y }}

/-- **`Restore(b')`** from the storage `B'` holding an image of the history `σ'.kv` (the user's
decision 3, 2026-11-03: at any share of the new storage's post-lock hook): by the caller's update,
at a state whose history `σ'`'s extends (its compaction revision not lowered), the state `σ'`
(its linearization point: `currentRev` set, under `s.revMu`). The store's storage is now `B'`; the
old one's rest back (`Restore` waits out every transaction, the scheduler and the loops). The
lessor's item map re-attached: the restored store's, but for keys whose lease the lessor does not
have (`Attach` fails; the error is logged). When the image records an unfinished compaction (`u`),
it is resumed: the new storage's hook once under its batch lock (`Pre` to `Q'`, `Pk'` back) and one
commit (`X` to `Y`); otherwise neither. The hook at a share given back: unset (`nil`, at any share:
etcd sets the new backend's hook after `Restore`, `server.go:1098`) or frozen. -/
abbrev KV.Restore.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (γl : LessorName) (B B' : MvccStorage) (Pk Pk' : IProp GF) (σ' : MvccState)
    (u : Bool) (L : List Int) (dq : DFrac) (f : GoFunc) (Pre Q' Post X Y : IProp GF)
    (Q : MvccState → IProp GF),
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗ mvccLessorIs γ γl ∗ mvccOpen γ ∗
      mvccBackend γ 1 B Pk ∗ mvccStorageFor B' Pk' σ'.kv u ∗
      ⌜MvccReachable σ' ∧ σ'.pending = []⌝ ∗
      storageHook B' dq f ∗ ⌜f = func.nil ∨ dq = DFrac.discard⌝ ∗
      Pre ∗ hookRun Pk' f Pre Q' ∗ (Q' ={⊤}=∗ Pk' ∗ Post) ∗ X ∗ storageReq B' Pk' X Y ∗
      leaseItems γl L (fun _ => 0) ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ ∗
              ⌜σ.kv.revs <+: σ'.kv.revs ∧ σ.kv.compacted ≤ σ'.kv.compacted⌝ }> @ ⊤ \ ↑mvccN, ∅
        <{ mvccState γ σ' ∗ ⧖ (evCount σ'.kv), COMM Q σ }> }}
    (App (Val #(methods ty go!"Restore" v)) (Val #(GoInterface.ok (storageVal B'))))
  {{ RET #(GoInterface.nil); mvccOpen γ ∗ mvccBackend γ 1 B' Pk' ∗ storageRest B ∗
      storageHook B' dq f ∗ (if u then iprop(Post ∗ Y) else iprop(Pre ∗ X)) ∗
      leaseItems γl L (itemsIn L σ'.kv.store) ∗ ∃ σ : MvccState, Q σ }}

/-- **`HashStorage()`**: the store's hash storage. -/
abbrev KV.HashStorage.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName),
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ }}
    (App (Val #(methods ty go!"HashStorage" v)) (Val #()))
  {{ (h : GoInterface), RET #h; isHashStorage h γ }}

/-- **`Close()`** (the whole open token): the store closed (its goroutines stopped, its job
scheduler's pending jobs run). `store.Close` takes no lock, so a read may still be in flight: no
part of the storage comes back here; the client gets it with every reader token
(`mvccClosed_rest`). A read concurrent with or after `Close` is no bug (it touches no closed
resource); closing the storage under one is etcd's shutdown crash
(`issues/etcd-read-after-backend-close-panic.md`), which the reader tokens rule out. -/
abbrev KV.Close.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName),
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗ mvccOpen γ }}
    (App (Val #(methods ty go!"Close" v)) (Val #()))
  {{ RET #(GoInterface.nil); mvccClosed γ }}

/-! ### `TxnRead`, `TxnWrite` -/

/-- `Rev()`: the revision the transaction began at. -/
abbrev Txn.Rev.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (trace : Loc) (k : MTxn),
  {{ pkgInit ∗ mvccTxn (interface.mkOk ty v) γ trace k }}
    (App (Val #(methods ty go!"Rev" v)) (Val #()))
  {{ RET #(W64 k.state.rev : w64); mvccTxn (interface.mkOk ty v) γ trace k }}

/-- `FirstRev()`: a read transaction's compaction revision; a write transaction's `0`
(`store.Write` sets none). -/
abbrev Txn.FirstRev.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (trace : Loc) (k : MTxn),
  {{ pkgInit ∗ mvccTxn (interface.mkOk ty v) γ trace k }}
    (App (Val #(methods ty go!"FirstRev" v)) (Val #()))
  {{ RET #(match k with
      | .read σ => (W64 σ.crev : w64)
      | .write _ _ => (W64 0 : w64)); mvccTxn (interface.mkOk ty v) γ trace k }}

/-- `Range(ctx, key, end, ro)`: its outcome over the history the transaction reads
(`MTxn.readHist`: a write transaction's events included). -/
abbrev Txn.Range.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (trace : Loc) (k : MTxn) (ctx : GoInterface) (key endk : GoSlice) (kk e : Bytes)
    (ro : go_etcd_io.etcd.server.v3.storage.mvcc.RangeOptions),
  {{ pkgInit ∗ mvccTxn (interface.mkOk ty v) γ trace k ∗ traceOwn trace ∗ Context.ctxOk ctx ∗
      key ↦*□ kk ∗ endk ↦*□ e }}
    (App (App (App (App (Val #(methods ty go!"Range" v)) (Val #ctx)) (Val #key)) (Val #endk))
      (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      mvccTxn (interface.mkOk ty v) γ trace k ∗ traceOwn trace ∗
      ∃ out : RangeOut, ⌜rangeOut k.readHist k.state.crev (mrange kk endk e) ro out⌝ ∗
        rangeResOwn ctx r err out }}

/-- `Put(key, value, lease)` of a write transaction: the put's event appended; the lessor's item
map moved with it (the lease live in the lessor). Returns the revision it writes. -/
abbrev Txn.Put.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (γl : LessorName) (trace : Loc) (σ : MvccState) (pend : List Event)
    (key value : GoSlice) (kk vv : Bytes) (lid : w64) (L : List Int),
  let ev := putEv σ pend kk vv (sint.Z lid)
  {{ pkgInit ∗ mvccTxn (interface.mkOk ty v) γ trace (.write σ pend) ∗ mvccLessorIs γ γl ∗
      traceOwn trace ∗ key ↦*□ kk ∗ value ↦*□ vv ∗
      leaseItems γl L (storeItems (txnStore σ pend)) ∗ ⌜sint.Z lid = 0 ∨ sint.Z lid ∈ L⌝ }}
    (App (App (App (Val #(methods ty go!"Put" v)) (Val #key)) (Val #value)) (Val #lid))
  {{ RET #(W64 (σ.rev + 1) : w64);
      mvccTxn (interface.mkOk ty v) γ trace (.write σ (pend ++ [ev])) ∗ traceOwn trace ∗
      leaseItems γl L (storeItems (txnStore σ (pend ++ [ev]))) }}

/-- `DeleteRange(key, end)` of a write transaction: the deletes of the range's present keys (in
the store the transaction sees) appended; their number; the revision written (`beginRev + 1` once
the transaction has a change). -/
abbrev Txn.DeleteRange.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (γl : LessorName) (trace : Loc) (σ : MvccState) (pend : List Event)
    (key endk : GoSlice) (kk e : Bytes) (L : List Int),
  {{ pkgInit ∗ mvccTxn (interface.mkOk ty v) γ trace (.write σ pend) ∗ mvccLessorIs γ γl ∗
      key ↦*□ kk ∗ endk ↦*□ e ∗ leaseItems γl L (storeItems (txnStore σ pend)) }}
    (App (App (Val #(methods ty go!"DeleteRange" v)) (Val #key)) (Val #endk))
  {{ (n rev : w64), RET (PairV #n #rev); ∃ ds : List Key,
      ⌜rangeKeys (txnStore σ pend) (mrange kk endk e) ds⌝ ∗
      mvccTxn (interface.mkOk ty v) γ trace (.write σ (pend ++ ds.map .delete)) ∗
      leaseItems γl L (storeItems (txnStore σ (pend ++ ds.map .delete))) ∗
      ⌜n = W64 ds.length ∧ rev = W64 (if pend ++ ds.map .delete = [] then σ.rev else σ.rev + 1)⌝ }}

/-- `Changes()`: as many as the transaction's events (a read transaction's none). -/
abbrev Txn.Changes.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (trace : Loc) (k : MTxn),
  {{ pkgInit ∗ mvccTxn (interface.mkOk ty v) γ trace k }}
    (App (Val #(methods ty go!"Changes" v)) (Val #()))
  {{ (chs : GoSlice), RET #chs; mvccTxn (interface.mkOk ty v) γ trace k ∗
      ⌜uint.nat chs.len = k.pend.length ∧ 0 ≤ sint.Z chs.len⌝ }}

/-- `End()`: a read transaction gives the reader token back; a write transaction too, committing
in two steps of the caller's updates at the state it began at (`σ₀`): notify (the history it makes
receipted), then the bump; the batch lock's invariant `Pk` back to the lock. -/
abbrev Txn.End.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (trace : Loc) (k : MTxn) (q : Qp) (B : MvccStorage) (Pk Q : IProp GF),
  {{ pkgInit ∗ mvccTxn (interface.mkOk ty v) γ trace k ∗
      match k with
      | .read _ => iprop(True)
      | .write σ₀ pend => iprop(mvccBackend γ q B Pk ∗ Pk ∗
          AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
            <{ ⌜σ = σ₀⌝ ∗ mvccState γ (σ.notify pend) ∗ ⧖ (evCount (σ.kv.commit pend)), COMM
                AU <{ ∃∃ (σ' : MvccState), mvccState γ σ' }> @ ⊤ \ ↑mvccN, ∅
                  <{ ⌜σ' = σ₀.notify pend⌝ ∗ mvccState γ σ'.commitPending, COMM Q }> }>) }}
    (App (Val #(methods ty go!"End" v)) (Val #()))
  {{ RET #(); mvccReaders γ 1 ∗
      match k with
      | .read _ => iprop(True)
      | .write _ _ => iprop(mvccBackend γ q B Pk ∗ Q) }}

/-! ### `HashStorage` (trusted: the hashing is translated names-only) -/

/-- `HashByRev(rev)`: any hash, current revision and error (the corruption checker and the
maintenance server compare hashes across members; no safety proof reads them). A reader. -/
abbrev HashStorage.HashByRev.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (rev : w64),
  {{ pkgInit ∗ isHashStorage (interface.mkOk ty v) γ ∗ mvccReaders γ 1 }}
    (App (Val #(methods ty go!"HashByRev" v)) (Val #rev))
  {{ (kh : KeyValueHash) (cur : w64) (err : GoInterface), RET (PairV (PairV #kh #cur) #err);
      mvccReaders γ 1 }}

/-- `Hash()`: any hash, revision and error (a forced commit asking nothing, then the storage's
hash: a reader). -/
abbrev HashStorage.Hash.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName),
  {{ pkgInit ∗ isHashStorage (interface.mkOk ty v) γ ∗ mvccReaders γ 1 }}
    (App (Val #(methods ty go!"Hash" v)) (Val #()))
  {{ (h : w32) (rev : w64) (err : GoInterface), RET (PairV (PairV #h #rev) #err); mvccReaders γ 1 }}

/-- `Store(kh)`: no panic. -/
abbrev HashStorage.Store.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (kh : KeyValueHash),
  {{ pkgInit ∗ isHashStorage (interface.mkOk ty v) γ }}
    (App (Val #(methods ty go!"Store" v)) (Val #kh))
  {{ RET #(); True }}

/-- `Hashes()`: a fresh slice of the stored hashes (the caller's). -/
abbrev HashStorage.Hashes.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName),
  {{ pkgInit ∗ isHashStorage (interface.mkOk ty v) γ }}
    (App (Val #(methods ty go!"Hashes" v)) (Val #()))
  {{ (sl : GoSlice), RET #sl; ∃ hs : List KeyValueHash, sl ↦* hs }}

/-! ### The bundles (an interface value's methods meet the contracts; cf. `sync.isLocker`) -/

abbrev isKV (ty : go.GoType) (v : val) : Prop :=
  KV.Read.contract (GF := GF) ty v ∧ KV.Write.contract (GF := GF) ty v ∧
  KV.Rev.contract (GF := GF) ty v ∧ KV.FirstRev.contract (GF := GF) ty v ∧
  KV.Range.contract (GF := GF) ty v ∧ KV.Put.contract (GF := GF) ty v ∧
  KV.DeleteRange.contract (GF := GF) ty v ∧ KV.Compact.contract (GF := GF) ty v ∧
  KV.Commit.contract (GF := GF) ty v ∧ KV.Restore.contract (GF := GF) ty v ∧
  KV.HashStorage.contract (GF := GF) ty v ∧ KV.Close.contract (GF := GF) ty v

abbrev isTxn (ty : go.GoType) (v : val) : Prop :=
  Txn.Rev.contract (GF := GF) ty v ∧ Txn.FirstRev.contract (GF := GF) ty v ∧
  Txn.Range.contract (GF := GF) ty v ∧ Txn.Put.contract (GF := GF) ty v ∧
  Txn.DeleteRange.contract (GF := GF) ty v ∧ Txn.Changes.contract (GF := GF) ty v ∧
  Txn.End.contract (GF := GF) ty v

abbrev isHashStorageV (ty : go.GoType) (v : val) : Prop :=
  HashStorage.HashByRev.contract (GF := GF) ty v ∧ HashStorage.Hash.contract (GF := GF) ty v ∧
  HashStorage.Store.contract (GF := GF) ty v ∧ HashStorage.Hashes.contract (GF := GF) ty v

end contracts

/-! ## The laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

def persistent.spec : Prop :=
  (∀ kv γ, Persistent (isMvcc (GF := GF) kv γ)) ∧ (∀ γ γl, Persistent (mvccLessorIs (GF := GF) γ γl)) ∧
  (∀ h γ, Persistent (isHashStorage (GF := GF) h γ)) ∧
  (∀ γ σ, Timeless (mvccState (GF := GF) γ σ)) ∧ (∀ γ n, Timeless (mvccReaders (GF := GF) γ n)) ∧
  (∀ γ B (Pk : IProp GF), Fractional (fun q => mvccBackend γ q B Pk))

def excl.spec : Prop :=
  (∀ γ σ σ', mvccState (GF := GF) γ σ ∗ mvccState γ σ' ⊢ iprop(False)) ∧
  (∀ γ, mvccOpen (GF := GF) γ ∗ mvccOpen γ ⊢ iprop(False)) ∧
  (∀ γ, mvccOpen (GF := GF) γ ∗ mvccClosed γ ⊢ iprop(False))

/-- **The package's error variables** (`ErrCompacted`, `ErrFutureRev`): `errors.New` values with
their messages, read-only, distinct (so a client's `err == mvcc.ErrCompacted`, Go's interface `==`,
needs no internals; the tester's migration's G2). -/
def init.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ⊢
    ∃ (x1 x2 : Loc),
      globalAddr ErrCompacted ↦□
        (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x1 : GoInterface) ∗
      x1.[errors.errorString, go!"s"] ↦□ go!"mvcc: required revision has been compacted" ∗
      globalAddr ErrFutureRev ↦□
        (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x2 : GoInterface) ∗
      x2.[errors.errorString, go!"s"] ↦□ go!"mvcc: required revision is a future revision" ∗
      ⌜x1 ≠ x2⌝

/-- **The reader tokens split and join.** -/
def mvccReaders_split.spec : Prop :=
  ∀ γ n m, mvccReaders (GF := GF) γ (n + m) ⊣⊢ mvccReaders γ n ∗ mvccReaders γ m

/-- **Shutdown: the storage's rest back** (the user's decision, 2026-11-06, `notes/decisions.md`,
"mvcc's API: the store's readers as client-held tokens"): the closed store, every reader token (no
read in flight) and a share of the store's backend. -/
def mvccClosed_rest.spec : Prop :=
  ∀ γ (q : Qp) B (Pk : IProp GF),
    mvccClosed (GF := GF) γ ∗ mvccReaders γ mvccTokN ∗ mvccBackend γ q B Pk ={⊤}=∗
      storageRest B ∗ mvccBackend γ q B Pk

/-- **A storage ready for a store that no store took: its rest back** (the server's `NewServer`,
whose error path closes the backend before `mvcc.New`). -/
def mvccStorageFor_rest.spec : Prop :=
  ∀ B (Pk : IProp GF) h u, mvccStorageFor (GF := GF) B Pk h u ={⊤}=∗ storageRest B

def mvccBackend_agree.spec : Prop :=
  ∀ γ q q' B B' (Pk Pk' : IProp GF), mvccBackend (GF := GF) γ q B Pk ∗ mvccBackend γ q' B' Pk' ⊢
    ⌜B = B' ∧ Pk = Pk'⌝

def mvccLessorIs_agree.spec : Prop :=
  ∀ γ γl γl', mvccLessorIs (GF := GF) γ γl ∗ mvccLessorIs γ γl' ⊢ ⌜γl = γl'⌝

/-- **A store's state is reachable** (from its start or the restored state), its revision an
`int64` with one to spare. -/
def mvccState_reachable.spec : Prop :=
  ∀ kv γ σ, isMvcc (GF := GF) kv γ ∗ mvccState γ σ ⊢ ⌜MvccReachable σ ∧ σ.rev + 1 < 2 ^ 63⌝

/-- **A transaction's state** is reachable, its revision an `int64` with one to spare, and a write
transaction's events well formed (each put's record over the key's, each delete of a key present):
what a client relating the transaction's results to its own model needs. -/
def mvccTxn_state.spec : Prop :=
  ∀ t γ trace k, mvccTxn (GF := GF) t γ trace k ⊢
    ⌜MvccReachable k.state ∧ k.state.rev + 1 < 2 ^ 63 ∧ k.state.pending = [] ∧
      EvsWf (k.state.kv.rev + 1) k.state.kv.store k.pend⌝

/-- **The names are inhabited** (a client builds a stand-in before the store exists). -/
def names_nonempty.spec : Prop := Nonempty MvccName ∧ Nonempty LessorName

/-- **The shapes and the bundles** (proved from the concrete specs, as `sync`'s
`Mutex_is_Locker`): a store's handle, a transaction, a hash storage are an `interface.mkOk ty v`
whose type meets its interface's contracts. -/
def shapes.spec : Prop :=
  (∀ kv γ, isMvcc (GF := GF) kv γ ⊢ ⌜∃ ty v, kv = interface.mkOk ty v ∧ isKV (GF := GF) ty v⌝) ∧
  (∀ t γ trace k, mvccTxn (GF := GF) t γ trace k ⊢
    ⌜∃ ty v, t = interface.mkOk ty v ∧ isTxn (GF := GF) ty v⌝) ∧
  (∀ h γ, isHashStorage (GF := GF) h γ ⊢
    ⌜∃ ty v, h = interface.mkOk ty v ∧ isHashStorageV (GF := GF) ty v⌝)

/-- **What the store's storage holds at its state** (the snapshot path: 2d's merged snapshot reads
the storage after `KV().Commit()`, through 4a's `Snapshot`): with the whole share of the store's
storage (no write, compaction or restore in flight can start: each takes a share) and the state
(nothing pending), an atomic read of the storage's visible data, at any time, finds an image of the
state's history (its compaction's job possibly unfinished: `u`) and the history's receipt. -/
def mvccImage_obs.spec : Prop :=
  ∀ kv γ B (Pk : IProp GF) σ, isMvcc (GF := GF) kv γ ∗ mvccBackend γ 1 B Pk ∗ mvccState γ σ ∗
    ⌜σ.pending = []⌝ ⊢
    kbObs B (fun D => iprop(∃ u : Bool, ⌜mvccImage D σ.kv u⌝ ∗ ⧖ (evCount σ.kv) ∗
      mvccBackend γ 1 B Pk ∗ mvccState γ σ))

end laws

end Mvcc
end EtcdGrove
end Perennial
