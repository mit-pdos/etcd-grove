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

Opaque Iris predicates (10): `mvccState`, `isMvcc`, `mvccOpen`, `mvccBackend`, `mvccTxn`,
`isMvccWatchStream`, `wsState`, `wsRecv`, and (the reader tokens, 2026-11-06) `mvccReaders`,
`mvccClosed`; and at the storage boundary (the design "mvcc's API over
its storage abstraction", approved by the user, 2026-11-06: no name of etcd's backend here; etcd's
backend is one storage, `mvcc/EtcdBackend.lean`): `MvccStorage`, `storageVal`, `storageHook`,
`storageReq`, `storageRest`, `mvccReaderN`, `mvccStorageFor`. Opaque pure names: the types `MvccName`, `WsName`;
`mvccLeases`, `wsChanOf`, `wsChanNames`. Definitions: `hookRun`, `mvccDeleter`, `compactChanOk`, `hashStoreOk`,
`wrespIs`, the contracts and bundles, the pure state and `wsRecvOk`.
-/
module

public import Spec.go_uber_org.zap.Defs
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiState
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore
public import Perennial.Proof.sync
public import Perennial.Ghost.Token
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStream
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.RdPool
public import Proof.go_opentelemetry_io.otel.trace.Defs
import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.StreamGhost
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.DelKeys
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBuffer
public import Perennial.Std.ListBasics
public import Perennial.Golang.Theory.Map
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.GhostMap
public import Perennial.IrisLib.BI
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Model2
public import Spec.go_uber_org.zap.Defs
public import Perennial.Ghost.SavedProp
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base
public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.bytes
public import Perennial.GeneratedProof.encoding.binary
public import Perennial.Golang.Theory
public import Code.google_golang_org.protobuf.reflect.protoreflect
public import GeneratedProof.google_golang_org.protobuf.internal.impl
public import Code.google_golang_org.protobuf.runtime.protoimpl
public import Code.go_etcd_io.etcd.api.v3.authpb
public import Perennial.GeneratedProof.context
public import Code.go_etcd_io.etcd.api.v3.membershippb
public import GeneratedProof.go_etcd_io.etcd.api.v3.mvccpb
public import Code.google_golang_org.grpc.metadata
public import Code.google_golang_org.grpc
public import GeneratedProof.google_golang_org.grpc.chunk1
public import GeneratedProof.google_golang_org.grpc.chunk3
public import Code.go_etcd_io.etcd.api.v3.etcdserverpb
public import Perennial.GeneratedProof.fmt
public import Code.go_etcd_io.etcd.client.pkg.v3.verify
public import Perennial.GeneratedProof.errors
public import Code.google_golang_org.grpc.codes
public import Code.google_golang_org.grpc.internal.status
public import Code.google_golang_org.grpc.status
public import Code.go_etcd_io.etcd.api.v3.v3rpc.rpctypes
public import GeneratedProof.go_etcd_io.etcd.pkg.v3.adt
public import GeneratedProof.go_uber_org.zap
public import Code.golang_org.x.crypto.bcrypt
public import Perennial.GeneratedProof.sort
public import Perennial.GeneratedProof.strconv
public import Perennial.GeneratedProof.strings
public import Perennial.GeneratedProof.sync
public import Perennial.GeneratedProof.sync.atomic
public import Perennial.GeneratedProof.time
public import Code.go_etcd_io.etcd.server.v3.auth
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.backend
public import GeneratedProof.google_golang_org.protobuf.internal.pragma
public import Code.google_golang_org.protobuf.proto
public import Code.go_etcd_io.etcd.server.v3.storage.schema
public import Perennial.Golang.Theory.Chan.Idioms.Spsc
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndex
public import Perennial.Spec.sync.atomic.Int32__Add
public import Perennial.Proof.sync.Base
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketRange
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCindex
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Compact
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndexCut
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Hist
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiState
import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.TxnHandle
import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.RdSupply
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
@[no_expose] def MvccName : Type := StoreNames
/-- **The store's lessor's ghost name** (its `lease.leaseOwn`; M3, 2026-11-06: defined, the store's
names' `leases`). -/
@[no_expose] def mvccLeases (γ : MvccName) : GName := (γ : StoreNames).leases

/-! ## The vocabulary -/

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The store's state is `σ`** (exclusive, timeless; the client's). -/
@[no_expose] def mvccState (γ : MvccName) (σ : MvccState) : IProp GF :=
  api.mvccStateI (γ : StoreNames).api σ

/-- A plain store's handle (stage 2, 2026-11-05; partial: `notes/mvcc-api-invariants.md` §2 adds
its readers' pool and the write-back supply). (`KV.Compact.contract`, 2026-11-06) The store's
location recorded (`locIs`, which the open token's agrees with) and its compaction permit `True`
(the API's compactions are permitted at any revision). (Track A, request 3, 2026-11-06) The
readers' supply (`rdSupply`) and the certificate map's free entry (`certFree`); that the store has
no watchers is `isMvcc`'s. (2026-11-06) The store's read and write views (`KV.Rev`, `FirstRev`,
`Range`, `Put`, `DeleteRange` are theirs, promoted): `NewStore`'s, whose `kv` is the store itself.
(The watchable store's `Compact` no longer builds this handle of its inner store, whose views are
the watchable store's: it calls the plain `Compact`'s body over the store, location and permit.) -/
private def isMvccPlain (kv : GoInterface) (γ : MvccName) : IProp GF :=
  iprop(∃ s : Loc, ⌜kv = interface.mkOk (go.GoType.PointerType store.ty) #s⌝ ∗
    isStore s (γ : StoreNames) ∗ api.locIs (γ : StoreNames).api s ∗
    crevPermIs (γ : StoreNames) (fun _ => iprop(True)) ∗
    rdSupply s (γ : StoreNames) ∗ certFree (γ : StoreNames) ∗ idxCert (γ : StoreNames).idx [[], []] ∗
    (∃ rv wv : Loc,
      s.[store, go!"ReadView"] ↦□ (interface.mkOk (go.GoType.PointerType readView.ty) #rv : GoInterface) ∗
      isReadView rv s (γ : StoreNames) ∗
      s.[store, go!"WriteView"] ↦□ (interface.mkOk (go.GoType.PointerType writeView.ty) #wv : GoInterface) ∗
      isWriteView wv s (γ : StoreNames)))

/-- A watchable store's handle (stage 2, 2026-11-05: what `NewWatchStream` needs, §2): the
watchable store `s` over its inner store `st`, at names `γw` whose store is `γ`, the watch tokens'
pool (a registration's cost) and the pool of the client's reader tokens (`rdkPool`, of
`watchSlots`: a `watchReader` but its ticket; 2026-11-06; 2026-11-07, keyed by the reader tokens,
`mvccReaders`, in place of thread tokens), which every stream of it draws on. Still to add (§2): the write-back supply, the store's own goroutines'
readers from the same pool. (`KV.Compact.contract`, 2026-11-06) The inner store's location and its
compaction permit `True`, as a plain store's. (Track A, request 3, 2026-11-06) The certificate
map's free entry (`certFree`). -/
private def isMvccWatchable (kv : GoInterface) (γ : MvccName) : IProp GF :=
  iprop(∃ (s st : Loc) (γw : WsNames),
    ⌜kv = interface.mkOk (go.GoType.PointerType watchableStore.ty) #s ∧ γw.st = (γ : StoreNames)⌝ ∗
    isWatchableStore s st γw ∗ watchTokPool γw ∗
    rdkPool γw.st (watchSlots s st γw) ∗
    api.locIs (γ : StoreNames).api st ∗ crevPermIs (γ : StoreNames) (fun _ => iprop(True)) ∗
    certFree (γ : StoreNames))

/-- **`kv` (the `KV` `New` or `NewStore` returned) serves the store `γ`** (persistent). -/
@[no_expose] def isMvcc (kv : GoInterface) (γ : MvccName) : IProp GF :=
  iprop(□ ((isMvccPlain kv γ ∗ ⌜(γ : StoreNames).watchQ = false⌝) ∨ isMvccWatchable kv γ))

/-- **`t` is a transaction of `γ`, begun with `trace`, at `k`** (exclusive; it holds the caller's
reader token until its `End`, not the trace). Defined (M4, track B, 2026-11-06; `Api/TxnHandle.lean`): the
internal transaction without its trace, at the state it began at, with the reader token's way back. -/
@[no_expose] def mvccTxn (t : GoInterface) (γ : MvccName) (trace : Loc) (k : MTxn) : IProp GF :=
  api.mvccTxnI t (γ : StoreNames) trace k

/-- **A storage implementation** (opaque; the design "mvcc's API over its storage abstraction",
approved by the user, 2026-11-06): what the store keeps its history in, as mvcc's storage contract
sees it. Phase A: sealed over the real backend's instance (`KBReal`); the bridge module
(`mvcc/EtcdBackend.lean`) names etcd's backend as one (`etcdStorage`). -/
@[no_expose] def MvccStorage : Type := KBReal

/-- **A share `dq` of the storage's post-lock hook, at `f`** (fractional; sealed): the hook the
storage's batch lock runs (`hookRun`), `nil` for none. -/
@[no_expose] def storageHook (B : MvccStorage) (dq : DFrac) (f : GoFunc) : IProp GF :=
  backend.plHookAt (B : KBReal).γB dq f

/-- **`n` of the store's reader tokens** (exclusive, counted, timeless; sealed; the user's decision,
2026-11-06, `notes/decisions.md`, "mvcc's API: the store's readers as client-held tokens"): each is
the right to one reader of the store: a reader slot of each of the store's locks it takes (`s.mu`,
`s.revMu`, and a watchable store's `s.mu`; 2026-11-07, `notes/decisions.md`, "mvcc's reader token
carries the store's lock slots": no thread token) and one of the storage's reader slots, which the
store keeps (with their shares of the storage's open token) at its current storage, so `Restore`
leaves the tokens alone. `New` and
`NewStore` give `mvccReaderN` of them; a contract whose call reads the storage takes one and gives
it back (`KV.Read`'s and `KV.Write`'s transaction keeps it until its `End`). A client holding all
of them, with `Close`'s post (`mvccClosed`), gets the storage's rest back (`mvccClosed_rest.law`):
no read of the store is then in flight. They split and join (`mvccReaders_split.law`). Defined:
the tokens of the handle's readers' pool (`ownToks γ.api.rdk n`; the pool, `rdkPool`, holds a
reader's lock slots and ticket of the store's readers' pool for each). -/
@[no_expose] def mvccReaders (γ : MvccName) (n : Nat) : IProp GF :=
  ownToks (γ : StoreNames).api.rdk n

/-- **A share `q` of the store's backend: it is `B`, its batch lock's invariant `Pk`**
(fractional; `New`'s or `NewStore`'s, then `Restore`'s). Defined at stage 2 (M2, 2026-11-05;
`notes/mvcc-api-invariants.md` §2): `q` of the backend share token (of total 1: the whole share
excludes every step that changes the history) and `q` of the writer's fragment of the store's
current objects and physical names (`curAt`, an eighth at `q = 1`), whose backend is the real one
`B`, compacting (the API has no compaction mode), opened at the store's write invariant
(`isBackend` at `lateW`, the bridge's `mvccW`) with the batch lock's invariant `Pk`, and (the snapshot image's (d),
2026-11-05) the store's registration's invariant in it at the current names (`writerReg`: a
snapshot's freezer lends a pending registration through it); (`KV.Compact.contract`, 2026-11-06)
the store's name of its batch lock's invariant at `Pk` (`hookP`: a compactor's hook contract over
`Pk` is the store's); (track A, request 3, 2026-11-06) the write-back supply of the current backend
(`storeWT` at the share's names: a `Restore` gives the new backend's). -/
@[no_expose] def mvccBackend (γ : MvccName) (q : Qp) (B : MvccStorage) (Pk : IProp GF) : IProp GF :=
  iprop(api.shareTok (γ : StoreNames).api q ∗
    ∃ (p : PhysNames) (o : StoreObjs) (d : KBReal),
      curAt ((γ : StoreNames).withPhys p) (DFrac.own q.half.half.half) o ∗
      ⌜p.kb = some d ∧ d.cm = true ∧ (d : MvccStorage) = B⌝ ∗
      □ backend.isBackend d.γB d.P (lateW d.gx) Pk d.be ∗
      □ (∃ s : Loc, writerReg s ((γ : StoreNames).withPhys p)) ∗
      □ hookP ((γ : StoreNames).withPhys p) Pk ∗
      □ (⧗ 1 ={⊤}=∗ storeWT ((γ : StoreNames).withPhys p)) ∗ ⌜leaseParams d.P⌝)

/-- **What the post-lock hook `f` does** under the batch lock of invariant `P`, from the caller's
`Pre`: `f`'s triple to `Q`, or with no hook (`nil`), the caller's view shift. -/
def hookRun (P : IProp GF) (f : GoFunc) (Pre Q : IProp GF) : IProp GF :=
  if f = func.nil then iprop(P ∗ Pre ={⊤}=∗ Q)
  else iprop(□ {{ P ∗ Pre }} (App (Val #f) (Val #())) {{ RET #(); Q }})

/-- **The storage's hook is `f`, for good** (frozen: the discarded share of `storageHook`). -/
abbrev hookIs (B : MvccStorage) (f : GoFunc) : IProp GF := storageHook B DFrac.discard f

/-- The lessor's range deleter `rd` is the store's `Write(traceutil.TODO())`, not `nil` (the
server draft's S2: `lessor.Revoke` checks it). -/
def mvccDeleter (rd : GoFunc) (γ : MvccName) : IProp GF :=
  iprop(⌜rd ≠ func.nil⌝ ∗ □ ∀ (q : Qp) (B : MvccStorage) (P Pre Q : IProp GF) (f : GoFunc) (R : MvccState → IProp GF),
    {{ mvccReaders γ 1 ∗ mvccBackend γ q B P ∗ hookIs B f ∗ Pre ∗ hookRun P f Pre Q ∗
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

/-! ### `TxnRead`, `TxnWrite` -/

/-! ### `WatchStream` -/

/-! ### The bundles (an interface value's methods meet the contracts; cf. `sync.isLocker`) -/

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

-- (and likewise `Rev`, `FirstRev`, `Range`, `DeleteRange`, `Changes` of each of the three)

-- (and likewise `Chan`, `RequestProgress`, `RequestProgressAll`, `Cancel`, `Close`, `Rev`)

end specs

/-! ## The laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

end laws

end api
end mvcc
end EtcdGrove
end Perennial
