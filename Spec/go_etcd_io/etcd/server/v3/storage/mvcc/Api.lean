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
`isMvccWatchStream`, `wsState`, `wsRecv`; and at the storage boundary (the design "mvcc's API over
its storage abstraction", approved by the user, 2026-11-06: no name of etcd's backend here; etcd's
backend is one storage, `mvcc/EtcdBackend.lean`): `MvccStorage`, `storageVal`, `storageHook`,
`storageReq`, `storageRest`, `mvccReaderN`, `mvccStorageFor`. Opaque pure names: the types `MvccName`, `WsName`;
`mvccLeases`, `wsChanOf`, `wsChanNames`. Definitions: `hookRun`, `mvccDeleter`, `compactChanOk`, `hashStoreOk`,
`wrespIs`, the contracts and bundles, the pure state and `wsRecvOk`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiState
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStream
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.RdPool
public import Proof.go_opentelemetry_io.otel.trace.Defs
import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.StreamGhost
import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.SnapImage
import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.TxnHandle
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
/-- **A watch stream's name** (pure, opaque). -/
@[no_expose] def WsName : Type := api.WsAbs
/-- **The store's lessor's ghost name** (its `lease.leaseOwn`; M3, 2026-11-06: defined, the store's
names' `leases`). -/
@[no_expose] def mvccLeases (γ : MvccName) : GName := (γ : StoreNames).leases
/-- **The stream's channel** (fixed at its creation). -/
@[no_expose] def wsChanOf (ι : WsName) : GoChan := (ι : api.WsAbs).ch
/-- **The stream's channel's ghost names** (fixed at its creation; the probe of v3rpc's watch,
2026-11-04: named, so that a client's definitions can mention them, in place of an existential in
`wsChan_recv.law`). -/
@[no_expose] def wsChanNames (ι : WsName) : ChanNames := (ι : api.WsAbs).chn

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
(the API's compactions are permitted at any revision). -/
private def isMvccPlain (kv : GoInterface) (γ : MvccName) : IProp GF :=
  iprop(∃ s : Loc, ⌜kv = interface.mkOk (go.GoType.PointerType store.ty) #s⌝ ∗
    isStore s (γ : StoreNames) ∗ api.locIs (γ : StoreNames).api s ∗
    crevPermIs (γ : StoreNames) (fun _ => iprop(True)))

/-- A watchable store's handle (stage 2, 2026-11-05: what `NewWatchStream` needs, §2): the
watchable store `s` over its inner store `st`, at names `γw` whose store is `γ`, the watch tokens'
pool (a registration's cost) and a thread pool of its readers' slots (`watchReader`), which every
stream of it draws on. Still to add (§2): the write-back supply, the store's own goroutines'
readers from the same pool. (`KV.Compact.contract`, 2026-11-06) The inner store's location and its
compaction permit `True`, as a plain store's. -/
private def isMvccWatchable (kv : GoInterface) (γ : MvccName) : IProp GF :=
  iprop(∃ (s st : Loc) (γw : WsNames) (γp : GName),
    ⌜kv = interface.mkOk (go.GoType.PointerType watchableStore.ty) #s ∧ γw.st = (γ : StoreNames)⌝ ∗
    isWatchableStore s st γw ∗ watchTokPool γw ∗
    threadPool.isThreadPool watchRdPoolN γp (watchReader s st γw) ∗
    api.locIs (γ : StoreNames).api st ∗ crevPermIs (γ : StoreNames) (fun _ => iprop(True)))

/-- **`kv` (the `KV` `New` or `NewStore` returned) serves the store `γ`** (persistent). -/
@[no_expose] def isMvcc (kv : GoInterface) (γ : MvccName) : IProp GF :=
  iprop(□ (isMvccPlain kv γ ∨ isMvccWatchable kv γ))

/-- The open token's closer pieces (track A, `New.spec`, 2026-11-06): the store's current backend
(at physical names `p`) compacting, and, of a watchable store, its own closer: the watchable store
`w` the inner store `s`'s read view points at, its stop channel's close and the loops' waiter
(`watchableStore.Close`'s, beside the inner store's right). -/
private def openRest (γ : MvccName) (p : PhysNames) (s : Loc) : IProp GF :=
  iprop(⌜kbCmpM p.kb⌝ ∗ if (γ : StoreNames).watchQ then iprop(∃ (w rv stc : Loc),
      s.[store, go!"ReadView"] ↦□
        (interface.mkOk (go.GoType.PointerType readView.ty) #rv : GoInterface) ∗
      rv.[readView, go!"kv"] ↦□
        (interface.mkOk (go.GoType.PointerType watchableStore.ty) #w : GoInterface) ∗
      w.[watchableStore, go!"stopc"] ↦□ stc ∗ stopCloser stc ∗ wsWaiter w)
    else iprop(True))

/-- **The store's open token** (exclusive): `Compact`, `Restore` and `Close` take it, the first two
give it back. A compaction schedules its job after releasing `s.mu`, on a scheduler `Close` stops and
`Restore` replaces; and two concurrent compactions could schedule their jobs out of the order of
their revisions. **Scope restriction** (marked): compactions are not concurrent with each other or
with a restore or close (etcd compacts from its apply thread; the tester does not compact).
Defined (`KV.Compact.contract`, 2026-11-06; `notes/mvcc-api-invariants.md` §2): at the store's
location (`locIs`, the handle's) and current physical names `p`, the restorable compaction right at
the compaction revision `c` (`compactRightR`: its queue, the closer's share, the jobs' lease), the
right's quarter of the API's compaction authority, the compactor's reader token
(`checkPrevCompactionCompleted`'s) and its write-back supply. (Track A, `New.spec`, 2026-11-06) The
closer's pieces (`openRest`): the current backend compacting, and a watchable store's own closer (its
stop channel's close and the loops' waiter), found from the inner store's location through its read
view. Still to add (§2): the restore's pieces (`Restore`). -/
@[no_expose] def mvccOpen (γ : MvccName) : IProp GF :=
  iprop(∃ (s : Loc) (p : PhysNames) (c : Int), api.locIs (γ : StoreNames).api s ∗
    compactRightR s ((γ : StoreNames).withPhys p) c ∗
    api.crevAuth (γ : StoreNames).api (1 : Qp).half.half c ∗
    storeRT ((γ : StoreNames).withPhys p) ∗ kbWTSupplyM p.kb ∗ ⌜-1 ≤ c⌝ ∗ openRest γ p s)

/-- **`t` is a transaction of `γ`, begun with `trace`, at `k`** (exclusive; it holds the caller's
thread token until its `End`, not the trace). Defined (M4, track B, 2026-11-06; `Api/TxnHandle.lean`): the
internal transaction without its trace, at the state it began at, with the thread token's way back. -/
@[no_expose] def mvccTxn (t : GoInterface) (γ : MvccName) (trace : Loc) (k : MTxn) : IProp GF :=
  api.mvccTxnI t (γ : StoreNames) trace k

/-- The rest of a stream's handle: its channel (buffered) and the channel's invariant, at a
watchable store `s` of `γ` (stage 2, the watch chain, 2026-11-05: what `wsChan_recv.law` needs);
the stream `ws` itself (`isWatchStreamAt`, over the store at that channel), and the store's
pools its calls draw on: the watch tokens (`watchTokPool`, a registration's cost) and the
readers' slots (a thread pool of `watchReader`s, lent to each call of the store); and the channel's
progress fact (`progFact`, what a `-1` response the store sends on it carries). -/
private def isMvccWatchStreamRest (ws : GoInterface) (γ : MvccName) (ι : WsName) : IProp GF :=
  iprop(∃ (γw : WsNames) (γc : WatchChanNames) (w s st : Loc) (γo : WsStreamNames) (γp : GName),
    ⌜(ι : api.WsAbs) = wsAbsOf γw (ι : api.WsAbs).ch γc ∧ γw.st = (γ : StoreNames) ∧
      0 < sint.Z γc.ch.chanCap ∧ ws = interface.mkOk (go.GoType.PointerType watchStream.ty) #w⌝ ∗
    isChan (ι : api.WsAbs).ch γc.ch WatchResponse ∗
    inv watchN (watchChanInv γw (ι : api.WsAbs).ch γc) ∗
    isWatchStreamAt w (interface.mkOk (go.GoType.PointerType watchableStore.ty) #s)
      (storeWatchParams s st γw) γo (ι : api.WsAbs).ch γc ∗
    watchTokPool γw ∗ threadPool.isThreadPool watchRdPoolN γp (watchReader s st γw) ∗
    progFact γc.prog)

/-- **`ws` (the `WatchStream` `NewWatchStream` returned) is a stream of `γ`, named `ι`**
(persistent). -/
@[no_expose] def isMvccWatchStream (ws : GoInterface) (γ : MvccName) (ι : WsName) : IProp GF :=
  iprop(⌜(ι : api.WsAbs).st = (γ : StoreNames).api⌝ ∗ □ isMvccWatchStreamRest ws γ ι)

/-- **The stream's state is `S`** (exclusive, timeless; the client's). -/
@[no_expose] def wsState (ι : WsName) (S : StreamState) : IProp GF := api.wsStateI ι S

/-- **The stream has sent at least `n` responses** (persistent; round 14, A1): `Watch` gives it at
the watcher's stamp `k`, so that a client can match a stream-wide progress response (the `j`-th
received, `j ≥ k`) with the watchers registered before it; the non-blocking receive's empty case
bounds it by what was received (`wsChan_recv`). -/
@[no_expose] def wsSentLb (ι : WsName) (n : Nat) : IProp GF := api.wsSentLbI ι n

/-- **The consumer has received `rs`**, in order (exclusive, timeless). -/
@[no_expose] def wsRecv (ι : WsName) (rs : List WResp) : IProp GF := api.wsRecvI ι rs

/-- **A storage implementation** (opaque; the design "mvcc's API over its storage abstraction",
approved by the user, 2026-11-06): what the store keeps its history in, as mvcc's storage contract
sees it. Phase A: sealed over the real backend's instance (`KBReal`); the bridge module
(`mvcc/EtcdBackend.lean`) names etcd's backend as one (`etcdStorage`). -/
@[no_expose] def MvccStorage : Type := KBReal

/-- **The storage's Go value** (what `New`, `NewStore` and `Restore` take). -/
@[no_expose] def storageVal (B : MvccStorage) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
    #(B : KBReal).be

/-- **A share `dq` of the storage's post-lock hook, at `f`** (fractional; sealed): the hook the
storage's batch lock runs (`hookRun`), `nil` for none. -/
@[no_expose] def storageHook (B : MvccStorage) (dq : DFrac) (f : GoFunc) : IProp GF :=
  backend.plHookAt (B : KBReal).γB dq f

/-- **A commit request on the storage**, from `X` to `Y`, its batch lock's invariant `Pk` (sealed):
what a forced commit (`Commit`, a compaction's, a resumed one's) turns `X` into. -/
@[no_expose] def storageReq (B : MvccStorage) (Pk X Y : IProp GF) : IProp GF :=
  backend.commitReq (B : KBReal).γB (B : KBReal).P Pk (B : KBReal).be X Y

/-- **What the store gives back of a storage it no longer uses** (sealed; `Restore`'s give-back of
the old storage). -/
@[no_expose] def storageRest (B : MvccStorage) : IProp GF :=
  iprop([∗list] _x ∈ List.replicate nReaders (), backend.bOpen (B : KBReal).γB backend.rdOpen)

/-- **The number of the store's readers** (sealed): a store admits at most this many threads. (Track
A, `New.spec`, 2026-11-06: the backend's counted stock less three, the watchable store's two loops'
and the compactor's reader slots, held for good, so that the readers' pool a watchable store's
handle holds, `isMvccWatchable`, has a slot for every thread but one. The server's request,
2026-11-06, decided by the coordinator: two fewer again, `rdStockN - 5`, the backend's opener keeping
two counted slots for good, `etcdStorage_open.law`.) -/
@[no_expose] def mvccReaderN : Nat := backend.rdStockN - 5

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
`Pk` is the store's). -/
@[no_expose] def mvccBackend (γ : MvccName) (q : Qp) (B : MvccStorage) (Pk : IProp GF) : IProp GF :=
  iprop(api.shareTok (γ : StoreNames).api q ∗
    ∃ (p : PhysNames) (o : StoreObjs) (d : KBReal),
      curAt ((γ : StoreNames).withPhys p) (DFrac.own q.half.half.half) o ∗
      ⌜p.kb = some d ∧ d.cm = true ∧ (d : MvccStorage) = B⌝ ∗
      □ backend.isBackend d.γB d.P (lateW d.gx) Pk d.be ∗
      □ (∃ s : Loc, writerReg s ((γ : StoreNames).withPhys p)) ∗
      □ hookP ((γ : StoreNames).withPhys p) Pk)

/-- **The storage `B`, with batch-lock invariant `Pk`, holds the history `L` compacted at `c`, ready
for a store over it**, recording an unfinished compaction iff `u` (which `Restore` resumes)
(exclusive; sealed; the design "mvcc's API over its storage abstraction", 2026-11-06: in place of
`mvccBackendFor`). What `New`, `NewStore` and `Restore` take of a storage: `B` meets mvcc's storage
contract at `Pk` (the store's `isKeyBackendG` with the compaction's clauses and the clean read), its
view of the `Key` bucket at the image of `(L, c)` with the history's receipt `⧖ (logCh L)`, its
compaction records' ownership, the store's write tokens and supply, `mvccReaderN` reader tokens, and
the registration of the store's write resource. Made by the storage's provider (etcd's backend: the
bridge's `etcdStorage_open.law`). Phase A (M3, 2026-11-06): defined over etcd's backend's open, the
store's part of `newPostKP` at the image's data `D`, the bridge's premises (`bridgeParams`, the
compaction mode, `keySized`), and the payment rights. -/
@[no_expose] def mvccStorageFor (B : MvccStorage) (Pk : IProp GF) (L : Log) (c : Int) (u : Bool) :
    IProp GF :=
  iprop(∃ (bk : KBReal) (D : backend.Data),
    ⌜(bk : MvccStorage) = B ∧ bridgeParams bk.P ∧ bk.cm = true ∧ snap.imageOk D L c u⌝ ∗
    ⧖ (logCh L) ∗
    □ backend.isBackend bk.γB bk.P (lateW bk.gx) Pk bk.be ∗ □ (∀ γ b', keySized γ bk.P b') ∗
    backend.bViewC bk.γB 1 (backend.vData bk.P (D, ⟨∅, W64 0⟩)) true ∗
    backend.dlInit bk.γB ∗ backend.fkCl bk.γB bk.P D ∗ backend.srSlot bk.be ∗
    ([∗list] _x ∈ List.replicate nReaders (), backend.rdTok bk.γB bk.P bk.be) ∗ lateReg bk.gx ∗
    backend.wbTok bk.γB ∗ backend.wbTok bk.γB ∗ □ (⧗ 1 ={⊤}=∗ backend.wbTok bk.γB) ∗
    ([∗list] _x ∈ List.replicate nReaders (), backend.bOpen bk.γB backend.rdOpen))

/-- **What the post-lock hook `f` does** under the batch lock of invariant `P`, from the caller's
`Pre`: `f`'s triple to `Q`, or with no hook (`nil`), the caller's view shift. -/
def hookRun (P : IProp GF) (f : GoFunc) (Pre Q : IProp GF) : IProp GF :=
  if f = func.nil then iprop(P ∗ Pre ={⊤}=∗ Q)
  else iprop(□ {{ P ∗ Pre }} (App (Val #f) (Val #())) {{ RET #(); Q }})

/-- **The storage's hook is `f`, for good** (frozen: the discarded share of `storageHook`). -/
abbrev hookIs (B : MvccStorage) (f : GoFunc) : IProp GF := storageHook B DFrac.discard f

instance hookIs_persistent (B : MvccStorage) (f : GoFunc) : Persistent (hookIs (GF := GF) B f) := by
  unfold hookIs storageHook; infer_instance

instance storageReq_persistent (B : MvccStorage) (Pk X Y : IProp GF) :
    Persistent (storageReq (GF := GF) B Pk X Y) := by
  unfold storageReq; infer_instance

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
  iprop(⌜rd ≠ func.nil⌝ ∗ □ ∀ (q : Qp) (B : MvccStorage) (P Pre Q : IProp GF) (f : GoFunc) (R : MvccState → IProp GF),
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
  ∀ (γ : MvccName) (trace : Loc) (te : Bool) (q : Qp) (B : MvccStorage) (P Pre Q : IProp GF)
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
needs), and the state's log well formed, each revision of fewer than `2 ^ 63` changes (txn's
migration, 2026-11-05: decided by the coordinator, A). -/
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
        ⌜∀ r' : Nat, σ.crev ≤ (r' : Int) → r' ≤ σ.rev → stateOk (stateAt σ.log r')⌝ ∗
        ⌜LogWf' σ.log ∧ ∀ cs ∈ σ.log, cs.length < 2 ^ 63⌝ }}

/-- **`Put(key, value, lease)`** (a write transaction of one put): the hook, then the commit's two
steps at the state the update gives (the lessor's item map that state's). -/
abbrev KV.Put.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (key value : GoSlice) (k vv : GoString) (leaseID : w64) (L : List w64)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (q : Qp) (B : MvccStorage)
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
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (q : Qp) (B : MvccStorage)
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
revision, `ErrFutureRev` and no channel. A revision of at least 1 (the user, 2026-11-04: a
`Compact(0)` mid-job restores to compaction revision -1, `issues/etcd-restore-scheduled-compact-zero.md`;
`EtcdServer.Compact.spec` requires it too). -/
abbrev KV.Compact.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (trace : Loc) (te : Bool) (rev : w64) (q : Qp) (B : MvccStorage)
    (P : IProp GF) (f : GoFunc) (Pre Q' Post X Y : IProp GF) (Q : MvccState → IProp GF),
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗ mvccOpen γ ∗ threadTok ∗ ⌜trace ≠ null⌝ ∗
      ⌜1 ≤ sint.Z rev⌝ ∗
      traceutil.ownTrace trace te ∗ mvccBackend γ q B P ∗ hookIs B f ∗
      X ∗ storageReq B P X Y ∗
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
  ∀ (γ : MvccName) (q : Qp) (B : MvccStorage) (Pk X Y : IProp GF),
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗ threadTok ∗ mvccBackend γ q B Pk ∗ X ∗
      storageReq B Pk X Y }}
    (App (Val #(methods ty go!"Commit" v)) (Val #()))
  {{ RET #(); threadTok ∗ mvccBackend γ q B Pk ∗ Y }}

/-- **`Restore(b')`** from the backend `B'` holding the history `σ'.log` compacted at `σ'.crev`
(decision 3, the user, 2026-11-03: at any share of the new backend's post-lock hook): by the
caller's update, at a state whose history `σ'`'s extends (the compaction revision not lowered), the
state `σ'`; the store's backend now `B'`, the old one's reader slots' open shares back (`Restore` waits out
every transaction, the scheduler and the sync loops); the lessor's items re-attached (the restored history's receipt is inside `mvccStorageFor`, from
the image, round 16, and the update is given it, as at every step that changes the
history; the history's length bound follows from it, a committed revision never being empty). When
the image
records an unfinished compaction (`u`), `Restore` resumes it: under the new backend's batch lock,
running its post-lock hook `f` once (from `Pre` to `Q'`, giving the lock's invariant `Pk'` back), and
committing once (the new backend's commit request, `X` to `Y`); otherwise neither, and `Pre`, `X`
come back. The hook at any share `dq` (`storageHook`), given back: unset and owned (at `nil`,
etcd's order: it sets the new backend's hook after `Restore`, `server.go:1078`), or frozen at any
hook (`hookIs`). The old storage's rest back (`storageRest B`). -/
abbrev KV.Restore.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (B B' : MvccStorage) (Pk Pk' : IProp GF) (σ' : MvccState) (u : Bool) (L : List w64)
    (dq : DFrac) (f : GoFunc) (Pre Q' Post X Y : IProp GF) (Q : MvccState → IProp GF),
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗ threadTok ∗ mvccOpen γ ∗ mvccBackend γ 1 B Pk ∗
      mvccStorageFor B' Pk' σ'.log σ'.crev u ∗
      ⌜MvccReachable σ' ∧ σ'.pending = none⌝ ∗
      storageHook B' dq f ∗ Pre ∗ hookRun Pk' f Pre Q' ∗ (Q' ={⊤}=∗ Pk' ∗ Post) ∗
      X ∗ storageReq B' Pk' X Y ∗
      lease.leaseOwn (mvccLeases γ) L ∅ ∗
      ⌜∀ it lid, (pendItems σ'.log []).lookup it = some lid →
        lid ∈ L ∧ (it.Key'.length : Int) < 2 ^ 63 - 1⌝ ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ ∗ ⌜σ.log <+: σ'.log ∧ σ.crev ≤ σ'.crev⌝ }>
          @ ⊤ \ ↑mvccN, ∅ <{ mvccState γ σ' ∗ ⧖ (logCh σ'.log), COMM Q σ }> }}
    (App (Val #(methods ty go!"Restore" v))
      (Val #(storageVal B')))
  {{ RET #(GoInterface.nil); threadTok ∗ mvccOpen γ ∗ mvccBackend γ 1 B' Pk' ∗
      storageRest B ∗
      storageHook B' dq f ∗
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
        stateOk (stateAt k.readLog r')⌝ ∗
      ⌜LogWf' k.readLog ∧ ∀ cs ∈ k.readLog, cs.length < 2 ^ 63⌝ }}

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

/-- A write transaction's delete of a range: the deletes of the range's present keys appended to
the pending revision; the state after them well formed, each revision of fewer than `2 ^ 63` changes
(txn's migration, 2026-11-05: decided by the coordinator, F). -/
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
      ⌜n = W64 (ds.length : Int) ∧ rev = W64 ((writeRev σ.log (pend ++ ds) : Nat) : Int)⌝ ∗
      ⌜LogWf' (σ.log ++ [pend ++ ds]) ∧ ∀ cs ∈ σ.log ++ [pend ++ ds], cs.length < 2 ^ 63⌝ }}

abbrev Txn.Changes.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (trace : Loc) (k : MTxn),
  {{ pkgInit ∗ mvccTxn (interface.mkOk ty v) γ trace k }}
    (App (Val #(methods ty go!"Changes" v)) (Val #()))
  {{ (chs : GoSlice), RET #chs; mvccTxn (interface.mkOk ty v) γ trace k ∗
      ⌜uint.nat chs.len = k.pend.length ∧ 0 ≤ sint.Z chs.len⌝ }}

/-- A read transaction's gives the thread token back; a write transaction's commits in two steps of
the caller's updates at the state it began at (`σ₀`), with the batch lock's invariant `P` back. The
notify step gives the update the receipt of the history it makes (`⧖ (logCh ..)`, round 16: what the
caller's model of the history needs, client/v3's `kvLogOk`, at the step that makes it; `Put`,
`DeleteRange` and `Restore` too). -/
abbrev Txn.End.contract (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (trace : Loc) (k : MTxn) (q : Qp) (B : MvccStorage) (P Q : IProp GF),
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
  {{ pkgInit ∗ isMvccWatchStream (interface.mkOk ty v) γ ι ∗ threadTok ∗
      (⌜ctx = interface.mk context.todoCtx.ty #(zero_val context.todoCtx)⌝ ∨
        (context.isContext ctx cd ∗ trace.spanCtxOk ctx)) ∗
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
  ∀ (lg : Loc) (le : GoInterface) (cfg : StoreConfig) (B : MvccStorage) (Pk : IProp GF)
    (γl : GName) (rd0 : GoFunc),
  batchLimitOk cfg.CompactionBatchLimit' → receiptBound GF ≤ 2 ^ 48 → threadBound GF ≤ mvccReaderN →
  {{ pkgInit ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      mvccStorageFor B Pk mvccStart.log mvccStart.crev false ∗
      lease.lessorRdOf γl ∗ isLessor le γl ∗ lease.rdOwn γl rd0 }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.New)) (Val #lg))
      (Val #(storageVal B)))
      (Val #le)) (Val #cfg))
  {{ (ws : Loc), RET #(interface.mkOk PW #ws);
      ∃ γ : MvccName, ⌜mvccLeases γ = γl⌝ ∗
        isMvcc (interface.mkOk PW #ws) γ ∗ mvccState γ mvccStart ∗ mvccOpen γ ∗
        mvccBackend γ 1 B Pk ∗ (∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvccDeleter rd γ) }}

/-- **`mvcc.NewStore(lg, be, le, cfg)`**: as `New`, a store without watchers. -/
abbrev NewStore.spec : Prop :=
  ∀ (lg : Loc) (le : GoInterface) (cfg : StoreConfig) (B : MvccStorage) (Pk : IProp GF)
    (γl : GName) (rd0 : GoFunc),
  batchLimitOk cfg.CompactionBatchLimit' → receiptBound GF ≤ 2 ^ 48 → threadBound GF ≤ mvccReaderN →
  {{ pkgInit ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      mvccStorageFor B Pk mvccStart.log mvccStart.crev false ∗
      lease.lessorRdOf γl ∗ isLessor le γl ∗ lease.rdOwn γl rd0 }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewStore)) (Val #lg))
      (Val #(storageVal B)))
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
  (∀ B f, Persistent (hookIs (GF := GF) B f)) ∧ (∀ B Pk X Y, Persistent (storageReq (GF := GF) B Pk X Y)) ∧
  (∀ γ σ, Timeless (mvccState (GF := GF) γ σ)) ∧ (∀ ι S, Timeless (wsState (GF := GF) ι S)) ∧
  (∀ ι rs, Timeless (wsRecv (GF := GF) ι rs)) ∧
  (∀ γ B Pk, Fractional (fun q => mvccBackend (GF := GF) γ q B Pk))

abbrev excl.law : Prop :=
  (∀ γ σ σ', mvccState (GF := GF) γ σ ∗ mvccState γ σ' ⊢ False) ∧
  (∀ ι S S', wsState (GF := GF) ι S ∗ wsState ι S' ⊢ False) ∧
  (∀ ι rs rs', wsRecv (GF := GF) ι rs ∗ wsRecv ι rs' ⊢ False) ∧
  (∀ γ, mvccOpen (GF := GF) γ ∗ mvccOpen γ ⊢ False)

/-- **mvcc's error variables are `errors.New`'s** (the tester's migration, 2026-11-06, G2: decided
by the coordinator): the package's initialization gives `ErrCompacted`, `ErrFutureRev` and
`ErrEmptyWatcherRange` as `*errors.errorString` values with their messages (`errorsNewVar`), so a
client's `err == ErrFutureRev` (Go's interface `==`, which checks the dynamic type's
comparability) is provable without mvcc's internals. -/
abbrev errVars.law : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ⊢
    EtcdGrove.errorsNewVar ErrCompacted go!"mvcc: required revision has been compacted" ∗
    EtcdGrove.errorsNewVar ErrFutureRev go!"mvcc: required revision is a future revision" ∗
    EtcdGrove.errorsNewVar ErrEmptyWatcherRange go!"mvcc: watcher range is empty"

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
  ∀ ws γ ι, isMvccWatchStream (GF := GF) ws γ ι ⊢
    isChan (wsChanOf ι) (wsChanNames ι) WatchResponse ∗
    □ (∀ (rs : List WResp) (Φ : WatchResponse → Bool → IProp GF),
      wsRecv ι rs -∗
      (∀ (v : WatchResponse) (ok : Bool),
        (if ok then ∃ r : WResp, wsRecv ι (rs ++ [r]) ∗ wrespIs v r else wsRecv ι rs) -∗ Φ v ok) -∗
      recvAu (wsChanNames ι) WatchResponse Φ) ∗
    □ (∀ (rs : List WResp) (n : Nat) (Φ : WatchResponse → Bool → IProp GF) (Ψ : IProp GF),
      wsRecv ι rs -∗ wsSentLb ι n -∗
      ((∀ (v : WatchResponse) (ok : Bool),
          (if ok then ∃ r : WResp, wsRecv ι (rs ++ [r]) ∗ wrespIs v r else wsRecv ι rs) -∗ Φ v ok) ∧
        (wsRecv ι rs -∗ ⌜n ≤ rs.length⌝ -∗ Ψ)) -∗
      nonblockingRecvAuAlt (wsChanNames ι) WatchResponse Φ Ψ)

/-- **The stream has sent at least nothing** (the review of round 14: v3rpc's drain before a
refused create, which has no stamp). -/
abbrev wsSentLb_zero.law : Prop := ∀ ι, ⊢ wsSentLb (GF := GF) ι 0

abbrev wsRecv_ok.law : Prop :=
  ∀ ws γ ι rs S σ,
    isMvccWatchStream (GF := GF) ws γ ι ∗ wsRecv ι rs ∗ wsState ι S ∗ mvccState γ σ ⊢
      ⌜wsRecvOk σ S rs⌝

/-- **A reachable state's history is well formed, its notified history too** (round 16, pure, of the
API's own definitions: by induction on `MvccReachable`, `notify`'s `LogWf` and `commitLog`; the
server's read path and the watch path take their clients' `LogWf'` from it). -/
abbrev reach_logWf.law : Prop :=
  ∀ σ : MvccState, MvccReachable σ → LogWf' σ.log ∧ LogWf' σ.notifiedLog

/-- `reach_logWf.law` holds: a fact of the vocabulary (`ApiState.reach_logWf`), no obligation of the
implementation. -/
theorem reach_logWf.law_holds : reach_logWf.law := reach_logWf

end laws

end api
end mvcc
end EtcdGrove
end Perennial
