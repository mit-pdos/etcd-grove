# Integration I6 (storage): mvcc, adt, backend, schema, pkg leaves, their boundaries

Integration agent I6, 2026-11-09, following `integration-brief.md`. Batches 3e, 3f, 4a, 4b. Three
sub-agents did parts of it (schema ↔ backend bundles; the pkg leaves, boundaries and traces; 3f's
watch half and adt); their findings are merged below.

## The central item: `Backend.keyBackend_intro` (etcd's backend meets mvcc's storage contract)

mvcc's contract rows (`storage/mvcc/ApiStorage.lean`) changed as 4a asked (`req/..._mvcc.md`, "from
4a, round 1"), and the bridge (`storage/backend/MvccStorage.lean`) was rewritten against them; its
header now goes through every row against the backend spec it rests on.

| 4a's item | done | where |
|---|---|---|
| (a) open share on the lock rows and `ForceCommit` | `kbOpen B q` (fractional): `LockInsideApply`/`LockOutsideApply`/`ForceCommit` take it, `Unlock`/`ForceCommit` give it back; `kbLocked B q D0 D` carries the share; `mvccStorageFor` gives `kbOpen B 1`, `storageRest` returns it; `mvccClosed_rest` now takes `mvccBackend γ 1 B Pk` and returns `kbOpen B 1` | `ApiStorage.lean`, `Api.lean` |
| (b) the `key` delete: a key not put in the session | `⌜D.keys k = D0.keys k⌝` | `ApiStorage.lean` |
| (c) entry bound on both put rows | `k.length + v.length ≤ kbEntryMax` (`2^28`, = 4c's `bboltEntryMax`) | `ApiStorage.lean` |
| (e) concurrent read transaction: single keys, lingering deletes | the read-transaction range row split: the shared `ReadTx` keeps `KeyData.rtRange` (exact); a concurrent one (`rt ≠ kbReadTx B`) is single-key (`one = true`: a `nil` end) with `KeyData.linger` (exact for keys the snapshot has) | `ApiStorage.lean` |
| (f) bytes lent, not for good | `rangeLent kl vl l L` (outer slices owned, inner bytes `Schema.lentIn dq`, wand back to `L`), lent against a **share of a new liveness token** `kbLive B t p` (fractional; `Lock*`/shared `RLock`/`ConcurrentReadTx` give `kbLive … 1`, `Unlock`/`RUnlock` take it). The transaction's own resource (`kbLocked`, `kbRead`) is kept, not lent. | `ApiStorage.lean`, backend `Api.lean` |
| (g) `hookRun` holding the session | **not taken** (below) | |

Why (f) differs from 4a's request (lend against `R`, the transaction resource): two of mvcc's
sketches need bytes out while the transaction is used again. The compaction job
(`kvstore_compaction.go:58-71`) deletes the very key slices its batch range returned
(`tx.UnsafeDelete(schema.Key, keys[i])`) while holding them; `restore` (`kvstore.go:345-361`)
sends each chunk's key slices to the index goroutine (`restoreChunk`'s `revKeyValue.key`) and reads
the next chunk before that goroutine is done, then `RUnlock`s after `<-revc`. Lending against `R`
makes both unprovable (the session is behind the wand while the keys are out). So the backend got
the same token: `Backend.beLive γ t p` (fractional), and the backend's range specs keep
`beSess`/`beRd` and lend against `beLive γ t pl`; `Backend.rangeRes` lends the inner slices only
(`Backend.lentIn`). Changed backend files: `Api.lean` (`beLive`, `beLive_fractional`, `lentIn`,
`rangeRes`, `beSess_rd` lends `beLive γ (rtLoc γ) 1` too), `batchTxBuffered__{Lock,LockInsideApply,
LockOutsideApply,Unlock,UnsafeRange}`, `readTx__{RLock,RUnlock,UnsafeRange}`,
`baseReadTx__UnsafeRange`, `concurrentReadTx__{RUnlock,UnsafeRange}`, `backend__ConcurrentReadTx`.
The internal helpers (`unsafeRange`, `batchTx.UnsafeRange`) still lend against `curOver`/`btPhys`:
their realization over 4c needs the liveness split out of `boltTx` (below, 4c).

Restore's loans: `InternalStore.lean`'s `rkvProducer c ents n L` (the key bytes lent to the
goroutine so far), `rkvIs v e dq` (a fraction), `rkvSend` (the loan joins `L`), new
`rkvProducer_mono`, `rkvClosed`, `rkvClose` (`close(rkvc)`), `revConsumer c kc ti ents`, `revRecv`
(the loans back with the index); `restoreChunk` takes the chunk's lent bytes at `dq` and returns the
values'; `restoreIntoIndex` gives `rkvProducer rkvc ents 0 True`.

The two-step `Unlock` (F1) had one more consequence: `SetScheduledCompact`/`SetFinishedCompact` took
the caller's single update, which cannot drive the row's nested pair (the second update needs the
caller's invariant again). Their `kbObs` body is now the nested pair (to `D'` twice: a `Meta`-put
session has `KeyData.mid D D' = D'`), and they take and return `kbOpen B q`.

**(g), not taken.** Lending the hook the session needs `hookRun` to name the storage (`hookRun B Pk f
Pre Q`, the session lent as an `H` with a read law `kbLent B H`), but `Mvcc.hookRun Pk f Pre Q` is
cited with four arguments by `lease/{Api,Lease__persistTo,lessor__Grant,lessor__Checkpoint}.lean`,
`etcdserver/txn/Api.lean`, `auth/{Api,NewAuthStore}.lean`, `etcdserver/apply/applierV3backend__LeaseGrant.lean`
(other owners). The bridge holds without it (mvcc's `hookRun` gives 4a's by framing the session
around the hook). The cost is the server's: its post-lock hook (`cindex.go:102-110`,
`UnsafeConsistentIndex` reading `ReadTx()` without `RLock` while the atomic index is `0`, i.e. a
fresh member's first applies) cannot be proved against mvcc's `hookRun`, which gives it no session
for `Backend.beSess_rd`. Proposal for 3c/3b/3d/2d together: `Mvcc.hookRun B Pk f Pre Q :=
□ ∀ H Φ, kbLent B H -∗ H ∗ Pk ∗ Pre -∗ ▷ (H ∗ Q -∗ Φ #()) -∗ WP f` with `kbLent` persistent and the
bridge's law `kbLent B H ⊢ □ ∀ G V, H ∗ beVis γ G V -∗ beRd γ (rtLoc γ) G V ∗ beLive γ (rtLoc γ) 1 ∗
(… -∗ H ∗ beVis γ G V)` (the bridge instantiates `H := beSess γ q Fp.none S`). An open question.

**The lent lock (3e's `kbHeld`, 3c's `beTxHeld`).** The bridge's `□ (kbHeld B ∗-∗ ∃ q S, beSess γ q
mvccFp S)` was not provable once `kbLocked` carries the open share (the way back loses which share
and which session). It is now a lend law: `kbHeld B` gives a session `beSess γ q' mvccFp S` and takes
back any `S'` with `Sess.sameOn mvccFp S S'` (same base, mvcc's cells and puts untouched: the
lessor's lease delete). For 3c: `beTxHeld be` can be realized as `∃ B, ⌜be = ok (storageVal B)⌝ ∗
Mvcc.kbHeld B` (so `mvccDeleter_rdOk`'s premise `□ (kbHeld B ∗-∗ beTxHeld _)` is immediate); the
lessor's `UnsafeDeleteLease` under it then needs `writable γ mvccFp (lease cells)`, i.e. the lease
bucket untracked (`beVis_drop` → `beNoVis`) by whoever owns it (the server), since mvcc's session
publishes only `mvccFp`.

## mvcc's sketches re-checked against the new rows

- `store.Read`/`readView.Range`/`storeTxnCommon.rangeKeys`: a concurrent read transaction's reads
  are by revision, of revisions the image has (`kvstore_txn.go:126`): `KeyData.linger` is exact
  there; bytes unmarshalled inside, given back (`kbLive` in `txnCommon`). Sketches updated.
- `UnsafeRead{Finished,Scheduled}Compact`: restated over `rangeOk t R L D false rg ∗ R ∗ L p` (the
  value parsed inside the call, its bytes back).
- `store.scheduleCompaction`: batch range lent against half the session's liveness, deletes of the
  lent keys (each committed before the session: (b) holds), `WriteKeyValue`, bytes back, `Unlock`'s
  nested update (the finished key at the write-back, the deletes at the commit); `ForceCommit` on the
  job's open share (`compactJobRes`, `Internal.lean` header). Sketch updated.
- `store.restore`/`restoreChunk`/`restoreIntoIndex`: as above (loans through the channels; the last
  key's bytes read on the main thread with the other half of the chunk's fraction).
- `storeTxnWrite.End`, `store.Write`: a write transaction only puts to `Key` (a delete is a
  tombstone put), so `KeyData.mid D0 D = D` and the second update is a no-op the store's invariant
  gives again; the open share comes from the reader token's part. Sketches updated.
- `NewStore`: `schema.UnsafeCreateMetaBucket(tx)` (4b's spec over `Schema.txWr`) built from the
  contract's create row at the scope `⟨fun _ => some [], (· = .metaB)⟩` (put/delete rows vacuous).
  Sketch updated.
- `updateCompactRev`, `compactLockfree`, `checkPrevCompactionCompleted`, `Compact`, `Commit`,
  `Restore`: their internal predicates (`storeWB`, `compactJobRes`, `mvccBackend`) carry the open
  share in the realization (`Internal.lean`'s header, `Api.lean`'s `mvccBackend` text); no statement
  change.
- The hash (`hashStorage.*`, names only, trusted): no storage row needed (`hash.go:35`'s
  `UnsafeForEach` on a concurrent read transaction would be `Backend.rdOrderL`).

## 3f's needs of 3e (the watch half), and 3f's own repairs

Met in 3e's files by I6:
- **`mvccLb` inside `mvccState`** (3f round 1, item 1): `Api.lean`'s realization of `mvccState` now
  holds a half of the authority of the monotone record of `σ.notified` whose fragments are `mvccLb`.
- **G2, the watchable write transaction's `End`**: `Txn.End.contract`'s first update admits the
  already-notified state (`⌜σ = σ₀ ∨ σ = σ₀.notify pend⌝`), and `End` accepts a transaction whose
  records were taken (`mvccTxnNC`, new); `Txn.Changes.contract` gives `mvccTxnChs t chs` (new,
  persistent); `InternalTxn.mvccTxn_changes` (new) opens a `*metricsTxnWrite` handle's records.
- **G3, the image at the compaction revision**: `Internal.mvccImage_above` now also covers revision
  `h.compacted` (each event that is its key's last change there is present; every entry at or above
  it is its event).
- **G4, one decoding relation**: `InternalStore.kvBytes_decodes` (`kvBytes m bs → kvDecodes bs m`).

**G1, left open (3e and 3f together):** the watchable store's two sync loops read the storage
directly (`s.store.b.ReadTx()`, `watchable_store.go` `syncWatchers`) under the watchable `s.mu`, the
only thing excluding `Restore` (which returns every slot of the old storage, `storageRest B
mvccReaderN`). 3e reserves their slots (`mvccOwnN`) but nothing hands them out, and a hand-off needs
`store.Restore`/`Close` to know no loop pass is running, which only the watchable lock knows. Every
design within the current contracts fails on one point: the client holds `mvccRestoreGate γ 1` and
the loops' passes must exclude `Restore`, at the same `γ`. A fix needs either the watchable store's
own ghost names over the inner store's (3f realizing `mvccRestoreGate` of its `γw` with the loops'
shares inside), or client-visible loop tokens that `NewStore` gives and `KV.Restore`/`mvccClosed_rest`
take back. A design decision; until then `New`/`newWatchableStore` are not provable from
`NewStore.spec` alone.

3f's files (sub-agent C): `New`/`newWatchableStore` follow 3e's round 1 (no `MvccReachable`;
`mvccRevLent γ 0 ∗ mvccRestoreGate γ 1`); `WatchInternal` uses 3e's `kvBytes`/`revOfBytes` (the
provisional `kvEnc`/`revEnc` gone), the loops borrow a slot per pass (G1); `kvsToEvents` reads the
storage's lent bytes at a fraction; `rangeEvents` gains `h.compacted ≤ lo` (its post was false
below the compaction); `syncWatchers`, `watchableStoreTxnWrite.End`, `Restore`, `Close` sketches cite
the real names; `watchStream.Watch` takes `OtelTrace.ctxSpanOk ctx` in place of `Context.ctxOk ctx`
(`SpanFromContext` needs it; the cancel closure ends the span). adt: `intervalTree.Contains`' post
adds `b = "" → r = false` (3d's request, adt req "from 3d" item 3); `ivt_agree` dropped from the
header.

## The pkg leaves, the third-party boundaries, traces (sub-agent B)

All nine directories build (53 modules); no provisional names declared there. Changed:
`traceutil/Api.lean`, new law `traceOwn_empty` (`traceOwn t ⊢ ∃ e, traceEmpty t e`: 2c's `ctxTrace`
holds only `traceOwn`, txn's `ctxTraceOwn` needs the flag); snippet `ReqCtxTraceLent`
(`pkgleaves/trace.go`). Sketches fit their callees (pbutil/2a's Proto, traceutil/W0, `Tracer.Start`/otel,
`GracefulClose`/2f's `roundTripperOk`) but **ioutil**, which rests on 2f's missing
`Http.readerAt_wrap`/`readerCloser_wrap`.

**Traces exclusive everywhere**: no file uses a persistent or provisional trace predicate any more.
Remaining: 2c's `ApiReq.ctxTrace` could keep `traceEmpty t false` (else cite `traceOwn_empty` in
`EtcdServer__doSerialize`); `read/Read__LinearizableReadLoop`'s sketch should spell out the trace
threading (`ctxTraceIs_background`, `Step`/`AddField`, `LogAllStepsIfLong`); 2c's `EtcdServer__*`
sketches should cite `TraceUtil.tracer_init` for `Tracer.Start`; mvcc `Api.lean`'s `⌜trace ≠ null⌝`
beside `traceOwn` is redundant (cosmetic, kept).

## The schema over the backend (sub-agent A)

**New `storage/backend/SchemaTx.lean`**: the laws 4a owed 4b (the schema's bundles for 4a's
transactions), each checked against the backend spec it rests on: view families `btView` (session,
`beLive γ (btLoc γ) 1`, the caller's `beCur`, a `madeIn` fact, a frame) and `rtView` (`beRd`,
`beLive γ (rtLoc γ) 1`); `btRd` (`txRd`, `txRange` of the batch), `btWr` (`txWr`; the scope leaves
`key` alone and is `writable`), `rtRd` (`txRd` of the shared read transaction, after `RLock` or by
`beSess_rd`); **no `txRange` for read transactions** (`rdRange`'s hidden split is not `rangeOf`; the
schema never ranges one); `rtSect`, `btSectOut`, `beRet`, `btLockIn`, `btLockOut`, `btUnlock`,
`beForceCommit`, `rtLock`, `rtUnlock`; `bucketAt_ok` (4a's request: `bucketAt ⊢ bucketOk`),
`bktsAre_intro`, `safeRegOk_init`; `applyHook_intro` (the schema's provisional `applyHook` resolved:
from `isBackend`, `beOpen`, `beHook`, 4a's `hookRun` and `Q' ={⊤}=∗ Pk ∗ Q`, the shares back in the
wrapper's post), `alarmBkt_intro`/`_elim`, `memberBkts_intro`/`_elim` (new opaque decodings
`alarmEnts`, `memberEnts` in `schema/Api.lean`).

`schema/` changes: `alarmBkt`, `memberBkts`, `applyHook` take the heap binders explicitly (below);
`txRd`'s `UnsafeForEach` row lets the visitor keep its lent bytes until it gives the view back
(`LentKV`, `lentKVs`: `unsafeGetAllUsers` unmarshals the values after the loop), `J` indexed by the
entries visited; `unsafeUpdateConsistentIndex`'s premise `allow ∨ verifyOff ∨ (txRd ∗ …)`;
`MustUnsafePutLease` takes `c.fits ∧ marshalOk c` (3c's `persistTo` gets it from
`leaseMsg_of_struct`); `MustUnsafeGetAllLeases`' header "some order". Left provisional:
`userName`, `roleName`, `alarmMemberIs` (3h has no such vocabulary yet). `Durable.lean`: the gap
paragraph rewritten (next item). `backend/Api.lean`: `isBackend_agree` added (A's request: the
wrappers hide `γ`).

**Two findings left open:**
1. **The backend's `UnsafeForEach` specs** (`visitOk` and the four `*__UnsafeForEach.lean`) return
   any error with a prefix of the visitor's state, not the visitor's own error, and lend each call's
   bytes for that call only: `SchemaTx`'s `btRd`/`rtRd` `UnsafeForEach` rows are unprovable until
   they return the visitor's error and lend the bytes against a share of `beLive` until the end, as
   `rangeRes` does. (Not done in this round; mvcc does not need it.)
2. **Opaque predicates without their heap binder (branch-wide, the coordinator's).** An `opaque p
   … : IProp GF := iprop(True)` declared under `variable [GooseExts] [GooseSemantics] [GooseInterp]
   … [hG : HeapGS …]` does not take `hG` (Lean includes only the section variables its type and
   body use), so `#check @Backend.beFile` shows no heap: no such predicate can be realized over the
   heap. README's convention causes it in every package (`Mvcc.kbData` too). The fix is to put the
   binders in each opaque's own signature (as A did for the schema's three); `HasExt osFsExt` need
   not be added (a `Prop` class, held inside a realization; `New`'s `beFile` premise carries it), and
   `Durable.beCrash` would then conclude at the crashed generation's heap. This also settles 4a's
   recorded `[HasExt osFsExt]` gap.

Not taken (4a's decision): `batchTxBuffered.UnsafePut`/`UnsafeRange`/`UnsafeForEach` take no
premise that the bucket exists or the key is non-empty (those paths are `lg.Fatal`, which never
returns: 4a's open question 4); the schema's rows supply both anyway. Suggested: index `safeRegOk` by
the declared set (`safeRegOk Bs`).

## What I need from directories I do not own

- **lease (3c), auth (3d), txn (3b), apply, the server (2d)**: for 4a's (g), `Mvcc.hookRun` would
  take the storage (`hookRun B Pk f Pre Q`, lending the session as an `H` with a read law) — an
  arity change in `lease/{Api,Lease__persistTo,lessor__Grant,lessor__Checkpoint}.lean`,
  `auth/{Api,NewAuthStore}.lean`, `etcdserver/txn/Api.lean`,
  `etcdserver/apply/applierV3backend__LeaseGrant.lean`; until then the server's post-lock hook
  (`cindex.go:102-110`) is not provable through mvcc's contract.
- **lease (3c), `Api.lean`**: `beTxHeld be` realized as `∃ B, ⌜be = ok (storageVal B)⌝ ∗
  Mvcc.kbHeld B` (the bridge's lend law then gives the session); the lessor's lease write under mvcc's
  session needs the lease cells untracked (`Backend.beNoVis`, by the server's `beVis_drop`) or
  published by the session (mvcc's publishes `mvccFp` only). `beOk be` (4a's Q5): realize as a
  fractional open share, `Backend.beOpen`, given back before the backend's close.
- **The server (2d/2e)**: `mvccClosed_rest` now takes `mvccBackend γ 1 B Pk` (the whole share; no
  write or commit in flight) and returns `kbOpen B 1`, which the bridge's way back turns into
  `beOpen γ q` for `Close`; `KV.Restore`'s `storageRest` carries the old storage's `kbOpen B 1`.
  3e's open question 2 (key and value size) now also covers the storage's entry bound
  (`kbEntryMax`, the put rows): mvcc's put cannot establish it without a premise or the request
  bound carried down.
- **2b (v3rpc)**: `serverWatchStream__recvLoop` must pass `OtelTrace.ctxSpanOk ctx` (from
  `Tracer.Start`'s post) to `watchStream.Watch`; `watchServer__Watch.lean`'s Changes text
  contradicts the reader-token decision. 2a: a law `rpcCtx ctx md ⊢ TraceUtil.ctxTraceIs ctx none ∗
  OtelTrace.ctxSpanOk ctx` (and for the stream context).
- **2f (`SpecPlan/Spec/net/http/Api.lean`, rafthttp)**: 4b's requests unmet: `readerAt_wrap`,
  `readerCloser_wrap`, a shared reader (`readerShared` with its law and `Read` triple) for the
  snapshot sender's timeout drain, a law for `Probing.urlParses` of rafthttp's probing URLs;
  `semverAt`/`semverParses`/`proberAt` to become `∃ sv, Semver.verAt v sv`, `(Semver.parse
  s).isSome`, `Probing.proberOk`; `addPeerToProber.spec` needs `us ≠ []` and the URLs parsing.
- **3a/3h**: laws from `irrDecodes` to `Proto.encodes`/`irrMsgAt`; **2d/R1**: from
  `decodeConfChange` to `Proto.encodes` (for `MustUnmarshalMessage`); **3h**: `api/version.LessThan`
  over `SemVer.ltb` (harmless); **3d/I5**: `checkKeyInterval.lean`'s adt request is met.
- **4c (bbolt)**: the backend's realization of lent range bytes needs bbolt to read a key it
  returned while writing: `Bucket.Delete`/`Put` take `boltTx tx γ 1 T` and a plain points-to of the
  key, but `txBytes_acc` borrows a fraction of `boltTx` for the key (the compaction's
  `UnsafeDelete(Key, keys[i])`); e.g. let them take a `txBytes` key.
- **2d/2e/3c's provisional backend names** (from 4a's report, unchanged in substance): `beStoredCI`
  /`txStoredCI` over `beVis`/`beCur` of `meta`'s index cells; `Snap.BeImage`/`beFile` are
  `Backend.Image`/`beFile`; `Lease.beHook be Pk f` is `isBackend ∗ beHook γ DFrac.discard f`.

## Build results (directories I own)

- `SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/mvcc` and `.../storage/backend` (with `SchemaTx.lean`):
  OK, 285 modules (`etc/specs-build.sh --dir`, after the last edit).
- With `.../storage/schema`: OK, 355 modules (the final build, after every edit here).
- `SpecPlan/Spec/go_etcd_io/etcd/pkg/v3/adt`: OK (31); 3f's mvcc modules within the mvcc build above.
- `pkg/v3/{traceutil,pbutil,ioutil,httputil}`, semver, `x/time/rate`, probing,
  `otel/{trace,attribute}`: OK (53 modules).
- Snippets: `go vet ./specreq/{mvcc,backend,mvccwatch,adt,pkgleaves}/` clean, `gofmt -l` empty.
- The dependents (`etcdserver`, `txn`, `lease`, `apply`, `auth`, `storage`, `cindex`): failed at
  `etcdserver/apply/checkTxnReqsPermission.lean:48` (`Unknown identifier opsDecoded`), another
  integration's work in progress, not these changes (no file there uses what changed).
