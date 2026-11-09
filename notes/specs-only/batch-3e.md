# Batch 3e: mvcc's core (report, before review)

The user-approved mvcc API (`specs-ref/notes/mvcc-api-candidate.md`, frozen 2026-11-03, reopened
through 2026-11-07) restated for the specs-only branch: opaque predicates, W0's history as the
model, the storage an explicit contract, 3c's lessor token threaded.

## Files

`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/` (namespace `Mvcc`; 3f's watch files share the
directory and namespace):

- **Vocabulary**: `Model.lean` (pure: `MvccState`, the steps, `MvccReachable`, `MTxn`, `MRange`,
  `rangeResult`/`rangeOut`, `putRec`/`putEv`, `EvsWf`, `storeItems`), `ApiStorage.lean` (the storage
  contract `keyBackend` and its views, `mvccImage`, `mvccStorageFor`, `storageRest`), `Api.lean`
  (resources, the interfaces' contracts at a receiver, the bundles, the lessor steps, the laws),
  `Internal.lean` (the internal helpers' models and handles; imported by mvcc's own files only).
  Internal additions: `InternalIdx.lean` (the index's logical state `idxAt γi M c` with a compaction
  floor: `treeIndex.Compact` works key by key, so a single `M` is not linearizable; `availAt`, the
  traversal `idxEnts`), `InternalStore.lean` (`storeWB` for `s.mu` held for writing, `revsAt`, the
  scheduler's and restore channels' protocols, the hasher, the schema's globals `schemaVars`),
  `InternalTxn.lean` (`txnCommon`, the change records `changesM`/`changesSl`, `storeTxnWNC`).
  119 files in all (7 vocabulary modules, 112 specs).
- **Client-facing specs** (canonical, per (type, method), each the contract at its type, full
  comments): `NewStore`, `store__{Read,Write,Rev,FirstRev,Range,Put,DeleteRange,Compact,Commit,
  Restore,HashStorage,Close}`, `metricsTxnWrite__{Range,DeleteRange,Put,End,FirstRev,Rev,Changes}`,
  `txnReadWrite__{Range,DeleteRange,Put,End,FirstRev,Rev,Changes}`, `NewReadOnlyTxnWrite`,
  `hashStorage__{Hash,HashByRev,Store,Hashes}` (trusted: names-only), `ReportEventReceived`.
- **Internal specs** (mirror their code, short comments; every panic path excluded by a premise):
  revision.go (`Revision__GreaterThan`, `RevToBytes`, `BytesToRev`, `newBucketKey`, `NewRevBytes`,
  `BucketKeyToBytes`, `BytesToBucketKey`, `isTombstone`, `IsTombstone`); key_index.go
  (`keyIndex__{put,restore,restoreTombstone,tombstone,get,compact,keep,doCompact,isEmpty,
  findGeneration,Less}`, `generation__{isEmpty,isRecreatedAt,walk}`); index.go (`newTreeIndex`,
  `treeIndex__{Put,Get,unsafeGet,KeyIndex,keyIndex,unsafeVisit,Revisions,CountRevisions,Range,
  Tombstone,Compact,Keep,Insert}`); kvstore internals (`store__{compactBarrier,updateCompactRev,
  checkPrevCompactionCompleted,compact,compactLockfree,scheduleCompaction,restore,
  setupMetricsReporter}`, `restoreIntoIndex`, `restoreChunk`); store.go (`UnsafeReadFinishedCompact`,
  `UnsafeReadScheduledCompact`, `SetScheduledCompact`, `UnsafeSetScheduledCompact`,
  `SetFinishedCompact`, `UnsafeSetFinishedCompact`); hash.go (`newKVHasher`,
  `kvHasher__{WriteKeyValue,Hash}`, `NewHashStorage`; trusted); the views (`readView__{FirstRev,Rev,
  Range}`, `writeView__{Put,DeleteRange}`); the transactions' internals (`storeTxnCommon__{FirstRev,
  Rev,Range,rangeKeys}`, `sliceCapWithLimit`, `storeTxnRead__End`, `storeTxnWrite__{Rev,Range,
  DeleteRange,Put,End,put,deleteRange,delete,Changes}`, `newMetricsTxnRead`, `newMetricsTxnWrite`).
  `storeTxnWrite.End` is one spec for both callers: its outer update accepts the state at `σ₀` or
  already notified (`notify` is idempotent), so the plain store passes `Txn.End`'s updates through
  and the watchable store (3f) fires the first itself.
- **Snippets**: `examples/specreq/mvcc/{store,compact,restore,lease,hash}.go` (`go vet` clean):
  `ReqReadFloor`, `ReqSoleWriter`, `ReqDeleteRange`, `ReqReadOnlyTxn`, `ReqRangeErrors`, `ReqViews`,
  `ReqCommit`, `ReqCompact`, `ReqCompactErrors`, `ReqBoot`, `ReqRestore`, `ReqClose`, `ReqPutLease`,
  `ReqRangeDeleter`, `ReqHash`.
- Everything builds (`etc/specs-build.sh --dir Spec/go_etcd_io/etcd/server/v3/storage/mvcc`).

## Exported vocabulary

**Model** (transparent): `MvccState = {kv : EtcdModel.KVHist, pending : List Event}` (W0's history,
so 2d ties it to `histAt` by equality and 3b's answers are W0's functions of it), `rev`, `crev`
(`-1` before any compaction), `notified`, `notify`, `commitPending`, `compactTo`, `mvccStart`,
`MvccReachable`; `MTxn` (`read σ`, `write σ pend`), `readHist`, `txnStore`, `putRec`, `putEv`,
`EvsWf`, `evCount`; `MRange` (mvcc's `(key, end)` with a `nil` end), `rangeKVs`, `rangeKeys`,
`keysOnlyM`, `kvSortOk`/`kvsFit` (the sort's local `2^62`), `rangeResult`, `readAt`, `RangeOut`,
`rangeOut`; `storeItems`.

**Storage contract** (`ApiStorage.lean`): `MvccStorage`, `storageVal`, `kbBatchTx`, `kbReadTx`,
`bucketVal`, `metaKey`, `KeyData`, `bkRange`; opaque `kbData` (visible data, exclusive), `kbLocked`
(batch lock held, the batch's view), `kbRead` (a read snapshot), `kbRdToks` (reader slots,
counted), `kbSafe`/`kbSafeHeld` (the `Key` bucket's delete right), `kbHeld` (lock held, lent to
other users), `kbMade`, `storageHook`/`hookIs`, `storageReq`, `mvccImage` (mvcc's meaning of its
data, pure), `mvccReaderN` (sealed); transparent `hookRun`, `kbObs`, `rangeOk`, **`keyBackend B Pk`
(the contract: 22 method rows)**, `mvccStorageFor`, `storageRest`. Laws: `kbData_timeless`,
`kbData_excl`, `kbLocked_excl`, `kbSafe_excl`, `kbLocked_held`, `kbRdToks_split`,
`kbMade_persistent`, `storageReq_persistent`, `storageReq_true`, `storageHook_fractional`,
`storageHook_agree`, `hookIs_persistent`, `keyBackend_persistent`, `mvccImage_empty`.

**Store** (`Api.lean`): `MvccName`, `mvccN`, `mvccTokN` (sealed), `storeCfgOk`; opaque
`mvccState γ σ` (the client's), `isMvcc kv γ` (persistent), `mvccLessorIs γ γl`, `mvccOpen γ`,
`mvccReaders γ n` (the reader tokens), `mvccClosed γ`, `mvccBackend γ q B Pk` (fractional),
`mvccTxn t γ trace k`, `isHashStorage h γ`, `traceOwn tr` (provisional, 4b's); transparent
`rangeResOwn`, `compactChanOk`, `mvccDeleter`, the lessor steps `putLs`, `delLs`, `delsLs`,
`presentKeys`, `RestoreLs`; the contracts `KV.{Read,Write,Rev,FirstRev,Range,Put,DeleteRange,
Compact,Commit,Restore,HashStorage,Close}.contract`, `Txn.{Rev,FirstRev,Range,Put,DeleteRange,
Changes,End}.contract`, `HashStorage.{HashByRev,Hash,Store,Hashes}.contract`, bundles `isKV`,
`isTxn`, `isHashStorageV`. Laws: `persistent`, `excl`, `init` (the error variables),
`mvccReaders_split`, `mvccClosed_rest`, `mvccStorageFor_rest`, `mvccBackend_agree`,
`mvccLessorIs_agree`, `mvccState_reachable`, `mvccTxn_state`, `mvccTxn_readOnly`, `mvccTxn_held`,
`mvccDeleter_rdOk` (3c's `Lease.rdOk` for the store's deleter), `names_nonempty`, `shapes`,
`mvccImage_obs` (the snapshot's image).

## Main changes from the old (frozen) API

- **The model is W0's `KVHist`** (events with their records) instead of mvcc's own log of changes:
  no bridge between mvcc's history and the cluster's (the frozen API's `srvLog`/`histLb` layer), and
  3b's and 2b's statements are directly in W0's/1b's terms. `pending : List Event` (`[]`: none).
- **The storage is a contract stated in mvcc's terms** (`keyBackend`, the user's 2026-11-06 decision),
  not sealed over etcd's backend (`KBReal`, `bridgeParams`, `isBackend`, `lateW`, ...): what the
  backend must prove is in `req/..._backend.md`.
- **Boot over any image** (`NewStore` takes `mvccStorageFor B Pk h u` for any history `h` and an
  unfinished compaction `u`, with the hook and commit request of a resumed compaction): the old
  `New`/`NewStore` took only an empty backend (a first start).
- **The lessor is 3c's writer token** (`Lease.lessorState γl n ls`), moved by the code's own steps
  (`putLs`, `delsLs`, `RestoreLs`), instead of the old `leaseOwn L I` with the coupling premise
  `pendItems σ.log [] = I`: the attachment invariant is the caller's (3c's request). `Restore`'s
  premise that every restored key's lease is live is dropped (`Attach`'s error is logged: the code
  does not need it).
- **Fractions where Go only reads**: a range's and a range delete's key and end are lent at any
  fraction (the index keeps a put's key and value: those stay read-only).
- **Receipts**: kept where the frozen API had them (a commit's notify step and `Restore`'s give the
  history's receipt, round 16); the client's model bounds (W0's `etcdState_sizeFits`) are the
  cluster's own.
- Kept from the frozen API: the client-owned state, the two-step commit (notify, then bump), the
  reader tokens (no thread tokens), the open token (compactions not concurrent: a marked scope
  restriction), the hook at any share for `Restore`/`NewStore`, `Compact(rev ≥ 1)`, `Close` giving
  nothing back but `mvccClosed` (and `mvccClosed_rest` with every reader token), the `Range`
  contracts' local sort facts (`kvsFit`), the canonical per-(type, method) specs with interface
  bundles.
- New: `HashStorage`'s four methods (trusted, any outcome: the corruption checker and the
  maintenance server need them; no proof uses their values), `mvccTxn_readOnly`, `mvccTxn_held`,
  `mvccDeleter_rdOk`, `mvccImage_obs` (in place of the backend-specific `mvccImage_snapshot`).

## Functions left out

- `store.hash`, `store.hashByRev`, `unsafeHashByRev`: translated names-only; covered by the trusted
  `hashStorage` method contracts.
- `treeIndex.Equal`, `keyIndex.since`, `keyIndex.equal`, `keyIndex.String`, `generation.String`,
  `generation.equal`: no old spec, nothing in the verified code calls them (tests, the watch's
  unused `since`).
- The promoted wrappers `storeTxnRead.{FirstRev,Rev,Range,rangeKeys}`, `storeTxnWrite.{FirstRev,
  rangeKeys}`, `BucketKey.GreaterThan`: covered by `storeTxnCommon`'s/`Revision`'s specs through the
  embedded-field laws (`storeTxnR_common`, `storeTxnW_common`).
- `metrics.go`'s `init` (Prometheus registration): the generated package initializer.
- The watchable store's files are 3f's (`New`, `newWatchableStore`, `watchableStore.*`,
  `watchableStoreTxnWrite.*`, `watchStream.*`, `kvsToEvents`, `rangeEvents`, `ChanBufLen`, ...).

## Callers' needs (`req/go_etcd_io_etcd_server_v3_storage_mvcc.md`): how they are met

- **2b** (watch): items 1-4, 6 are 3f's (`ApiWatch.lean`); item 5 (`Range` at a revision on the
  watchable store) is `KV.Range.contract` at `*watchableStore` (3f states it), with a **reader token**
  (`mvccReaders γ 1`), not a thread token (the user's 2026-11-07 decision: reads take reader tokens).
- **2d**: 1. `Commit` is `KV.Commit.contract` (the commit request `X ∗ storageReq B Pk X Y`). 2.
  `Restore` is `KV.Restore.contract` (`mvccStorageFor B' Pk' σ'.kv u`, no error). 3. The applied
  state: `mvccState γ σ` is the client's; 2d's invariant holds it with `σ.kv = (histAt γ k σc).kv`
  (equality, both W0's `KVHist`). Round 1, item 4 (the read slot): every read's update fires at the
  current state, so the invariant's `σ` at `k' ≥ k` answers it.
- **2e**: 2. `mvccBootCfg cfg` is `storeCfgOk` of the config (`Api.lean`). 3. `Close` gives
  `mvccClosed γ`; with every reader token, `mvccClosed_rest` gives the storage's rest, which the
  backend's close takes. 1. **`revGetter` (`Rev()` from the compactor's goroutine at any time, after
  `Close` too, without a token)**: open, below.
- **3b** (txn): all seven items are met by the contracts (the state is W0's `KVHist`; `Txn.Range`'s
  `rangeOut` with the sort's local facts; `Put`'s record is W0's shape over the pending store;
  `End` fires two updates, the caller passes its one through both; `NewReadOnlyTxnWrite`;
  `mvccState_reachable`/`mvccTxn_state` for the bounds), with two differences 3b must adopt: reads
  and writes take a **reader token** (`mvccReaders γ 1`), not a thread token; a write takes the
  store's storage share and hook (`mvccBackend γ q B Pk ∗ hookIs B f ∗ hookRun ...`) in place of
  `mvccWriter γ`. And a Go fact 3b's checks meet: **a write transaction's `FirstRev()` is `0`**
  (`store.Write` sets none), so `checkRange` in a write transaction fails a negative range revision
  with `ErrCompacted`, which a read-only one does not (W0's `txnRevErr` assumes `-1`); 3b's to model
  or report.
- **3a**: `Compact`, `Range` (no error at the current revision with a context never done) and `Rev`
  are contracts.
- **3c**: items 1-3 met (the writer token threaded; the attachment invariant the caller's;
  `mvccDeleter_rdOk`); what mvcc needs back is in `req/..._lease.md`, "from 3e".
- **2c** (round 1): the sentinels are `errors.New` values (`init.spec`); identifying them with
  `srvErrVal` is 2c's definition.

## `req/` sections written

`go_etcd_io_etcd_server_v3_storage_backend.md` (4a: prove `keyBackend` of etcd's backend; the
hand-over; the snapshot's observation; commits), `..._storage_schema.md` (4b: the bucket values and
key names; `UnsafeCreateMetaBucket`), `..._lease.md` (3c: `isLessor` non-nil; `rdOk`'s call form;
`beTxHeld` = `kbHeld`), `go_etcd_io_etcd_pkg_v3_traceutil.md` (4b: `traceOwn`, `TODO`),
`go_etcd_io_etcd_api_v3_mvccpb.md` (new; 3h: `keyValueOwn` ↔ `Proto.msgAt`, a key-value always
marshals), and the split with 3f in `..._storage_mvcc.md`.

## Open questions for the user

1. **The compactor's `Rev()` without a reader token** (2e's need 1). The compactor's goroutine calls
   `kv.Rev()` at any time, even after `Cleanup` closed the store (its `Stop` only cancels its
   context). Every read of the store takes a reader token (the user's 2026-11-06/07 decision, so
   that shutdown can know no read is in flight: `mvccClosed_rest`). Go: `Rev()` after the backend's
   close touches no closed file (it locks and unlocks the read transaction's mutex), so it does not
   crash. Options: (a) the server lends the compactor one reader token for its lifetime and the
   shutdown law takes all but one (`mvccTokN - 1`); (b) a token-free `Rev` whose spec says only that
   it returns (true of the code, but its proof needs a storage reader slot without a token, i.e. the
   storage contract's `RLock` without `kbRdToks`, which weakens 4a's close); (c) keep the token and
   make the server wait for the compactor's loop before closing (a code change). Recommended (a).
2. **The size of a key and a value** (`req/..._mvccpb.md`, item 2): `proto.Marshal`'s boundary spec
   requires `encSize < 2^48`; mvcc's put marshals the key and value. A workload premise on the store's
   producer (as `reply-size.md`), or the gRPC request bound (2a's `v3rpcBootCfg`) carried down?
3. **`HashByRev` concurrent with `Restore`** (`issues/etcd-mvcc-hashbyrev-restore-rev1.md`): `hashByRev`
   releases `s.mu` before reading the old storage, so a `Restore` can complete and give back the old
   storage's reader slots (`storageRest`) while one is still in use. The hash specs are trusted
   (names-only); their reader token is the store's. Options: `HashByRev` takes a share of the open
   token (cuts the corruption checker off from concurrent restores, the frozen API's decision 10:
   rejected); or `Restore` gives back the old storage's slots but those of hashes in flight (the
   realization tracks them; 4a's close must then wait for them, which etcd's backend close does). The
   specs as written assume the latter.
4. **`ReportEventReceived(n)` takes `n ≥ 0`** (a Prometheus counter's `Add` of a negative panics):
   v3rpc passes `len(...)`. Not a decision, noted for 2b.

## Findings on the way (not decisions)

- No new Go bug. The pinned fork has etcd-io/etcd#22377's fix in `keyIndex.doCompact`
  (`isRecreatedAt`), so `issues/etcd-compaction-delete-then-put.md` (blocks-proof: yes on upstream)
  does not block these specs.
- `compactBarrier`'s `default` branch (re-scheduling on a stopped store) is unreachable: `Stop`
  follows `close(stopc)` in both `Close` and `Restore`; the spec relies on it through the job
  context's `Pay` (`storeStopped`).
- The frozen API's `mvccTxn_state` claimed `pending = []` of every transaction: false for a read
  transaction begun between a watchable store's notify and its bump; now only of write
  transactions.

## Round 1 repairs (reviews `3e-provability-1.md`, `3e-completeness-1.md`)

Coordinator's decisions applied: `Rev()` without a token by option (a); hashing excludes `Restore`.

- **`Rev()` after close** (P-S3, C-F1): a reader token can be turned for good into a `Rev` token
  (`mvccRevTok`, counted by `mvccRevLent`, `mvccRevTok_of`); `KV.Rev`/`KV.FirstRev` take `revRd γ rt`
  (either). Their path only locks the shared read transaction: new storage rows `kbBareSlot`/`kbBare`
  (`RLock`/`RUnlock` with no snapshot, also after the storage's close; `kbRdToks_bare`). The shutdown
  law takes every other token (`n + m = mvccTokN`) and hands back `mvccReaderN - m` slots. Needs filed
  for 2e/2d (the compactor's token, the stock) and 2a (the header fill's token).
- **Hash vs Restore** (P-F5, P-F6, C-F8): `mvccRestoreGate γ q` (fractional): `Restore` takes it whole,
  `Hash`/`HashByRev` a share, so `Restore`'s `storageRest B mvccReaderN` (all old slots) is true; the
  server's obligation filed for 2d; `issues/etcd-mvcc-hash-currentrev-race.md`'s Proof updated
  (cherry-picking #22609 the open alternative; the word-sized `currentRev` read noted).
- **`Compact`** (P-F1, C-F2): premise `rev ≠ 0`; (P-F2) `ch ≠ null` on success and `ErrCompacted`;
  (C-F3) `compactChanOk (ch : Loc)` is `isChan` + `recvAu` (2c's `recvAny` shape).
- **Token counts** (P-F3): `mvccTokMin = 2^28`, `mvccOwnN = 4`; laws `mvccTokN_ge`, `mvccReaderN_eq`;
  the snippets' `Assumes:` name their tokens.
- **The read transaction's range** (P-F4): `rangeOk` takes the range relation; a read transaction's is
  `KeyData.rtRange` (bbolt's part cut at `limit − |buffer part|`, then the buffer's), an empty end
  only as `nil`, `Meta` one key; the `Key` put row requires the key above every key present (so the
  buffer's entries follow bbolt's in key order); `KeyData.clean` (no `Key` entry buffered), cleared by a
  put, given by `mvccStorageFor`: what `restore`'s chunked scan relies on, true there because the
  opened storage has nothing buffered and `NewStore` writes no `Key` entry before it.
- **A fresh member** (C-F4): `mvccStorageFor` asks `kbMade` of the buckets that exist;
  `mvccImage_empty` for any empty data (`KeyData.IsEmpty`); snippet `ReqBootFresh`.
- **Shutdown image** (C-F5): `mvccClosed_rest` takes the state and gives `kbData` at an image of it and
  the receipt; `mvccImage_obs` takes `mvccOpen` (no second `kbData` after shutdown).
- **Reachability** (C-F6): `mvccImage_reachable`; the `MvccReachable` premises of `NewStore` and
  `Restore` dropped.
- **Receipts** (C-F7): removed from the write updates (`KV.Put`, `KV.DeleteRange`, `Txn.End`,
  `mvccDeleter_rdOk`: mvcc handed them out and no one used them); kept where a history travels
  (`mvccStorageFor` takes one; `Restore`'s update, `mvccImage_obs` and the shutdown law give one);
  who supplies boot's filed for 2d/2e.
- Second tier: `mvccImage`'s realization per key a prefix (P-S1); `mvccImage_above.spec` (P-S2, C-S7:
  what an image holds above its compaction, for 3f's `rangeEvents` and `restore`); `mvccDeleter_rdOk`
  takes `□ (kbHeld B ∗-∗ Lease.beTxHeld …)` as a premise (C-S4); `store__Read`'s margin (P-S5);
  snippets `ReqCompactorRev`, `ReqBootFresh`, a receive on `ErrCompacted`'s channel (C-S1, part).
- Not done: C-S2 (a named `mvccCommitAU` abbreviation: PRINCIPLES keep the update in the triple), C-S5
  (a lessor contract instead of 3c's lessor: the frozen API's decision 6), C-S6 (restore of the store's
  own storage: tests only), P-S6 (the receipt bound's provenance is the invariant's, as before).

Open questions 1 and 3 above are settled by these decisions; 2 (key/value size for `Marshal`) stays.

## Round 2 (4a bridge, 4b schema)

- **4a F1, `Unlock` publishes in two steps** (coordinator's decision: two updates). `kbLocked B D0 D`
  carries the session's base `D0`; `Unlock` takes `kbObs`-style nested updates `kbData → KeyData.mid
  D0 D` (the session's puts, at the write-back) then `→ D` (its deletes, at the commit), 4a's
  `Sess.mid`/`Sess.fin`. Sketches re-checked: a read racing a compaction batch may see
  `finishedCompactRev = c` with the batch's deleted entries still there; reads by revision never ask
  for a revision below the compaction (`rangeKeys` reads `revBytes` the index names at
  `≥ compactMainRev`), `checkPrevCompactionCompleted` may answer "completed" before the batch's
  deletes commit (they commit right after, before the job stores the hash), `hashByRev` skips entries
  below its compaction not in `keep`. So `mvccImage`'s realization now admits, for any `u`, removal per
  key a prefix of what the compaction removes (also with the finished key already set): what the
  store's invariant keeps visible, and what `restoreIntoIndex` handles (versions from the first
  surviving entry; a stale entry below the compaction is never read and the next compaction removes
  it).
- **4a F3, the put row's freshness**: the key above every key the session began with (`D0`) or has
  (`D`): 4a's `Sess.fresh`; mvcc's sessions never put and delete `Key` together, so its code meets it.
- **4b, buckets**: `bucketVal` removed; every row takes any `bv` with `Schema.bucketAt b.bkt bv`
  (`MBucket.bkt`); `metaKey` is `Schema.schedKey`/`finKey`; `InternalStore.schemaVars` restated over
  `bucketAt`.
- **4b, `Meta` ranges**: `rangeOk` asks a range of `Meta` only of a compaction key (no claim about
  `Meta`'s other keys).
- **4b, trace**: `Mvcc.traceOwn` is now `TraceUtil.traceOwn` (an abbreviation).
- 4a's items 3, 5, 6 need no change here (`kbHeld` is 4a's session; the snapshot's meaning is attached
  at each commit by the server's invariant through `mvccImage_obs`; `kbBareSlot` is a plain slot).
