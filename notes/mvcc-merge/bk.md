# Track BK: the backend's proofs, the bridge, mvcc's build (the `origin/lean` merge, 2026-11-06)

## Method

Every storage file `lean` changed (outside `mvcc/`) was rebuilt as a 3-way merge of ours, the base
`5eea04e0d6` and **`lean` minus F2** (`lean`'s text with F2's two backend commits, `8ac4492a09`
stage 1 and `2c6e69f0a5` stages 3-4, reverse-merged out). The F2 reversal conflicted in three
files, resolved by hand: `OpenBackend.lean` (docstring: F2's `pvckInit` sentence dropped, R2b-3c's
`bFile` sentence kept), `InvBackend.lean` (`BNames`: `pv`/`ck` dropped, `dbf`/`rq` kept),
`NewAlloc.lean` (allocation: `gpv`/`gck` dropped). The second merge conflicted only in `NewAlloc.lean`
(ours' `fkd`/`dls` allocations with `lean`'s `dbf`/`rq` and `bFile`; `BNames` order `..., gfkv, gdbf,
grq, rbDomOf P D, gfkd, gdls`). Every other storage file came out identical to the coordinator's
auto-merge, so only the F2-touched ones changed.

## The 8 conflicted files (`git add`ed)

- `InvBatch`, `backend__Snapshot`, `batchTxBuffered__{UnsafeCreateBucket,UnsafeDelete,
  UnsafeDeleteBucket,UnsafePut,UnsafeSeqPut}`: ours' proofs (`viewAtD`/`dlsOwn`/`fkdOwn`), `lean`'s
  non-F2 edits kept (none conflicting beyond F2's), F2's `pvPut`/`ckPut`/`pvHalf`/`ckHalf` dropped.
- `NewAlloc`: as above; `New`/`newBackend` specs are `lean`'s minus `pvckInit` (they keep R2b-3c's
  `bFile γ cfg.Path'`); `UnsafeDeleteBucket`'s spec is ours (no `pvPut`).

## Ported (`lean`'s non-F2 work onto ours)

- R2b-3c/3d: `bStopG` (`InvBackend`) now also holds the lock's `fkdOwn γ (fkVals C)` and
  `∃ X, dlsOwn γ X` (from `fkHalf`, in place of F2's `ckHalf`); `bStopView` (`InvStop`) is
  `W ∗ Pk ∗ viewAt ∗ hkOwn ∗ rbOwn ∗ fkdOwn γ (fkVals D) ∗ (∃ X, dlsOwn γ X) ∗ ∃ R, fkRd` (F2's
  `pvHalf` dropped: no counterpart; the `dlVd` agreement of `viewAtD` is not carried to the stop:
  would need the stop commit's `dlsOk`). `unsafeCommit`'s stop path hands them over. `trkHalf` is the
  base's (hook keys + tracked buckets).
- `InvOpen`, `OpenBackend`, `BackendHooks__OnPreCommitUnsafe`: no `pvckInit` left (reverted with F2).
- bbolt-v2, `HooksLoeb`, `TrackedLemmas`, `RdPool` (`authRdN`, `rdAuth`), `commitReq`, `BNames.rq`:
  `lean`'s text, unchanged.

## The bridge (`Spec/.../mvcc/EtcdBackend.lean`) and mvcc

- **API change**: `backendRest` (sealed) and `backendRest_open.law`:
  old `backend.isStopChans γB b ∗ K γB ∗ plHook ∗ rbOwn ∗ rdPool γB P b`,
  new `backend.isStopChansE γB P b ∗ K γB ∗ plHook ∗ rbOwn ∗ rdPool γB P b ∗ backend.rdAuth γB P b`
  (`lean`'s `isStopChans` takes `P W Pk`; `isStopChansE` hides `W Pk`; `rdAuth` is `lean`'s
  `newPostKP`'s new auth share, which goes to the client). `etcdStorage_open.law`'s statement is
  unchanged (its `newPostKP` is `lean`'s). MERGE-TODO(shutdown) on `backendRest`: a client that needs
  `Close`'s `bStopView` at the store's own `W` needs `isStopChans` at it.
- `rdStockN = 536870783`: `mvccReaderN = rdStockN - 6 = 536870777`; `nReaders_val` updated to
  `536870781`; all `threadBound ≤ ...` users still hold (`2 ^ 28`). `Api.lean`'s docstring "about
  `3 · 2 ^ 28`" → "about `2 ^ 29`".
- **errorf-wrap (API change, approved on `lean`)**: `InvStore`'s `rangeOutcome` error disjunct
  `errorfIs err` → `ctxErrorf err` (`lean`'s `ctxErrorf`, `ctxErrorf_ne_nil`, `ctxErrorf_ok` and
  `errorfIs`'s docstring ported). `rangeOutcomeC` is defined through it, so `KV.Range`/`Txn.Range`
  contracts change in meaning (text unchanged). `rangeKeys` takes `fmt.ErrorfWrap.spec` (`lean`'s,
  auto-merged; `Link` passes `fmt.wp_ErrorfWrap`); `ErrorfWrap.wp_proof` is now among mvcc's results'
  axioms (19 of them in the build's `#print axioms`). `scheduleCompaction` calls `lean`'s
  `wp_Errorf_errorfIs` with its new no-`%` premise.
- Auto-merged `lean` text in mvcc taken back to ours (F2): `rangeEvents`, `RestoreCmp`,
  `BackendRecs`, `RestoreImageOpen`, `store__compact`, `M2StorageDraftRestore`, the
  `crevRightM` destruct in `InvWatchStore.noCompactor_of_new` (`lean`'s `isWatchableStore_agree` kept).
- **R-D1 not ported** (MERGE-TODO(shutdown), on the two `Close` specs): `InvWatchSync`,
  `NewWatchableLemmas`, `WsCloserR`, `store__Close`, `watchableStore__Close`,
  `syncVictimsLoop`, `syncWatchersLoop` (its `wsDone` hunk only; the ticker hunk of the Perennial bump
  kept) and the four specs are ours: `lean`'s `wsWgInv st γs ...`/`wsWaiter s st γs` name the readers
  at the store's physical names, which `Restore` changes, and the API's `openRest` holds
  `wsWaiter w` across restores: the risk-1 decision. `wsCloseRes` (in `lean`'s `WsCloserR`) is gone.
  `ReaderRetire.lean` kept, not built (nothing in mvcc imports it).
- Constant inlining: `storeTxnWrite__{put,delete}` (`try simp only [NoLease]`); the others came
  auto-merged.

## Build state

`lake build Proof...mvcc.ApiResults Proof...mvcc.Results Proof...backend.Link`: green. No `sorryAx`
in the 66 + 127 results' `#print axioms`; no `sorry` added. Every storage module (751 targets, all
of `{Proof,Spec}/.../storage/{,backend,schema,mvcc}`, `ReaderRetire` excluded) builds except
`schema/membershipBackend__Must{Delete,Read,Save}Member*` (spec and proof), which reach
`Proof/.../etcdserver/InvRest.lean` (`MvccName.leases`, an error of the server track's).

Interfaces (`interface/**/storage/**`) not regenerated (after the server builds).

## What breaks outside (other tracks)

- `wsCloseRes`, `ReaderRetire`: `etcdserver/StopShutdown`, `NewServer`, `EtcdServer__Cleanup` (proof, spec).
- `bStopView`'s new shape: `StopShutdown`, `StopImage`, `SnapRO`, `EtcdServer__Cleanup` (they unfold it
  for `pvHalf`/`ckHalf`).
- `backendRest`'s new part: `KVStoreApi`, `SnapApplyWalk` (`backendRest_open.law` users: one more conjunct,
  `isStopChansE` in place of `isStopChans γB b`).
- `lateWD` (F2): `SnapApplyOpts{,Lemmas}`, `SnapRO`, `StopShutdown`, `applyConfChange`, `InvRestart`,
  `NewServer`, `SnapApplyWalk`, `BuildLemmas`, ...
- `rangeOutcome`'s `ctxErrorf` disjunct: consumers that eliminated `errorfIs` (txn's `executeRange`/`executeTxn`
  on `lean` already take `ctxErrorf`).
