# Integration Y (residual): storage, lease, auth, apply, txn, bbolt

Integration agent Y, 2026-11-09, following `integration-brief.md`, in parallel with X (client,
api/v3, gRPC, the rest of etcdserver, raftpb, net/http). Owned: `storage/{mvcc,backend,schema}`,
`pkg/v3/{adt,traceutil,pbutil,ioutil,httputil}` and 4b's boundaries, `lease`, `auth`,
`etcdserver/{apply,txn}`, `golang_org/x/crypto/bcrypt`, `bbolt`. The items owed between these
directories by I4-I7, one by one.

## (1) `Mvcc.hookRun` names the storage and lends the hook the session (I6's (g))

- `storage/mvcc/ApiStorage.lean`: new opaque **`kbLent B H`** (persistent, `kbLent_persistent`): "`H`
  is the storage's just-begun batch session, lent to its post-lock hook". **`hookRun B Pk f Pre Q`**
  (was `hookRun Pk f Pre Q`): with a hook, `□ ∀ H Φ, kbLent B H -∗ H ∗ Pk ∗ Pre -∗ ▷ (H ∗ Q -∗ Φ #()) -∗
  WP f #()`; with none, the caller's view shift (unchanged). The `LockInsideApply` row cites it.
- Followed through: mvcc (`Api.lean`'s `mvccDeleter`, `KV.Write/Put/DeleteRange/Compact/Restore`,
  `mvccDeleter_rdOk`; `NewStore`, `New`, `newWatchableStore`, `SetScheduledCompact`,
  `SetFinishedCompact`, `store.{updateCompactRev,compactLockfree,restore}`, `writeView.{Put,DeleteRange}`),
  `etcdserver/txn/Api.lean` (`Mvcc.hookRun B Pk f Pre Q'`).
- The lessor no longer cites mvcc's: `lease/Api.lean` has its own **`Lease.beHookRun be Pk f Pre Q`**
  (opaque, one use; realization `∃ γb b p, be = beIface b ∗ isBackend γb b p Pk ∗ ∀ q, Backend.hookRun
  γb q Pk f Pre Q`), cited by `lessor.Grant`, `lessor.Checkpoint`, `Lease.persistTo` in place of
  `Mvcc.hookRun Pk f Pre Q` (the lessor's API is over its backend value, not mvcc's storage). Auth's
  `authHook` and apply's `LeaseGrant` changed in docstrings only.
- `storage/backend/MvccStorage.lean`: `kbLent B H := □ (H -∗ ∃ q S, beSess γ q Fp.none S ∗ (beSess γ q
  Fp.none S -∗ H))` in the realization; `keyBackend_intro`'s post now gives **`□ ∀ f Pre Q, (∀ q, hookRun
  γ q Pk f Pre Q) -∗ Mvcc.hookRun B Pk f Pre Q`** (a hook proved over 4a's contract at every share is
  mvcc's), and `mvccOn γ B` (below).
- **Which hook contract the apply uses** (I5's question): the server proves its hook once, over 4a's
  `Backend.hookRun γ q Pk f Pre Q` at every `q` (its `UnsafeConsistentIndex` reads the shared
  `ReadTx` through `Backend.beSess_rd` of the lent session), and converts: to mvcc's by
  `keyBackend_intro`'s conversion, to the lessor's by `Backend.leaseHookRun_intro`, to the schema's
  (auth's backend wrappers) by `Backend.applyHook_intro`.

## (2) A persistent `Rev` right (I4's request)

`storage/mvcc/Api.lean`:
- **`mvccRevTok γ` is persistent** ("`Rev()`/`FirstRev()` with a thread token, for good"), in
  `persistent.spec`; **`revRd γ true := mvccRevTok γ ∗ threadTok`** (the caller's thread token, given
  back: the bounds plan's thread pool of reader slots).
- New `mvccRevN := 2^28`: the `Rev` pool's lock-only slots; **`mvccReaderN_eq`: `mvccReaderN = mvccTokN
  + mvccOwnN + mvccRevN`**.
- **`mvccRevLent γ (lent : Bool)`** (was `Nat`); `NewStore`/`New`/`newWatchableStore` give `false`;
  **`mvccRevTok_of`: `∀ [ThreadBoundLe GF mvccRevN] γ, mvccRevLent γ false ={⊤}=∗ mvccRevTok γ ∗
  mvccRevLent γ true`** (no reader token consumed).
- **`mvccClosed_rest`**: takes `mvccReaders γ mvccTokN ∗ mvccRevLent γ l` (no `n + m` split), gives
  `kbRdToks B (if l then mvccReaderN - mvccRevN else mvccReaderN)`.
- `ApiStorage.lean`: new law **`kbBareSlot_back`** (`kbBareSlot B ={⊤}=∗ kbRdToks B 1`): the store's
  `Restore` swaps the pool's slots to the new storage under `s.mu` (no `Rev` then).
- `readView__Rev.lean`'s sketch: with the right, the store's realization (`isStore`), a pool slot per
  call. Snippet `examples/specreq/mvcc/store.go` **`ReqRevGetter`** (two goroutines and after `Close`).
- `backend/MvccStorage.lean`: `beReaderN_mvcc`'s text recomputed (`mvccTokN = 2^28` fits under
  `2^30 - 2`).

## (3) G1: the watchable store's sync loops vs the whole restore gate

New **`storage/mvcc/InternalWatched.lean`** (internal; its header is the design):
- The store has two modes, a ghost choice at its allocation: **plain** (`NewStore.spec`, `isMvcc` of
  the `*store` handle, the loop slots stay inside) and **watched** (**`NewStore.watched.spec`**, what
  `newWatchableStore` calls: `storeWatched s γ` (persistent, `storeWatched_isStore`) and
  **`storeLoops s γ mvccLoopN`** (`mvccLoopN = 2`, counted, `storeLoops_split`) in place of `isMvcc`
  of the `*store` handle, which is then never given, so the `*store` instances of the
  `Restore`/`Close` contracts hold vacuously).
- **`store.Restore.watched.spec`**, **`store.Close.watched.spec`**: the contracts' triples at the
  inner store with `storeWatched` and every loop share taken and given back.
- The watchable store parks the shares under its `s.mu` (`wsMu` holds the park's key): a pass borrows
  its loop's share (3f's `wsReadAt`), `watchableStore.Restore` (holding `s.mu`, so no pass runs) hands
  all to `store.Restore.watched`; `watchableStore.Close`, once both loops deposited their
  `wsLoopS`/`wsLoopV` at `Done` (a pass needs them), to `store.Close.watched`. **Restore waits for the
  loops; the loops' slots are outside the gate**; the client still holds `mvccRestoreGate γ 1`.
- Updated sketches/docs: `WatchInternal.lean` (`wsMu`, `wsLoopS`/`wsLoopV`, `wsReadAt`),
  `newWatchableStore`, `New`, `watchableStore__{Restore,Close}` (import `InternalWatched`).
  `New`/`newWatchableStore` are now provable from `NewStore.watched.spec`.

## (4) The backend's `UnsafeForEach`: the visitor's error, the bytes kept (I6's finding)

- `backend/Api.lean`: new `Lent` (key, value, slices, fraction), `lentAll`; **`visitOk vis P E`**: the
  visitor keeps the bytes on success (`P (done ++ [⟨k, v, ks, vs, dq⟩])`), on its error gives them back
  with `E done err`.
- `batchTxBuffered/readTx/concurrentReadTx__UnsafeForEach.lean`: take a share `beLive … pl`; post
  `∃ l full, ⌜order (full.map ent) ∧ l <+: full⌝ ∗ (lentAll l -∗ beLive … pl) ∗ ((err = nil ∧ l = full) ∗
  P l ∨ err ≠ nil ∗ E l err)`: **the visitor's own error**, the bytes lent against the liveness as
  `rangeRes`. Internal `bucketBuffer.ForEach`, `txReadBuffer.ForEach` likewise (the buffer's bytes
  read-only: `dq = discard`, no wand).
- `schema/Api.lean`'s `txRd` `UnsafeForEach` row: a failing visitor call gives its own entry's bytes
  back (`ks ↦*{dq} k ∗ vs ↦*{dq} v ∗ J pre err`): without it the row was unprovable (the backend
  could not return the liveness). `backend/SchemaTx.lean`: `btRd`/`rtRd` sketches now fit; its
  "Needed of 4a (1)" marked met.

## (5) bbolt: reading a returned key while writing (I6's request)

The literal request (let `Bucket.Delete`/`Put` take a `txBytes` key) would not have sufficed:
`txBytes_acc` borrowed **all of `boltTx tx γ q T`**, so with the compaction's keys out the backend
could never present `boltTx … 1`. Instead, `bbolt/Api.lean`: new **`txLive tx p`** (fractional,
`txLive_frac`): the transaction's liveness, separate from its view; **`txBytes_acc` reads against a
share of `txLive`**. `DB.Begin`, `DB.beginTx`, `DB.beginRWTx` give `txLive tx 1`; `Tx.Commit`,
`Tx.Rollback`, `Tx.close` take it (a read-only `Commit`'s error gives it back); `DB.Update`/`View`'s
callbacks get and return it. `Bucket.Delete`'s users note: a key the transaction returned is passed
as a plain points-to read against `txLive`, `boltTx … 1` stays the caller's. The backend's
realization of `beLive γ t p` is then `txLive` of the current bbolt transaction (plus the read
buffer's bytes).

## (6) 3c's `beTxHeld` via the lend law; the lease cells untracked

- `backend/MvccStorage.lean`: new persistent **`mvccOn γ B`** (mvcc's storage over backend `γ`, given
  by `keyBackend_intro`), laws `mvccOn_persistent`, `mvccOn_agree`, `mvccOn_val`, **`mvccOn_held`**
  (the lend law restated over it). The lend now also lends the session's liveness (`beLive γ (btLoc
  γ) 1`, which 4b's `btView` holds): **`ApiStorage.lean`'s `kbLocked_held` takes and gives back
  `kbLive B (kbBatchTx B) 1`** with the lock (a write transaction between calls has no bytes out).
- New **`backend/LeaseBackend.lean`**: `leaseShare := 1/2` (fixed), `leaseBkt`, `leaseFp`,
  `leaseImg C B`; laws `leaseBeOk_intro`/`_elim`, `leaseBeHook_intro`, `leaseHookRun_intro`,
  `leaseBeLeases_intro`/`_elim` (the lease bucket's batch image **with `beNoVis γ leaseFp`**: untracked,
  so `writable` in mvcc's session), **`leaseTxHeld_intro`** (`mvccOn γ B ⊢ □ (kbHeld B ∗-∗ Lease.beTxHeld
  (ok (storageVal B)))`: `mvccDeleter_rdOk`'s premise).
- `lease/Api.lean`: `beOk`, `beLeases`, `beHook`, `beTxHeld` no longer "provisional": the lessor's
  own names over its backend value, their realizations rewritten over 4a's (above).

## (7) I5's other owed items in these directories

- **3e's context error none of mvcc's sentinels**: `rangeResOwn`'s `.ctxErr` now carries
  `context.isCtxErr err` (Perennial's: `Canceled`'s `errorString` "context canceled" or
  `DeadlineExceeded`'s type), from `ctx.Err()`'s spec; with mvcc's `init.spec` (`ErrCompacted`,
  `ErrFutureRev` are `errorString`s of other messages) it is neither (3b's `ctxErr_not_errIs`, 2c's
  `srvIndef`).
- **A record's lease fits `int64`**: `Model.lean`'s `kvSortOk` adds `-2^63 ≤ kv.lease < 2^63`
  (`kvsFit`, hence `rangeResult`).
- **Which `hookRun` the apply uses**: (1).
- **4a's `beOk`/`beHook`/`beLeases` intro laws**: (6).
- **3f's `Contains` at the empty key**: already met (I6: `b = "" → r = false`).

## (8) "Image is the state machine at a point"

New **`backend/StateImage.lean`**: **`Backend.smImage (I : Image) (σ : EtcdModel.State) (ci : Nat) :
Prop`** (transparent): mvcc's part an image of `σ.kv` (`Mvcc.mvccImage (keyDataOf I) σ.kv u`), `meta`
made with `consistent_index` `ci` (`Schema.ciOf`), the lease bucket `σ.leases`' TTLs (`leaseImg`), and
`smRest I σ` (opaque `Prop`: auth's, membership's, alarms' buckets; their owners' decodings are still
provisional or 2e's). **For X**: `beSnap bs γ k := ∃ γb s I bs' σ, … ∗ Backend.beSnap γb s I bs' ∗
histAt γ k σ ∗ ⌜Backend.smImage I σ k⌝`, `dbReader rc γ k := ∃ I σ, Snap.dbReader rc I ∗ histAt γ k σ
∗ ⌜Backend.smImage I σ k⌝` (2e's `Snap.BeImage` := `Backend.Image`); 2e's `beHolds γ img ci` can be
`smImage` of the cluster's state at `ci`.

## Provisional names

Resolved: lease's `beOk`, `beHook`, `beLeases`, `beTxHeld` (now the lessor's own opaque names with
4a's intro laws). Left: `Backend.smRest` (new, auth/membership/alarms decodings); `Auth.authHook`'s
introduction from the server's hook needs a store-level "the store's current backend is `be`" ghost
(the auth store's `as.be` changes at `Recover`), which `authBackendAt`'s realization should expose
(3d's; recorded, not done); schema's `userName`/`roleName`/`alarmMemberIs` (3h, unchanged).

## Sketches checked, not fitting before, fixed here

- The lessor's `Revoke` delete under mvcc's transaction: `btView` (4b's write bundle's view) holds
  `beLive γ (btLoc γ) 1`, which the lend did not give: fixed by `kbLocked_held` lending the liveness.
- `readView.Rev` with the `Rev` right: `KV.Read.contract` needs a reader token; the sketch now goes
  through the store's realization (a pool slot).
- `SchemaTx`'s `UnsafeForEach` rows (4): fixed. The compaction's delete of ranged keys (5): fixed.
- `newWatchableStore`/`New` (3): fixed by the watched instances.

## What X needs (by file and name)

- **`etcdserver/NewServer.lean`, the server's hook** (`getTxPostLockInsideApplyHook`): prove `∀ q,
  Backend.hookRun γ q Pk f Pre Q`; give mvcc `Mvcc.hookRun B Pk f Pre Q` by `keyBackend_intro`'s
  conversion, the lessor `Lease.beHookRun (beIface b) Pk f Pre Q` by `Backend.leaseHookRun_intro`, the
  schema `applyHook` by `Backend.applyHook_intro`.
- **The lessor's backend resources**: `Lease.beOk` by `Backend.leaseBeOk_intro` (split `beOpen γ 1`
  into `Backend.leaseShare` and the rest; back by `_elim` for `Close`), `Lease.beHook` by
  `leaseBeHook_intro`, `Lease.beLeases` by `leaseBeLeases_intro` (the opener's `beCur γ leaseFp C` and
  `beVis_drop` of the lease part to `beNoVis γ leaseFp`), `mvccDeleter_rdOk`'s identification premise
  by `leaseTxHeld_intro` (with `keyBackend_intro`'s `mvccOn γ B`).
- **`api/v3compactor/Api.lean`'s `revGetter`**: take the caller's `threadTok` per call (given back);
  the server realizes it by `mvccRevTok γ` (persistent, `mvccRevTok_of` under `ThreadBoundLe GF
  mvccRevN`, `mvccRevN = 2^28`). `NewServer.lean`'s "gap" paragraph is closed.
- **Shutdown**: `mvccClosed_rest`'s new shape (`mvccReaders γ mvccTokN ∗ mvccRevLent γ l`).
- **`etcdserver/ApiApply.lean`'s `beSnap`/`dbReader`**: definitions over `Backend.smImage` (8).
- **2c/2a**: `rangeResOwn`'s `.ctxErr` now gives `context.isCtxErr err`.

## Build

- All my directories (`.lake/ydirs.txt`: mvcc, backend, schema, adt, traceutil, pbutil, ioutil,
  httputil, semver, rate, probing, otel trace/attribute, lease, auth, apply, txn, bcrypt, bbolt,
  bbolt/errors, bbolt/internal/{common,freelist}) with the dependents `etcdserver`, `v3rpc`, `cindex`,
  `storage`, `v3compactor`, `read`, `snap`, in one `etc/specs-build.sh --dir` run after the last
  edit: **OK, 1308 modules**. (An earlier run failed only in X's `api/v3/etcdserverpb/Api.lean`, then
  under X's edit; it builds now.)
- Snippets: `go vet ./specreq/{adt,apply,auth,backend,bbolt,lease,mvcc,mvccwatch,pkgleaves,schema,txn}/...`
  clean, `gofmt -l` empty (with `bboltinternal`).
