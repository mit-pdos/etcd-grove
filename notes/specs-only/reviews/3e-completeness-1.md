# Review: batch 3e (mvcc's core store), completeness, round 1

Reviewer: completeness (users), independent of the author. Targets: `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/{Model,ApiStorage,Api,Internal*}.lean` and 3e's spec files (not 3f's watch files), the snippets `examples/specreq/mvcc/` (`go vet` clean). Go sources: the pinned fork `server/v3@v3.0.0-20261107170612-a4d2bb1720b9` (`$S` below). I formed the findings below before reading `batch-3e.md`. Where the author's report already names a finding as an open question, I say so.

## The users and their patterns

| # | Pattern | What the users rely on | Real call site checked | Snippet |
|---|---|---|---|---|
| P1 | Boot (`New`/`NewStore`) over a fresh or existing storage | the store starts at the storage's history (rev, crev), an unfinished compaction is resumed, leases are re-attached, the deleter is set | `$S/etcdserver/server.go:366` (after `bootstrap.go:266` created `Meta`); `examples/mvccrand/mvccrand.go:811`; etcd's tests, `kvstore_test.go:566` ("recreate": `Close`, then `NewStore` over the same backend) | `ReqBoot` |
| P2 | Read transactions (`Read`, `Rev`, `FirstRev`, `Range`, `End`), both modes, beside the writer | linearization at begin, a floor, the outcomes of `rangeOut`, owned results | `txn/range.go:53`, `txn.go:43`, `mvccrand.go:625-647` | `ReqReadFloor`, `ReqReadOnlyTxn`, `ReqRangeErrors` |
| P3 | A sole writer pinned to its state (a read, then a write that must begin where the read was) | `tw.Rev()` equals the read's revision, its own writes are visible, `Changes` counts, the revision after `End` | `txn.go:43-63`, `mvccrand.go:466-495` | `ReqSoleWriter`, `ReqDeleteRange` |
| P4 | The post-lock hook runs inside every write's batch lock (the consistent index saved with the write) | `Write`'s post `Q` (the hook has run) | `server.go:409` (hook), `mvccrand.go:363-366` (`checkHook`) | **none** |
| P5 | One-shot views (`kv.Rev`, `kv.Range`, `kv.Put`, `kv.FirstRev`) | as P2/P3, one call | `apply/backend.go:78`, `v3_server.go:429,730`, `api/v3rpc/header.go:35` | `ReqViews` |
| P6 | `Rev()` from a goroutine that holds no store resource, also after `Close` | that the call returns | `api/v3compactor/revision.go:81`, `periodic.go:110` (the compactor is stopped after `be.Close()`, `server.go:957-961`); `header.go:35` through `header.fill` | **none** (and not served: F1) |
| P7 | `Compact` and its channel; `ErrCompacted`/`ErrFutureRev` | the compaction moves `crev`; the errors; a receive on the channel; `ErrCompacted` counts as success | `apply/backend.go:73`, `apply/uber_applier.go:97`, `v3_server.go:403` | `ReqCompact`, `ReqCompactErrors` |
| P8 | Reads beside an unfinished compaction job | a read at or above the compaction succeeds while the job deletes | request path during `scheduleCompaction` | **none** (minor) |
| P9 | `Restore` from a snapshot's storage | the store is at the snapshot's history, no error, the old storage given back, the leases re-attached after `Recover` | `server.go:1087-1098` | `ReqRestore` |
| P10 | `Close`, then closing the storage; a later open of the same storage | every read done, then the storage's rest; on reopen, the data is an image of the last state | `server.go:950-957`, `:376`; 2e's restart; `kvstore_test.go:566` | `ReqClose` (the reopen: **none**, and not served: F5) |
| P11 | `Commit` | no panic; the commit request | `snapshot_merge.go:36`, `server.go:2129` | `ReqCommit` |
| P12 | Hash storage | no panic, beside writes, compactions, restores | `corrupt.go:97,180,193,421,550`, `maintenance.go:233,243`, `server.go:367` | `ReqHash` |
| P13 | Writes with leases (the lessor's writer token) | attach, detach, live lease | `txn/put.go` through `txn.put`; `mvccrand.go:395,430,545` | `ReqPutLease` |
| P14 | The range deleter (`Revoke`, and the server's `Recover` closure) | `rd()` opens a write transaction, `DeleteRange(k, nil)` deletes and detaches, `End` commits | `lease/lessor.go:343-361`, `server.go:1087` | `ReqRangeDeleter` |
| P15 | The watchable store's notify (two-step `End`) | notify, then bump | 3f's `watchableStoreTxnWrite.End` | 3f's |
| P16 | Snapshot image | the storage's data is an image of the state | `snapshot_merge.go:36-37`, through `mvccImage_obs` | none (2d's/4a's) |

## First tier

### F1. `Rev()` needs a reader token, but its token-less callers cannot supply one, and the compactor calls it after the storage is closed (Complete; 2e, 2a). The author lists this as open question 1; I add a second user.

`KV.Rev.contract` (`Api.lean:261-266`) takes `mvccReaders γ 1`, and must: `readView.Rev` is a whole `SharedBufReadTxMode` read transaction (`$S/storage/mvcc/kv_view.go:31-35`), whose `ReadTx().RLock()` takes a storage reader slot in `keyBackend`. Two users cannot supply the token:
- **The compactor** (`api/v3compactor/revision.go:81`, `periodic.go:110`). 2e's `V3compactor.revGetter_intro` (`v3compactor/Api.lean:127-130`) asks for `□ (threadTok -∗ WP rg.Rev() {{ threadTok }})`. `Cleanup` closes the store and then the backend before it stops the compactor (`server.go:950-961`). `mvccClosed_rest` takes every reader token, so a token the compactor still holds blocks the backend's close.
- **The gRPC header**: `header.fill.spec` (`v3rpc/header__fill.lean`) takes the persistent `headerAt` only, and its `rev` closure calls `s.KV().Rev()` (`header.go:35,43`). Either 2a threads a reader token through every handler's header, or `Rev` needs another resource. The author's report misses this user.

Fix: decide open question 1 for both users at once. The author recommends option (a): the server lends the compactor one token for good, and `mvccClosed_rest` takes `mvccTokN - 1`. That needs 4a's close to tolerate one live slot after `Close`. File the header's need with 2a.

### F2. `Compact`'s premise `1 ≤ rev` is stricter than both the code and W0 (No unneeded premise; Complete; 3a)

`KV.Compact.contract` (`Api.lean:347`) takes `⌜1 ≤ sint.Z rev⌝`. The request's revision reaches it unchecked: `apply/backend.go:73` passes `compaction.Revision`, `kvServer.Compact` does not validate it (`v3rpc/key.go:139-144`), and 3a's `IrrOp.ok` admits any compaction (`apply/Api.lean:501-507`).
- W0's client scope is `rev ≠ 0` (`batch-W0.md`, open question 1; `req/..._etcdserver.md:64`), so negative revisions are in scope.
- For those, `updateCompactRev` returns `ErrCompacted` cleanly (`kvstore.go:197-205`: `rev <= compactMainRev`, and `compactMainRev ≥ -1`). That is exactly W0's step (`api/v3/Model.lean:955-962`: `rev ≤ compacted`).
- The only bad input is `Compact(0)` on a store never compacted (`issues/etcd-restore-scheduled-compact-zero.md`).

Fix: `⌜sint.Z rev ≠ 0⌝`, matching W0. Then `ok σ` and the two error arms hold unchanged for negative `rev`. 3a must still carry W0's `rev ≠ 0` into `IrrOp.ok` (3a's concern; noted for integration).

### F3. `Compact`'s channel does not give 3a's `Read.recvAny` (Complete; 3a, 2c)

- **What 3a and 2c need.** `applierV3backend.Compaction.spec`'s post (`apply/applierV3backend__Compaction.lean:48`) is `⌜ch = null⌝ ∨ Read.recvAny ch`, and so is `applierV3Corrupt.Compaction`'s. 2c's `ApiReq.lean:394` carries `recvAny` in the wait registry.
- **What 3e gives.** `KV.Compact.contract` gives `compactChanOk ch` (`Api.lean:200-202`): only a persistent WP of a plain receive.
- **Why one does not imply the other.** `Read.recvAny` (`read/Api.lean:93-95`) needs `isChan ch γc Unit` and a `recvAu`. No law turns `compactChanOk` into either.
- **What the code needs.** The only consumer is a plain receive (`v3_server.go:403`).

Fix (either side): 3a and 2c take `compactChanOk` (it is all `<-result.Physc` needs). Or 3e states its channel as `∃ γc, isChan ch γc Unit ∗ □ ∀ Φ, (∀ v ok, Φ v ok) -∗ recvAu γc Unit Φ`, which `make(chan struct{})` can realize. In that case define it below etcdserver (mvcc cannot import `read/Api.lean`), and let 2c's `recvAny` be that definition. Also align the type of `ch`: 3e uses `GoChan`, 3a uses `Loc`.

### F4. A fresh etcd member cannot establish `NewStore`'s or `New`'s storage premise: `Meta` already exists (Complete; 2e, `server.go:366`)

`mvccStorageFor` (`ApiStorage.lean:606-609`) requires `⌜D = KeyData.empty⌝ ∨ (kbMade both ∗ ⌜D.keyMade ∧ D.metaMade⌝)`, and `mvccImage_empty` is stated only at `KeyData.empty` (`ApiStorage.lean:658`). But on a first boot, `bootstrapBackend` runs `schema.CreateMetaBucket(be.BatchTx())` before `mvcc.New` (`$S/etcdserver/bootstrap.go:266`). So mvcc's part of the storage is `{keyMade := false, metaMade := true, keys := ∅, sched := none, fin := none}`, which is neither disjunct. The tester's fresh backend is empty (`lease.NewLessor` creates only `Lease`, `lessor.go:812`), so `ReqBoot` with a fresh backend hides the problem.

Fix:
- Replace the disjunction with `∀ b, ⌜D.made b = true⌝ → kbMade B b` (as a separating conjunction of the two buckets' cases).
- State `mvccImage_empty` for any made flags: `∀ D, D.keys = (fun _ => none) → D.sched = none → D.fin = none → mvccImage D ⟨[], 0⟩ false`.
- Add a `ReqBoot` variant that creates `Meta` first.

### F5. Shutdown gives no image of the final state: a restart over the same storage has no source for `mvccImage`, and `mvccImage_obs` after `mvccClosed_rest` derives `False` (Complete; Sound as a pair of laws; 2e's restart, etcd's "recreate" test)

- **The image is lost at close.** `mvccClosed_rest` (`Api.lean:600-603`) gives `storageRest B = (∃ D, kbData B D) ∗ …`, with no fact about `D`. 2e's restart (graceful stop, then `NewServer` over the reopened file) and 4a's item 4 (`req/..._backend.md`: "what a later open finds is the last commit's data; mvcc's part of it is an image of the store's history") need `⌜mvccImage D σ.kv u⌝` of the data the backend's close commits. Nothing gives it. Firing `mvccImage_obs` before the close does not help: the compaction job can still change the data until `Close` stops the scheduler (`fifoSched.Stop` waits for the running job).
- **The two laws conflict.** After `mvccClosed_rest` the client holds `kbData B D`, and still holds `isMvcc`, `mvccState γ σ` and every backend share. So it can apply `mvccImage_obs` (`Api.lean:691-695`) and open the resulting `kbObs`, an AU over `∃∃ D, kbData B D`. That gives a second `kbData B`, and `kbData_excl` yields `False`.

Fix:
- Make the shutdown law `mvccClosed γ ∗ mvccReaders γ mvccTokN ∗ mvccBackend γ q B Pk ∗ mvccState γ σ ∗ ⌜σ.pending = []⌝ ={⊤}=∗ (∃ D u, kbData B D ∗ ⌜mvccImage D σ.kv u⌝) ∗ kbSafe B ∗ kbRdToks B mvccReaderN ∗ mvccBackend γ q B Pk ∗ mvccState γ σ`.
- Give `mvccImage_obs` the premise `mvccOpen γ` (framed). The apply thread, which runs both snapshot paths, holds the open token (`server.go:1014`, in `applyAll`; `server.go:2129`).

### F6. `NewStore`'s, `New`'s and `Restore`'s `MvccReachable` premise has no source a caller sees (Every premise has a source; 2d's `applySnapshot`, 2e's boot)

`NewStore.spec` and `New.spec` take `⌜MvccReachable ⟨h, []⟩⌝`, and `KV.Restore.contract` takes `⌜MvccReachable σ' ∧ σ'.pending = []⌝` (`Api.lean:382`).
- **The history is another member's or an earlier run's.** For `Restore` it is the leader's history at the snapshot's index (2d's `imgAt`), and for boot the history the previous run left on disk.
- **No other batch states it.** `MvccReachable` is used by no batch outside mvcc. W0 has no well-formedness of `KVHist` (`api/v3/Model.lean:157-191`). The only law that gives it, `mvccState_reachable`, is about the *local* store.

Fix: put reachability into the image's meaning. Add a law `mvccImage_reachable : mvccImage D h u → MvccReachable ⟨h, []⟩`; `mvccImage_obs` can prove it from `mvccState_reachable`, and `mvccImage_empty` gives it trivially. Then drop the three premises. The pure image fact is what travels with a snapshot or a disk (a cluster-shared fact, PRINCIPLES "A client's certificate is the cluster's").

### F7. The receipts every write's update demands have no supplier (Complete; 3b → 3a → 2d)

The notify step of `KV.Put.contract`, `KV.DeleteRange.contract`, `Txn.End.contract` and `mvccDeleter_rdOk` (`Api.lean:304, 326, 494, 658`) asks the caller's update for `⧖ (evCount (σ.kv.commit pend))`. `Restore` asks for `⧖ (evCount σ'.kv)` (`Api.lean:388`), and `mvccStorageFor` for `⧖ (evCount h)`. No spec outside mvcc mentions `⧖`:
- 2d's report says "no receipt bound (W0's K7 step budget is the cluster's)";
- W0 has `etcdState_revFits`/`sizeFits` as pure laws, not receipts;
- 3b's txn passes its caller's update through.

So the chain 3b → 3a → 2d has no source for the receipt every committed write needs. This is the user-approved shape (mvcc API round 16), but no `req/` asks W0 or 2d for it.

Fix: file the need in W0's and 2d's `req/`: a law giving `⧖ (evCount h)` of the history at a member's applied point, and its growth across one apply. Alternatively, mvcc produces the write's receipt from its own steps (each put or delete is at least one step), and only the `Restore`/boot receipts come from the cluster.

### F8. `Restore`'s post gives back every slot of the old storage while a `HashByRev` may still read it (Sound; author's open question 3). Flagged for the provability reviewer.

`hashByRev` releases `s.mu` before reading the old storage (`$S/storage/mvcc/kvstore.go:188-192`: `tx.RLock(); …; s.mu.RUnlock(); unsafeHashByRev(tx, …)`). So `Restore` can complete under `s.mu.Lock` while that read holds a slot. Yet `KV.Restore.contract` gives `storageRest B` (`Api.lean:390`), that is `kbRdToks B mvccReaderN`: all the slots (`ApiStorage.lean:612-613`).

The author writes that "the specs as written assume" `Restore` gives back all slots but those of hashes in flight. The text does not say that. Then the server's `go oldbe.Close()` (`server.go:1140-1144`) takes slots that are in use. Real users: the corruption checker's goroutine and the maintenance `HashKV` RPC, concurrent with `applySnapshot`.

Fix: state the exception, for example `storageRest`'s slots minus a count the realization hands back later through a closer. Or make the trusted `HashByRev` contract return its storage slot keyed on the storage it read. Related: the trusted `Hash()` reads `s.b` and `s.currentRev` with no lock (`kvstore.go:155-164`), a race recorded in `issues/etcd-mvcc-hash-currentrev-race.md`. That issue is fixed upstream (#22609), but the fix is not in the pinned fork. The trusted `HashStorage.Hash.contract` (`Api.lean:516-520`) should cite the issue as a known gap of the trust base: a data race is a failure in the model.

## Second tier

- **S1. Uncovered patterns (snippets).**
  - P4, the hook runs under every write's lock. The server's consistent-index durability and `mvccrand`'s `checkHook` rely on it. Add a snippet whose `Pre`/`Q` records that the hook ran before `Write` returns (`KV.Write`'s `Q`).
  - P6 (F1).
  - P8, reads during an unfinished compaction job: `ReqCompact` reads only after `<-ch`.
  - P10's reopen (F5).
  - A past-revision read checked against the history at `r`: 2b's `prevKV`, `req` "from 2b" item 5; no snippet asserts the value.
  - A write transaction with no change keeps the revision: txn's `txn()` header (`txn.go:93-97`), `mvccrand`'s `end`.
  - A put that moves a key from one lease to another (`putLs`'s detach-then-attach): `ReqPutLease` covers only lease to none.
  - Receiving on `ErrCompacted`'s channel (`v3_server.go:403` does so for a physical compaction): `ReqCompactErrors` does not receive.
- **S2. 3b's provisional names map onto 3e's, with restatement.** List it in the batch report for the integration pass:
  - `mvccKV` → `isMvcc`; `mvccLessor` → `mvccLessorIs`.
  - `mvccState γ h` → `mvccState γ σ` with `σ.kv = h`.
  - `mvccTxn tx γ k h evs` → `mvccTxn t γ trace (.read σ | .write σ pend)`, with `roWrite` as `.read` at `*txnReadWrite` (`mvccTxn_readOnly`).
  - `mvccWriter γ` → `mvccReaders γ 1 ∗ mvccBackend γ q B Pk ∗ hookIs B f ∗ Pre ∗ hookRun Pk f Pre Q'`, with `Pk` back to `End`.
  - The thread token becomes a reader token.

  The one structural change: every single update of 3b's write specs (`Put.spec`, `DeleteRange.spec`, `Txn.spec`'s write path) must become the nested notify-then-commit pair. A named abbreviation for that pair would keep 3b's, 3a's and `mvccDeleter_rdOk`'s statements short and identical, for example `mvccCommitAU γ σ₀ pend Q`, which `KV.Put`, `KV.DeleteRange`, `Txn.End` and `mvccDeleter_rdOk` spell out four times today. A writer bundle `mvccWriterAt γ q B Pk f Pre Q'` would do the same for the writer's resources.
- **S3. The trace: `traceOwn` (exclusive, 3e) against `traceAt` (persistent, 2c and 3b).** Both are provisional for 4b. The real callers pass `traceutil.EnsureTrace`'s trace: `txn.go:33`, `apply/backend.go:68` (which returns `EtcdServer.traceAt trace` to its caller after `Compact`). Already in `req/..._traceutil.md`; it must be resolved before 3b and 3a can call `Read`, `Write` and `Compact`.
- **S4. `mvccDeleter_rdOk` concludes 3c's `Lease.rdOk`, whose third clause produces `Lease.beTxHeld ls.be`.** mvcc only has `kbHeld B` (`mvccTxn_held`), and mvcc's storage is abstract, so the law cannot be proved for an arbitrary `B` without an identification that only etcd's backend (4a) gives. Make it a premise of the law, `□ (kbHeld B ∗-∗ Lease.beTxHeld (storageVal B))`, which the server discharges, rather than a 4a law mvcc's proof silently needs. (Uncertain whether 4a will state it so that mvcc can use it.)
- **S5. The lessor is 3c's concrete lessor, not a contract** (PRINCIPLES, "An API is stated over the abstractions it builds on"). `NewStore` takes `Lease.isLessor le γl c` and `Lease.lessorIface le`. etcd's own tests (about 50 call sites, `&lease.FakeLessor{}`) and any other `lease.Lessor` are outside the spec. A lessor contract would serve them and the server alike: the triples of `SetRangeDeleter`, `GetLease`, `Attach` and `Detach` on a writer token, which 3c proves for its lessor. Low priority (tests are not verified clients); it is the same choice as the storage's.
- **S6. `Restore(b)` of the store's own storage** (`kvstore_test.go:571`, `watchable_store_test.go:662`) is unprovable: it needs `mvccBackend γ 1 B` and `mvccStorageFor B …` at once. Tests only; note it in the margin.
- **S7. 3f's need 5** (`req/…_mvcc.md`, "from 3f"), a law on what an image holds above its compaction (for `rangeEvents`), is unanswered. `mvccImage` is opaque, with only `mvccImage_empty`, and `rangeEvents.lean:10` relies on its header text. Since both batches are in the same package this is internal, but it should be a law (`mvccImage_entries` over `revEnc`/`kvEnc`) so that 3f's sketch is checkable.
- **S8. Who supplies reader tokens to background goroutines.** The corruption checker's `monitorKVHash` (`HashByRev`) and the maintenance handlers (`Hash`, `HashKV`) hold only `isServer`/`threadTok` in their specs (`EtcdServer__monitorKVHash.lean`, `HandlerTriple`), while 3e's hash contracts take `mvccReaders γ 1`. These goroutines end before `Cleanup` (their wait group), so 2d/2a can stock tokens. Flag it in their `req/` files so the census accounts for them (unlike F1's compactor).
- **S9. 2c's request that the sentinels hold `srvErrVal e` cannot be stated in mvcc** (layering: `etcdserver/errors` is above mvcc). 3e's `init.spec` (`errorString`s with their messages, distinct) is enough for 2c to define `srvErrVal .compacted` as that value. This is served; the redirect is right.

## What is good

- **The model is W0's `KVHist`.** 2d ties the store to `histAt` by equality, and 3b's and 2b's answers need no bridge. `rangeOut` and `rangeResult` match the code's checks exactly: `rangeKeys` uses the live `compactMainRev`, which is stable under `s.mu`'s read side (`kvstore_txn.go:73-83`). They also match the count rules and the keys-only lease `0`.
- **Each canonical spec is one contract instantiated per type** (`KV.*.contract`, `Txn.*.contract`), with the bundles and the `shapes` law. 3f states its watchable instances without restating.
- **The lessor's steps are the code's own** (`putLs`, `delLs`/`delsLs`, `RestoreLs`), on 3c's writer token, and the attachment invariant is the caller's. This serves 3c's items 1-3, 3b's item 4 and `mvccrand`'s `checkLeases`. `mvccDeleter_rdOk` is the right shape for 3c's `Revoke` (modulo S4), and the server's `Recover` closure can prove `mvccDeleter` from `KV.Write` through `shapes`.
- **Boot over any image, with an unfinished compaction resumed** (`u`), and the hook at any share for `NewStore`/`Restore`. This matches the server's order: hook set after `New`, `server.go:409`, and after `Restore`, `:1098`.
- **The two-step commit's read-side subtlety is caught.** `mvccTxn_state` claims `pending = []` only of write transactions.
- **The `Range` contracts' local sort facts (`kvsFit`) serve 3b's `sortRangeResults`.** The error arms carry the exact `RangeResult` values the callers read: `r.Rev` on `ErrFutureRev` (`ReqRangeErrors`), and `rr.Rev` after an ignored error (`apply/backend.go:78`).
- **The snippets compile, each names its users,** and together they cover P1-P3, P5, P7, P9-P14.

## Ranking (by need of revision)

1. **`Api.lean`**: F1, F2, F3, F5 (the shutdown law and `mvccImage_obs`), F6 (`Restore`), F7, F8; S2-S5.
2. **`ApiStorage.lean`**: F4 (`mvccStorageFor`, `mvccImage_empty`), F5 (`storageRest`/image), F6 (`mvccImage_reachable`), S7.
3. **`NewStore.lean`** (and 3f's copies in `New`/`newWatchableStore`): F4, F6.
4. **Snippets** (`examples/specreq/mvcc/`): S1; `ReqBoot`'s fresh case should create `Meta` first (F4).
5. **`Model.lean`**: sound and sufficient for every user I checked; only F6's law touches it.
6. **`Internal*.lean`** and the internal specs: serve 3f's items 1-4 and 6. S7 is the one gap.

## Verdict

Not done: eight first-tier findings.
- **Four are not on the author's list:** F2, F3, F4, F5.
- **Two are hidden obligations without a source:** F6 and F7.
- **Two are the author's open questions, made sharper:** F1 adds the gRPC header as a second user; F8 shows the spec text does not say what the author assumed.

Most fixes are local: relax a premise, change one disjunction, add an image fact to the shutdown law, add one image law. F1, F3 and F7 need decisions across batches (2e/2a, 3a/2c, W0/2d). F1 is already an open question for the user. No new Go bug found; the races F8 relies on are recorded in `issues/`.
