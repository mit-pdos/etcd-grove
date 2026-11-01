# The lock inventory (bounds plan B0, 2026-11-01)

Every Go `sync.RWMutex` whose reader resource reaches a spec or a counted stock, for B2 of
`notes/bounds-plan.md` (reader slots into per-owner thread pools) and its decision D2 (nested read
locks). Taken on `lean` `9722a14372` from `etc/bounds-check.py --kind stock` / `--kind spec-readers`.
Go paths are in the etcd fork (`.lake/go-src/etcd`, `249d76bea7`) unless marked k8s
(`k8s.io/client-go@v0.0.0-20261021054439`, module cache).

**The rule B2 works under** (Perennial `Proof/ThreadPool.lean`, `Proof/sync/RWMutexThreads.lean`
headers): one `threadTok` borrows one pool item at a time. A pool's item may be a bundle (several
locks' slots), so a goroutine that nests read locks of one bundle needs one token. Only nesting
across two pools needs two. Below, "nested" means the latter unless noted.

**gRPC and HTTP handlers get no thread token.** `grpcHandlerOkMd` (`Proof/google_golang_org/grpc/InvGrpc.lean:167`)
gives a unary run its slot `S` and nothing else. `grpc.serve` (`InvGrpc.lean:786`) and
`grpc.serveStream` (`InvGrpcStream.lean:1043`, pool `grpcSlotPool` `:852`) take `n` copies of `S`.
`net/http`'s handlers get `httpProcSlots` copies of `Rs` (`Proof/net/http/Boundary.lean:577`). No
`threadTok` appears under `Spec/`/`Proof/google_golang_org` or `Proof/net`. Goroutines a handler
forks do get one (`wp_fork_tok`): the watch `sendLoop` already takes `threadTok`
(`Spec/.../v3rpc/serverWatchStream__sendLoop.lean:39`). Server methods that already take
`threadTok` (`EtcdServer.LeaseTimeToLive`, `LeaseLeases`, `checkLease*`, `Lease.Remaining`) are
not registered with `grpc.serve`, so B2a is needed for them too.

## 1. RWMutex reader slots

Each entry: resource (definition) — Go lock — owner and where its slots are made — who stocks it —
nesting (Go) — B2 note.

### Server (`etcdserver`)

- **`srvLgReader`** (`Proof/.../etcdserver/InvApplier.lean:312`). `EtcdServer.lgMu`. Made in
  `Proof/.../etcdserver/NewServer.lean:490`; handed out through `srvServeBuilt … 64`
  (`InvServe.lean:113`, `Spec/.../NewServer.lean:268,439,617`). Stocks: `examples/common/Defs.lean:274,361`,
  `Served.lean:102` (`64 - 2`); `client/v3/ServeFromStart.lean:242` (K); `NewServer.lean:1022`
  (`2^23 - 8·|L|`); `SnapRO.lean:344`. 26 Spec files. Also inside `quotaRd`, `etcdIcRs`, `srvSVRes`.
  RLock: `server.go:449` (`Logger`), brief. Nested *inside* `wgMu` (GoAttach, below). B2: pool in
  the server's invariant (`NewServer`); callers are gRPC handlers (B2a), the apply thread and
  GoAttach'ed goroutines (have tokens).
- **`srvLeadTimeReader`** (`InvProposer.lean:480`). `EtcdServer.leadTimeMu`. Made `NewServer.lean:1227`;
  K = 64 in `srvServeBuilt`. Stocks: `examples/common/Defs.lean:273,360`, `Served.lean:101`,
  `InvServe.lean:112`, `ServeFromStart.lean:241`. 8 Spec files; in `etcdRunSlot`, `authSlot`,
  `authnSlot`. RLock `server.go:2387` (`parseProposeCtxErr`), brief, no nesting. B2: server pool;
  gRPC callers only (B2a).
- **`srvBemuReader`** / `srvBemuReaderAt` (`InvApplyAll.lean:113`). `EtcdServer.bemu`. Made
  `NewServer.lean:1240`; 1 + K in `srvServeBuilt`. Stocks: `common/Defs.lean:277,364`, `Served.lean:107`,
  `InvServe.lean:116`, `ServeFromStart.lean:246`. In `quotaRd`, `srvSVRes`. RLock: `server.go:2416`
  (`Backend`), `v3_server.go:411` (`Compact`), `server.go:2223` (`StorageVersion`), `adapters.go:78`,
  `server.go:979` (`Defragment`). **Nested**: `StorageVersion` holds `bemu` while
  `DetectSchemaVersion` read-locks the backend's `readTx.mu` (`storage/schema/schema.go:86`), which
  read-locks `txMu` (`backend/read_tx.go:96`): goroutine `monitorStorageVersion`, a trust-boundary
  spec (`srvSVRes`, `InvStorageVersion.lean:67`, plus a retired backend token). `Compact` and
  `Defragment` hold `bemu` around the backend's `b.mu.RLock` (`backend.go:1087`, `:727`), whose single
  slot the backend keeps internally (not pooled). B2: server pool; the monitor keeps a counted slot.
- **`srvWgReader`** (`InvGoAttach.lean:121`; `srvGoRes` `:125` = it ∗ `threadTok`). `EtcdServer.wgMu`.
  Made `InvStart.lean:377`; `Start` hands out `actualMaxReaders - 2` (`Spec/.../EtcdServer__Start.lean:59,86`,
  `InvStart.lean:304,356`). 1 Spec file. **Nested**: `GoAttach` (`server.go:2436`) calls `Logger()`
  (`lgMu`) at `:2440` under it, and deposits the caller's thread token at `wg.Add` (`:2447`, the
  wait group's bound, `InvGoAttach.lean` header) while it holds the slot. B2: keep counted. One token
  cannot both be lent to the `wgMu` pool and deposited in the wait group (B3).
- **`srvReadReader`** (`InvRead.lean:158`) = `readReader` (`InvRequest.lean:1697`) at `s.read`.
  `read.Read.mux`. Made `Proof/.../read/NewRead.lean:62`; `NewRead` gives `actualMaxReaders`
  (`Spec/.../read/NewRead.lean:44`), `Start` passes them on (`EtcdServer__Start.lean:57,84`).
  Stocks: `common/Defs.lean:268,355`, `Served.lean:105`, `ServeFromStart.lean:245`,
  `etcdserver/Results.lean:2240`, `InvStart.lean:302`. RLock `read/read.go:75`, brief, no nesting.
  B2: pool in the read loop's invariant (`read` package); gRPC callers (B2a).
- **`notifyReader`** (`Proof/.../pkg/v3/notify/Defs.lean:138`). `notify.Notifier.mu`. Made
  `NewNotifier.lean:40`; `NewNotifier` gives `actualMaxReaders` (`Spec/.../notify/NewNotifier.lean:29`);
  `Start` hands `actualMaxReaders - 1` of `s.leaderChanged`'s (`EtcdServer__Start.lean:61`). 5 Spec
  files. RLock `pkg/notify/notify.go:38` (`Receive`), brief, no nesting. B2: pool in `isNotifier`.
- **`raftNode.tickMu`** (`Spec/.../raftNode__getLatestTickTs.lean:28`, raw `ownRWMutex`). Made
  `NodeStart.lean:146`, slots dropped (guard kept); no stock. RLock `raft.go:170`. Out of B2 until a
  caller needs it.

### Auth store (`auth`)

- **`E.RD`** (field of `apply.AEnv`, `Proof/.../etcdserver/apply/Chain.lean:377`; for the real store
  `authRd st R M` = `enabledRd ∗ cacheRd ∗ beRd ∗ R`, `Proof/.../auth/InvAuth.lean:1861`; `R` a
  backend reader the caller lends). `authStore.enabledMu`, `.rangePermCacheMu`, `.beMu`. Made
  `NewAuthStoreOn.lean:348,356,374` (bundled by `slots_rd`, `:153`); `NewAuthStore` (an axiom) gives
  `actualMaxReaders` (`Spec/.../auth/NewAuthStore.lean:105`). Stocks: `common/Defs.lean:275,362`
  (64), `Served.lean:103`, `InvServe.lean:114`, `ServeFromStart.lean:211,243`, `AuthSrv.lean:92`;
  `enabledRd` alone: `auth/Boot.lean:168`, `NewAuthStoreOn.lean:157,229`, `etcdserver/Results.lean:1969,2001`.
  37 Spec files (the most). **Nested, inside the bundle**: `lockedReadTx` (`auth/store.go:941`)
  read-locks the backend's `readTx.mu` (`:945`) under `beMu` (`:942`). `isOpPermitted` (`:882`) holds
  that `readTx.mu` across `UnsafeGetUser` (`txMu`, `read_tx.go:96`) and `isRangeOpPermitted`
  (`rangePermCacheMu`, `range_perm_cache.go:112`). `IsAuthEnabled` (`:950`) is brief. Goroutines:
  gRPC handlers (request path), the apply thread (`apply/auth.go`). B2: one pool of the whole
  `authRd` bundle in the auth store's invariant, so one token pays for it. The trust-boundary
  `NewAuthStore` changes; request-path callers need B2a.

### Lessor (`lease`)

- **`lessorRdOf`** (`Proof/.../lease/InvLessor.lean:742`; `lessorRd` `:682`). `lessor.mu`. No proof
  allocation: `NewLessor` is an axiom and gives `actualMaxReaders` (`Spec/.../lease/NewLessor.lean:118`).
  10 Spec files; the apply thread holds one for good (`lessorUser`, `:747`). RLock `lessor.go:397,459,473,574,646`.
  **Nested** inside mvcc's `store.mu`: `storeTxnWrite.put`/`delete` call `GetLease`
  (`storage/mvcc/kvstore_txn.go:233,335`, under `:175`); `txn.Txn`'s `checkTxn` calls
  `lessor.Lookup` with the read txn open (`etcdserver/txn/txn.go:43` → `put.go:83`); `lessor.Revoke`'s
  `DeleteRange` reaches `GetLease` inside its txn (`lessor.go:343,350`). All on the apply thread.
  Also `revokeExpiredLeases` holds `lessor.mu` while `findExpiredLeases` read-locks each lease's
  `expiryMu` (`lessor.go:646` → `:740` → `lease.go:118`), but that code is not specified. B2: pool in
  `lessorInv`; the apply thread keeps one counted slot (nesting site).
- **`Lease.mu`, `Lease.expiryMu`**: already pooled (`isLeaseObj`, `InvLessor.lean:510`; made
  `LessorLemmas.lean:491`, `lessor__Grant.lean:116`; `Lease.Keys`/`Remaining` take `threadTok`).
  **Nested** inside `store.mu`: `Revoke` calls `l.Keys()` (`lease.go:107`) with its txn open
  (`lessor.go:343` → `:347`). Today the apply thread's `storeReader` is counted, so its token is free
  for this. It stays so if mvcc's pool leaves the apply thread a counted reader.

### mvcc

- **`storeReader` = `storeReaderC`** (`Proof/.../mvcc/InvStore.lean:3983`, `:3972`) = a slot of
  `store.mu` ∗ of `store.revMu` ∗ a ticket of the readers' pool (`ownToks γ.tk 1`). The pool
  (`poolBody`, `:3506`) lends `idxSlot` (`:3460`) = `idxReader` ∗ `storeRT` (a backend reader
  token). Made `NewStore.lean:513` (`revMu`), `:562` (`mu`); index `IdxPriv.lean:89,177`. `NewStore`
  gives `actualMaxReaders - nJobRd kb` (`Spec/.../mvcc/NewStore.lean:121`). Stocks:
  `common/Defs.lean:276,363` (64), `Served.lean:104`, `InvServe.lean:115`, `ServeFromStart.lean:244`,
  `etcdserver/Results.lean:853,1088`, `mvcc/Results.lean:297,369`, `StoreBackend.lean:124`,
  `InvStore.lean:3998`, `NewStore.lean:57`, `NewWatchableLemmas.lean:69`. 28 Spec files (with the
  cache's namesake). **Nested, inside the bundle**: `store.Read` holds `mu` for the txn's life
  (`kvstore_txn.go:47` to `End`) and read-locks `revMu` (`:48`), the backend's `readTx.mu`
  (`ConcurrentReadTx`, `backend/backend.go:302`; or `tx.RLock`, `kvstore_txn.go:60`, in shared mode),
  `txMu` (`read_tx.go:96`) and the index (`index.go:69,83,113,142,163,232`, via `kvindex`,
  `kvstore_txn.go:85,91,108,230,298`). `hashByRev` is the same (`kvstore.go:171`). Outside the bundle:
  `lessor.mu` and `Lease.mu` (above). B2: one mvcc pool of `storeReaderC` (the ticket keeps the index
  and backend slots in the readers' pool); the apply thread keeps a counted reader. Waits for
  `m2-b2-mvcc`.
- **`watchReader`** (`InvWatchStore.lean:1572`) = `storeReader` ∗ a slot of `watchableStore.mu`. Made
  `newWatchableStore.lean:147`; `newWatchableStore`/`mvcc.New` give `actualMaxReaders - nJobRd - 2`
  (`Spec/.../mvcc/New.lean:57`, `newWatchableStore.lean:60`). 14 stock sites in 11 files:
  `common/Defs.lean:304,394`, `Serve.lean:62,138`, `linkv3p/startMember.lean:143` (64);
  `ServeFromStart.lean:141,210`, `ServeFromStartOn.lean:49` (K); `BuildLemmas.lean:131`,
  `M2StorageDraft.lean:128`, `etcdserver/Results.lean:941`, `InvWatchBuilt.lean:62`,
  `NewWatchableLemmas.lean:71`. In `recvRes`/`sendRes`. **Nested, inside the bundle**: `progressIfSync`
  holds `ws.mu` (`watchable_store.go:530`) and calls `s.rev()` → `store.Rev` → `store.Read`
  (`:518`, `kv_view.go:33`): `ws.mu` ⊃ `store.mu` ⊃ `revMu`/`readTx.mu`. `syncWatchers` (`ws.mu`
  writer) holds `revMu` (`:367`) across `rangeEvents`' `readTx.mu` (`:442`), on the store's own
  goroutine, through the pool (`wsDep`). Holders: each watch stream's recv and send loops, for the
  stream's life. B2: an mvcc pool of `watchReader` bundles, carved from the same `mu`/`revMu` supply
  as `storeReaderC`'s.
- **`idxReader`** (`InvIndex.lean:897`), **`idxSlot`**, **`kbRT`/`storeRT`/`bkRTx`** (`InvStore.lean:1668`,
  `:1862`; `BackendBridge.lean:129`, = `backend.rdTok ∗ bOpen rdOpen`). Internal to the readers'
  pool and the backend → mvcc → server hand-off. Stocks: `NewStore.lean:408,429,434`, `RestoreMoves.lean:246-322`,
  `store__Restore.lean:190-278`, `IdxPriv.lean:61-168`, `RestoreNC.lean:56`, `InvStore.lean:3466-3510`;
  `bkRTx`/`kbRT`: `BootBackend.lean:56-91`, `BuildLemmas.lean:109,254`, `SnapApplyOpen.lean:90`,
  `SnapApplyWalk.lean:565`, `etcdserver/Results.lean:841,919,1074`, `mvcc/Results.lean:278,350`,
  `StoreBackend.lean:107`, `M2StorageDraft*.lean`; Specs `NewStore.lean:105`, `New.lean:47`,
  `newWatchableStore.lean:51`, `store__Restore.lean:133,143`, `store__restore.lean:101`,
  `watchableStore__Restore.lean:59,67`. A restore must hand every slot back to close the old backend
  (`k + j + w + r = nReaders`). B2: stays an exact count inside mvcc. These are the owner's own
  bookkeeping, not client stocks; B2 only stops them leaking into `NewStore`/`New`'s posts.

### Backend

- **`rdTok`** (`Proof/.../backend/InvBackend.lean:1027`) = a slot of `readTx.mu` ∗ `crTok` (a slot of
  `baseReadTx.txMu` ∗ a reader budget `ownToks γ.rdt 1`). Made `NewAlloc.lean:561` (`readTx.mu`,
  protocol tokens `newBackend.lean:203`, `sync.rwmutex.ownRLockToken` at `NewAlloc.lean:445`,
  `NewLemmas.lean:81`), `:567` (`txMu`). Stocks: `InvNew.lean:62,167`, `ClientLaws.lean:225,238`,
  `NewAlloc.lean:393`, `BootBackend.lean:56`. **Nested, inside the bundle**: a `readTx` holder
  read-locks `txMu` in `UnsafeRange` (`read_tx.go:130` ⊃ `:96`). Long holds: a `ConcurrentReadTx`
  keeps `txWg` (not a lock) until `RUnlock`. B2: all of it goes to mvcc and auth today (through `bkRTx`).
  A backend pool is not needed until a client outside them read-locks.
- **`b.mu`**, **`safeRangeDeleteMu`** (`srSlot`, `DelKeys.lean:154`): one slot each, kept inside the
  backend (`newBackend.lean:191,197`); no stock. Out of scope.

### Transport (`rafthttp`)

- **`trTok`** (`TransportState.lean:156` = `trReadTok`, `TransportInv.lean:121`). `Transport.mu`.
  Made `TransportState.lean:467`; `Transport.Start` gives `actualMaxReaders`
  (`Spec/.../rafthttp/Transport__Start.lean:61`). Stocks: `TransportState.lean:354,356,399`; inside
  `srvServeRes` (`InvRaftHandler.lean:61` = `τ.c.R ∗ trTok`, `httpProcSlots` = 2^29 copies,
  `Spec/.../NewServer.lean:281,452,630`, `NewServer.lean:1180`, `common/Defs.lean:246`). 6 Spec files.
  RLock `transport.go:171,184,235,250,401,427,435,446`. No reader nesting (`ActiveSince` takes
  `peerStatus.mu`, a `Mutex`). Holders: `Send` (raft node goroutine), each raft HTTP handler's `Get`.
  B2: pool in `trState`; the HTTP handlers need a thread token at the `net/http` boundary (B2a's
  analogue).

### v3rpc

- **`serverWatchStream.mu`** (raw `ownRWMutex`, `v3rpc.swsMu`). Made `watchServer__Watch.lean:125`,
  split between the stream's loops; `sendLoop` takes it with `threadTok`. RLock `watch.go:441,477`, brief, no
  nesting. Per-stream, no stock. Out of scope.
- **`progressReportIntervalMu`**: already pooled (`v3rpc.intervalPool`, `BaseWatch.lean:104-123`,
  made `Init.lean:359`; an early hand-rolled thread pool). B2: switch to Perennial's `threadPool`.

### Cache (`etcd/cache`)

- **`storeReader`** (`Proof/.../cache/v3/InvStore.lean:820`) = `cacheReader` (`InvCache.lean:1380`).
  `cache.store.mu`. Made `newStore.lean:84`; `newStore` gives `actualMaxReaders - 1`
  (`Spec/.../cache/v3/newStore.lean:42`), `New` hands them on (`InvNew.lean:81`). RLock `cache/store.go:75,173`,
  `cache.go:288`. No nesting. `waitTillRevision` holds it across `revCond.Wait` (`cache.go:288-300`;
  the cond's locker is `mu.RLocker()`, so it is released while waiting).
- **`demuxHandle`** (`InvDemux.lean:721`). `demux.mu`. Made `newDemux.lean:105`; Specs
  `NewDemux.lean:41`, `newDemux.lean:38`. In `cacheWatchSlot` (`InvCache.lean:1123` = it ∗
  `cacheWgSlot`, a wait-group deposit; `InvNew.lean:82`). RLock `demux.go:162,184`, no reader nesting.
  Held for life by each `Cache.Watch` goroutine.
- **`notifierHandle`** (`InvNotifier.lean:156`) = `demuxResyncHandle` (`InvDemux.lean:716`).
  `notifier.mu`. Made `newNotifier.lean:38`; Specs `newNotifier.lean:31`, `NewDemux.lean:44`,
  `newDemux.lean:41`, `InvNew.lean:83`. RLock `demux.go:384`, no nesting.
- B2 (all three): pools in the cache's invariants; the cache's callers are client goroutines (have
  tokens); `Cache.Watch` already takes `threadTok`.

### Leasing client

- **`lkvReader`** = `leaseCacheReader` (`InvLeasingKV.lean:229`, `InvLeaseCache.lean:472`).
  `leaseCache.mu`. Made `InvLeasingNewLemmas.lean:208`; `NewKV` gives `leasingMaxReaders`
  (`InvLeasingKV.lean:300,308`, `InvLeasingNewLemmas.lean:205`). 23 Spec files. RLock `leasing/cache.go:45,114,205,232`,
  `kv.go:464,478,492`, `txn.go:74`. No nesting. `Get` takes two (`leasingKV__Get.lean:33`): one goes
  to the `monitorLease` goroutine it forks (`kv.go:342`), which keeps it for life, the case the pool
  is for. B2: the pilot. Callers already hold `threadTok`.

### Kubernetes

- **`tsReader`** (`TSDefs.lean:247`) = `expReader` (`ExpDefs.lean:117`). client-go
  `threadSafeMap.lock`. Made `NewThreadSafeStore.lean:64`; Specs `NewStore.lean:38`,
  `NewThreadSafeStore.lean:40`, `NewControllerExpectations.lean:42`. 35 Spec files. RLock
  `thread_safe_store.go:363-495`, no nesting.
- **`consReader`** (`client_go/util/consistency/Defs.lean:378`). `consistencyStore.writesLock`. Made
  `newConsistencyStore.lean:66`; Specs `NewConsistencyStore.lean:37`, `newConsistencyStore.lean:36`;
  stock `kubernetes/pkg/controller/daemon/Defs.lean:215`. RLock `consistency.go:104`, no nesting
  (`ownerRecord.versionsLock` is a `Mutex`).
- **`procReader`** (`ProcDefs.lean:68`, `sharedProcessor.listenersLock`) and apiserver's
  `watchCache.RWMutex` (`wcLockP`, 5 Specs under `cacher/`): in specs, no constructor verified, no
  stock.
- B2: independent of etcd, low priority.

### Already pooled (no action)

`logkvrw`'s `mu` (`examples/lintest/logkvrw/New.lean:74`, `init_RWMutex_threadPool`), `Lease.mu`,
`Lease.expiryMu`, `progressReportIntervalMu` (own pool).

## 2. Bundles (go away with their parts)

| Bundle | Definition | Parts |
|---|---|---|
| `etcdRunSlot` | `client/v3/Results.lean:829` | `srvLeadTimeReader ∗ storeReader ∗ srvLgReader ∗ srvReadReader ∗ E.RD` |
| `etcdGrpcSlot` | `Results.lean:906` | `(etcdRunSlot ∗ quotaRd) ∗ etcdIcRs` (`:900`: `srvLgReader`) |
| `etcdLeaseSlot` | `Results.lean:3201` | `(S ∗ quotaRd) ∗ etcdIcRs` |
| `v3rpc.quotaRd` | `v3rpc/InvQuota.lean:90` | `srvLgReader ∗ srvBemuReader` |
| `authSlot`, `authnSlot` | `v3rpc/AuthService.lean:49`, `client/v3/AuthnServedOn.lean:76` | lead-time, lg, read readers, `E.RD` |
| `watchRunSlot` | `v3rpc/InvWatch.lean:402` | `recvRes` (`watchReader ∗ E.RD`) ∗ `sendRes` (`watchReader ∗ ⌜threadBound ≤ …⌝`) |
| `srvServeRes` | `etcdserver/InvRaftHandler.lean:61` | `τ.c.R ∗ trTok` |
| `srvSVRes` | `InvStorageVersion.lean:67` | `srvBemuReaderAt ∗ srvLgReader` |
| `srvGoRes` | `InvGoAttach.lean:125` | `srvWgReader ∗ threadTok` |
| `lessorUser` | `lease/InvLessor.lean:747` | `leaseOwn ∗ lessorRdOf ∗ revokers` |
| `cacheWatchSlot` | `cache/v3/InvCache.lean:1123` | `demuxHandle ∗ cacheWgSlot` |

`etcdGrpcSlot` (6 stock sites in 4 files: `client/v3/Results.lean:1958,2899,3324`, `ServedOn.lean:934`,
`AuthnServedOn.lean:255`, `ServeFromStart.lean:247`, plus `client.etcdGrpcSlot` in
`watchkv/Served.lean:85`, `authkv/MainServe.lean:86`, `cache/v3/Results.lean:259`), `etcdLeaseSlot`
(`Results.lean:3276,3450,3480`) and `watchRunSlot` (`v3rpc/Results.lean:1622,1689`,
`ServeFromStart.lean:213`, `watchkv/Served.lean:88`, `authkv/MainServe.lean:139`,
`cache/v3/Results.lean:262`) are the `grpc.serve`/`serveStream` slots. With B2a they become
persistent handles, and `n` and `etcdGrpcSlots_of_started`/`watchRunSlots_of` go.

## 3. Not reader slots (out of B2's scope)

- `ownToks` (Perennial `TokSet`): mvcc's readers'-pool tickets `γ.tk` (`NewStore.lean:56,75`),
  the backend's reader budget `γ.rdt` and write-back budget `wbTok` (`InvBackend.lean:308`), the cache's
  wait-group deposits (`cache/v3/InvNew.lean:192`, `cacheWgSlot`). These are budgets.
- `backend.bOpen` (`InvBackend.lean:279`): a share of "the backend is open" (for `Close`). Stocks
  `InvBackend.lean:1124,1148`, `BootBackend.lean:57`, `SnapApplyOpen.lean:91`.
- `wDep`, `wsDep` (`InvStore.lean:2464`, `:3484`): ghost deposits of the readers' pool.
- `c.R` (rafthttp's per-request handler resource; `Transport__AddPeer.lean:37`,
  `EtcdServer__applySnapshot.lean:139`, `SnapApplyWalk.lean:153,653`, `TransportFull.lean:105`),
  `Rs`/`httpProcSlots` (`net/http/Boundary.lean:186,577`), `sync.join.ownDone`
  (`pipeline__start.lean:85`): boundary or join resources.
- `sync.ownRWMutex`/`sync.rwmutex.ownRLockToken` stocks in owner construction lemmas
  (`NewAlloc.lean:364`, `NewLemmas.lean:83`, `IdxPriv.lean:61`, `NewStore.lean:54`,
  `NewWatchableLemmas.lean:70`, `NewAuthStoreOn.lean:153-156`, `LessorLemmas.lean:451`,
  `TransportState.lean:354`, `BaseWatch.lean:104,123`): the owner's raw slots before packaging. They go
  into `init_RWMutex_threadPool` instead.

## 4. Summary

| Resource | Go lock | Owner (slots made) | Stock files | Nested (cross-pool)? |
|---|---|---|---|---|
| `srvLgReader` | `EtcdServer.lgMu` | etcdserver (`NewServer.lean:490`) | 6 | inner of GoAttach |
| `srvLeadTimeReader` | `EtcdServer.leadTimeMu` | etcdserver (`NewServer.lean:1227`) | 4 | no |
| `srvBemuReader` | `EtcdServer.bemu` | etcdserver (`NewServer.lean:1240`) | 4 | yes: `StorageVersion` |
| `srvWgReader` | `EtcdServer.wgMu` | etcdserver (`InvStart.lean:377`) | 2 | yes: GoAttach |
| `srvReadReader`/`readReader` | `read.Read.mux` | read (`NewRead.lean:62`) | 6 | no |
| `notifyReader` | `notify.Notifier.mu` | notify (`NewNotifier.lean:40`) | 1 | no |
| `E.RD` (`authRd`) | `enabledMu`, `rangePermCacheMu`, `beMu` (+ backend `R`) | auth (`NewAuthStoreOn.lean:348-374`; axiom `NewAuthStore`) | 4 (+5 `enabledRd`) | inside the bundle only |
| `lessorRdOf` | `lessor.mu` | lease (axiom `NewLessor.lean:118`) | 1 | yes: under mvcc `store.mu` |
| `storeReader(C)` | `store.mu`, `revMu` (+ pool ticket) | mvcc (`NewStore.lean:513,562`) | 9 | inside the bundle; outer of lessor/Lease |
| `watchReader` | `watchableStore.mu` + `storeReader` | mvcc (`newWatchableStore.lean:147`) | 11 | inside the bundle |
| `idxReader`/`idxSlot`/`kbRT`/`bkRTx` | `treeIndex`, backend `readTx.mu`+`txMu` | mvcc pool / backend | ~20 | owner-internal |
| `rdTok` | `readTx.mu`, `txMu` | backend (`NewAlloc.lean:561,567`) | 3 | inside the bundle |
| `trTok` | `Transport.mu` | rafthttp (`TransportState.lean:467`) | 1 (+3 `srvServeRes`) | no |
| `cacheReader` | `cache.store.mu` | cache (`newStore.lean:84`) | 1 | no |
| `demuxHandle` | `demux.mu` | cache (`newDemux.lean:105`) | 1 | no |
| `notifierHandle` | `notifier.mu` | cache (`newNotifier.lean:38`) | 2 | no |
| `lkvReader` | `leaseCache.mu` | leasing (`InvLeasingNewLemmas.lean:208`) | 2 | no |
| `tsReader`/`expReader` | `threadSafeMap.lock` | client-go (`NewThreadSafeStore.lean:64`) | 0 (3 Specs) | no |
| `consReader` | `consistencyStore.writesLock` | client-go (`newConsistencyStore.lean:66`) | 1 | no |

That makes 23 reader locks whose slots are stocked: 21 etcd ones (lgMu, leadTimeMu, bemu, wgMu,
read.mux, Notifier.mu, enabledMu, rangePermCacheMu, beMu, lessor.mu, store.mu, revMu, treeIndex,
watchableStore.mu, readTx.mu, txMu, Transport.mu, cache store/demux/notifier, leaseCache.mu) and
two client-go ones. Ten more reach a spec but are already pooled (Lease.mu, expiryMu,
progressReportIntervalMu, logkvrw's mu), owner-internal single slots (sws.mu, tickMu, b.mu,
safeRangeDeleteMu), or unstocked (listenersLock, watchCache).

### Nesting sites (input to D2)

Within one owner's bundle; one token suffices if the pool item is the bundle:

- auth `isOpPermitted`/`lockedReadTx` (`auth/store.go:882,942-945`, `range_perm_cache.go:112`);
- mvcc `store.Read` (`kvstore_txn.go:47-60`, `backend.go:302`, `read_tx.go:96`, `index.go:69…`);
- `progressIfSync` (`watchable_store.go:530` → `kv_view.go:33`);
- backend `readTx` ⊃ `txMu` (`read_tx.go:96,130`).

Across owners; these need two tokens or a counted slot:

1. **Apply thread, mvcc ⊃ lessor**: `kvstore_txn.go:233,335` (under `:175`), `txn/txn.go:43` →
   `txn/put.go:83`, `lessor.go:343` → `:347` (`Lease.mu`) and `:350` (`GetLease`).
2. **Storage-version monitor, `bemu` ⊃ backend `readTx.mu` ⊃ `txMu`**: `server.go:2223` →
   `schema.go:86` (trust-boundary goroutine). `Compact`/`Defragment` nest the backend's internal `b.mu`,
   which is not pooled.
3. **GoAttach, `wgMu` ⊃ `lgMu`**, and the wait-group deposit inside the `wgMu` section:
   `server.go:2436,2440,2447`.
4. Not specified: `lessor.mu` ⊃ `Lease.expiryMu` in `revokeExpiredLeases` (`lessor.go:646` →
   `:740` → `lease.go:118`).

Three specified sites, each on one long-lived server goroutine, so (a) fits D2's recommendation:
the apply thread, the monitor and GoAttach's callers keep a counted slot (one each, or `wgMu`'s
existing stock), and every request goroutine borrows.

### Recommended B2 order

1. **Leasing pilot** (`lkvReader`): no nesting; callers hold `threadTok`; it removes the
   `monitorLease` slot hand-off.
2. **B2a**: a `threadTok` for each gRPC run and stream (`InvGrpc.lean:167,786`,
   `InvGrpcStream.lean:1043`) and each `net/http` handler (`Boundary.lean:577`). Trust-boundary
   change, needs approval. Every later step's request-path callers need it.
3. **Auth `E.RD`**: pool the `authRd` bundle in the auth store's invariant (the `NewAuthStore` axiom
   and `NewAuthStoreOn` change). The apply thread may keep one counted.
4. **Server locks**: `leadTimeMu`, `lgMu`, `read.mux`, `bemu` (monitor keeps a counted slot),
   Notifier, `Transport.mu`. `wgMu` stays counted (site 3, and B3). Then `lessor.mu` (the apply
   thread keeps its `lessorUser` slot, site 1). After `snap-j8a`.
5. **mvcc**: `storeReaderC` and `watchReader` as bundle pools from one `mu`/`revMu` supply; the
   readers' pool and the restore count stay internal; the apply thread keeps a counted reader
   (site 1). After `m2-b2-mvcc`.
6. **Examples' slot plumbing**: `etcdGrpcSlot`/`watchRunSlot`/`etcdLeaseSlot` stocks,
   `etcdGrpcSlots_of_started`, `watchRunSlots_of`, the 64/`64 - 2` splits in `examples/common`.
7. Independent, any time: the cache's three locks, client-go's two, `progressReportIntervalMu`
   moved to `threadPool`.
