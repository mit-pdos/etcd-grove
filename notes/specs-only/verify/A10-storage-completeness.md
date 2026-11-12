# A10 (storage: mvcc core and watch, adt, backend, schema, pkg leaves): completeness

Reviewer: completeness, verification round 2026-11-09, at `1aa6fc1337`. Batches 3e, 3f, 4a, 4b.
Read-only. I wrote the findings before reading `batch-*.md`, `integration-*.md`, `open-questions.md`
and `reviews/`. Afterwards I read them only to mark which findings are already recorded as open
decisions.

Go sources: the pinned server at `a4d2bb17` (module cache), `examples/mvccrand`, and the snippets in
`examples/specreq/{mvcc,mvccwatch,adt,backend,schema,pkgleaves}`.

Users of the area I checked:
- txn (3b), apply (3a), the lessor (3c), auth (3d), cindex (2d);
- the server: boot, `applySnapshot`, the merged snapshot, `Cleanup`, compaction, quota, the hash
  monitors;
- v3rpc: watch (2b), maintenance, `checkIntervals`, the header;
- the compactor; rafthttp (2f) through ioutil, httputil and pbutil;
- `examples/mvccrand`.

## Verdicts

| batch | verdict |
|---|---|
| **3e** (mvcc core) | **PASS WITH OPEN DECISIONS**: one open decision, A8 (hashing excludes `Restore`). The caller cannot actually discharge it (O1). |
| **3f** (mvcc watch, adt) | **PASS WITH OPEN DECISIONS**: the watch-id restriction (`batch-2b.md`, recorded) and A9 (reader tokens). The tokens are met by 2d's `srvReader_mvcc`; 2b's text about them is stale (S1). |
| **4a** (backend) | **FAIL**: two first-tier findings. F1: `Snapshot`'s post is too weak for the merged snapshot. F2: `keyBackend_intro` does not serve `examples/mvccrand`'s boot. |
| **4b** (schema, pkg leaves, probing/rate/semver) | **PASS WITH OPEN DECISIONS**: open-questions 3.15, `GracefulClose` against the snapshot sender's concurrent `ReadAll`. |

Counts:
- **Spec files whose users I checked: about 417** (mvcc 184, backend 104, schema 70, adt 31,
  traceutil 21, pbutil 3, ioutil 2, httputil 2).
  - I checked every pattern below at one real call site.
  - A script resolved every qualified name that a spec outside the area cites (`Mvcc.*`, `Backend.*`,
    `Schema.*`, `TraceUtil.*`, `IoUtil.*`): 69 distinct names, all exist.
- **Snippets checked against users: 80** (mvcc 18, mvccwatch 15, adt 3, backend 15, schema 11,
  pkgleaves 18). Two user patterns have no snippet:
  - "the snapshot is at least the last commit" (F1);
  - "mvcc over a backend whose `meta` bucket does not exist yet" (F2).
- **User patterns: 32.** 27 close, 2 fail (F1, F2), 3 are open on recorded decisions (A8,
  3.15, the 2b watch id).
- **Callers' specs checked: 18.** These are:
  - 3b `Txn`, `Put`, `DeleteRange`, `Range`, `Count`;
  - 3a `applierV3backend.Compaction`;
  - 2d `applySnapshot`, `createMergedSnapshotMessage`, `monitorKVHash`, `NewServer`;
  - 2b `serverWatchStream.sendLoop`, `recvLoop`;
  - v3rpc `maintenanceServer.{Hash,HashKV,Snapshot}`, `checkIntervals`;
  - 2f `snapshotSender.post`;
  - 3c `lease/Api` (the backend's predicates).

  14 fit. These do not:
  - `createMergedSnapshotMessage` (F1);
  - `applySnapshot` (O1);
  - `snapshotSender.post` (3.15);
  - 2b's `ApiWatch` header, which only needs a text repair (S1).
- **Coverage against `specs-ref`:** every old function spec has a successor. The files with no
  successor:
  - mvcc's `ApiState.lean` and `EtcdBackend.lean` (vocabulary; it moved to `Model`, `Api` and
    `ApiStorage`);
  - adt's `*_bytes` and `*_gen` variants, merged into one spec per function (as PRINCIPLES require);
  - adt's `ownIvt_split`;
  - pbutil's `MustUnmarshalMessagePb`, merged into `MustUnmarshalMessage` over `Proto` content.

## First-tier findings

**F1 (4a). `backend.Snapshot`'s post, "some committed image", is too weak for its main user, the
merged snapshot.** Not recorded.
- **Spec.** `backend__Snapshot.lean:47-53` returns `beSnap γ s I bs ∗ beCommitted γ I`. The only law
  over `beCommitted` is `beHist_mem` (`Api.lean:710`): `I ∈ L`. So `I` may be any image committed so
  far, including one from long before the call. The margin says so: "the post says only 'a
  committed one'".
- **What the code does.** `backend.go:381-386`: `Snapshot` first calls `b.batchTx.Commit()` itself,
  then `db.Begin(false)`. The image is therefore at least the batch image at the call, and at least
  every commit before it.
- **The caller.** `snapshot_merge.go:36-37`: `s.KV().Commit()`, then `dbsnap := s.be.Snapshot()`,
  sent as the image of a snapshot at index `snapi` (the applied index).
  - 2d's sketch (`EtcdServer__createMergedSnapshotMessage.lean:11-12`) needs "`beSnap bs γ c`": the
    image is the state machine at `c ≥ snapi`.
  - The receiver's `applySnapshot` takes the image as `imgAt γ sn.index`, at a point `a ≥ sn.index`.
  - With only `I ∈ L`, an image committed before entry `snapi` was applied satisfies the post, and
    the receiver would install an older state under a newer index.
- **Not fixable by 2d.** 2d cannot close this with an invariant on `beHist`: the history holds
  every old image, and nothing orders `I` within it. 4a's answer to 2d's request item 4
  (`batch-4a.md:119`, "with 2d's invariant on `I`") does not resolve this.
- **Snippet.** `backend/snapshot.go` (`ReqSnapshotStream`) checks only that the stream completes.
  It does not check that the snapshot reflects a write committed before it.
- **Fix.** Give the post a lower bound, for example either:
  - a persistent fragment of the history `beHistLb γ L0` as a premise, and `∃ L1, beCommittedAt γ
    (L0 ++ L1) I ∧ I = last (L0 ++ L1)` as the post; or
  - a `beCurIs`-style observation that `Snapshot`'s own commit hands the client's `commitOk` step.

  Add a snippet that writes a key, calls `ForceCommit`, takes `Snapshot`, and panics if the bytes'
  image (`imgBytes`) lacks the key.

**F2 (4a, affects 3e's `New`/`NewStore`). Nothing serves `examples/mvccrand`'s boot: mvcc over a
fresh backend whose `meta` bucket does not exist.** Not recorded.
- **The user.** `mvccrand.go:809-811`: `be := backend.New(bcfg)`, `lease.NewLessor(…)`, then
  `mvcc.New(lg, be, le, …)`. It never calls `schema.CreateMetaBucket`; `NewStore` creates `meta`
  itself under its lock (`kvstore.go:121-123`).
- **mvcc supports this.** `mvccStorageFor` makes `meta`'s existence conditional
  (`ApiStorage.lean:513-517`: `⌜D.metaMade = true⌝ -∗ kbMade B .metaB`), and `mvccImage_empty`
  allows either.
- **4a does not.** The only law that produces `mvccStorageFor`'s parts for etcd's backend is
  `keyBackend_intro` (`MvccStorage.lean:176-183`). It requires `beMade γ metaBkt`, and
  `keyDataOf` fixes `metaMade := true` (`MvccStorage.lean:110`). So `mvccrand` cannot establish
  `New.spec`'s premise.
- **This verified user lost its spec.** The old tree served it with `etcdStorage_open.law`
  (`specs-ref/Proof/.../mvccrand/RunChecksBackend.lean:15, 232`). PRINCIPLES, "A smaller API is not
  a narrower scope".
- **Snippet.** The area has none for this pattern. `mvcc/boot.go`'s `ReqBootFresh` calls
  `CreateMetaBucket` first.
- **Fix.** Add a `keyBackend_intro` case where `meta`'s existence cell is in mvcc's footprint
  (`mvccFp ∪ Fp.made metaBkt` when `C.made metaBkt = false`), with `keyDataOf`'s `metaMade :=
  V.made metaBkt`. Also add an `mvcc/boot.go` snippet: `backend.New`, then `mvcc.New` with no
  `CreateMetaBucket`, then `Rev() == 1`.

## Open on recorded decisions (count as open, not first-tier)

**O1 (3e, A8). `KV.Restore.contract` takes the whole `mvccRestoreGate γ 1` (`Api.lean:445`), and the
code does not let its caller obtain it.**
- **The decision.** Hashing excludes `Restore` (open-questions A8).
- **Why 2d's sketch does not close.** 2d's `applySnapshot` sketch
  (`EtcdServer__applySnapshot.lean:41-45`) says the apply thread "takes it whole … (a fractional
  census like `srvGate`'s)". But the hashers are not synchronized with the apply thread:
  - `maintenance.go:233, 243`: the RPC handlers' `Hash` and `HashByRev`;
  - `corrupt.go:97`: the corruption checker's `HashByRev`;
  - `monitorKVHash` and `monitorCompactHash`: goroutines.

  Nothing waits for them before `s.kv.Restore`. `srvGate`'s census works because `Stop` does wait,
  so the analogy does not hold.
- **What remains.** As A8 stands, the gate is a scope restriction on the server's run: no hash
  during a snapshot install. That should be stated as one in 2d (or the alternative in A8 adopted).
  Cherry-picking #22609 removes `Hash`'s torn read only, not `hashByRev`'s read of the old storage
  after `s.mu` (`kvstore.go:188-192`, `issues/etcd-mvcc-hashbyrev-restore-rev1.md`).
- The maintenance handlers' sketches (`maintenanceServer__Hash.lean`, `__HashKV.lean`: "any
  outcome") do not say where their `mvccReaders γ 1` and gate share come from. They are trusted
  (`maintenanceServer` is translated names only), so this is a sketch gap only.

**O2 (4b, open-questions 3.15). `GracefulClose.spec` takes the body's `readerAt` owned
(`GracefulClose.lean`).** The snapshot sender calls it from a `time.AfterFunc` goroutine while its
own goroutine runs `io.ReadAll(resp.Body)` on the same body (`snapshot_sender.go:169-170`). 2f's
`snapshotSender.post` sketch says the closure needs only `readerCloser`, which does not meet
`GracefulClose`'s pre. This is recorded (open-questions 3.15, `req/net_http.md` "from 4b").

**O3 (3f, `batch-2b.md`).** `watchStream.Watch.spec` fixes the id argument to `0`. v3rpc passes
`mvcc.WatchID(creq.WatchId)` (`watch.go:342`), which is `0` only for clients in 2b's wire model.
This is a recorded scope restriction (`issues/etcd-watch-id-reuse-stale-events.md`).

## Second-tier

- **S1 (2b text, about 3f).** `v3rpc/ApiWatch.lean:86-91` still says "Open (3f's reader tokens) …
  no law of the member converts a thread token into a reader". 2d's `srvReader_mvcc.spec`
  (`ApiApply.lean:675-678`) is exactly that law, and `integration-I4.md:232-233` counts it as met.
  The sendLoop and recvLoop sketches say "thread token" for mvcc's `Range`, `Rev`, `Watch` and
  `RequestProgress`, which all take `mvccReaders γ 1`. They should cite `srvReader_mvcc` (through
  `isServer_names` → `srvNode`).
- **S2 (3e).** The promoted wrappers `storeTxnRead.{Rev,FirstRev,Range}` and
  `storeTxnWrite.FirstRev` are translated with bodies but have no canonical spec file, unlike
  `batchTxBuffered.UnsafeForEach`. The `Txn.*.contract` at `*storeTxnRead` is what
  `txnReadWrite`'s and `metricsTxnWrite`'s proofs call through the interface. These are internal and
  rest on the `storeTxnCommon__*` files.
- **S3 (4b).** `schema.ReadStorageVersion` (`maintenance.go:141`) and `schema.UnsafeMigrate`
  (`adapters.go:84`, `monitorStorageVersion`) have no schema spec. Both are names only, and their
  callers are trusted, so this is acceptable. The maintenance `Snapshot` sketch cites "4b's
  `schema`" for a spec that does not exist.
- **S4 (4a).** `backend.Snapshot`'s docstring says "the image is the last commit's at the `Begin`".
  The post does not state that (F1); the margin should name what is lost.

## User patterns (summary)

mvcc (3e):
- txn reads (`Read`, `Range`/`Rev`/`FirstRev`, `End`): close.
- txn writes (`Write`, `Put`/`DeleteRange`/`Range`/`Changes`, `End`; `NewReadOnlyTxnWrite`): close.
- apply's `Compaction`: `Compact`, then `Range` at an `EnsureTrace(TODO())` context. Closes:
  `TODO.spec`'s never-done plus `ctxWithValues_done` rule out the `ctxErr` arm, so `rr.Rev` does not
  dereference `nil`.
- headers' `Rev()`: closes through `srvReader_mvcc`.
- the compactor's `RevGetter`: closes (`mvccRevTok_of`).
- the lessor's range deleter: closes (`mvccDeleter_rdOk` with `leaseTxHeld_intro`).
- the server's `mvcc.New` after `CreateMetaBucket`: closes (`keyBackend_intro`).
- `mvccrand`'s `New` with no `meta`: **F2**.
- `Restore`: **O1**.
- `Commit` before the merged snapshot: closes.
- `Close` with `mvccClosed_rest`: closes.
- hashing: **O1**.
- `mvccrand`'s reads, writes and errors (`err == ErrFutureRev`, `== ErrEmptyWatcherRange`): close.

mvcc watch (3f):
- the watch server's stream calls: close, with O3 and S1.
- prevKV's `Range` at `ModRevision - 1`: closes.
- `ReportEventReceived`: closes.

adt: auth's permission trees, `checkIntervals`, the watcher groups: close.

backend (4a):
- the merged snapshot: **F1**.
- maintenance `Snapshot`/`Status`/`Defrag` (trusted): close for the bytes.
- quota's `Size`: closes.
- cindex: closes, over the provisional `beStoredCI` (recorded in I4).
- the lessor: closes (`LeaseBackend.lean`).
- auth through the schema: closes.
- bootstrap's `Defrag`/`Size`/`Close`: close.
- `RecoverSnapshotBackend`'s `ReadConsistentIndex`: closes.
- the post-lock hook: closes.

schema (4b): alarms, membership, auth, leases, the consistent index, `CreateMetaBucket`, the conf
state: all close.

pkg leaves (4b):
- traceutil (request, apply hand-off, read loop, sub-traces): close.
- pbutil (rafthttp codecs, apply, WAL): close.
- ioutil (the pipeline's limited reader, the snapshot body): close.
- httputil: `stream.go`'s `GracefulClose` closes; the snapshot sender's is **O2**.

No new bug in the Go code. `issues/` already records the races behind O1 (`etcd-mvcc-hash-currentrev-race`,
`etcd-mvcc-hashbyrev-restore-rev1`).
