# Status (Lean port)

**Last updated:** 2026-10-13 (`rp-u4c` (unit 4c) merged into `lean` (unit 6) on branch `merge-u4c`: the apply-thread specs take both `srvGoRes` and the write budget, the write-budget hooks closed (`WB := txn.storeWTs E.γ`, the split `txn.storeWTs_add`, each batch's tokens passed to `applyAll`); gates 187 axioms, 31 sorries, server 141/1, mvcc 35/22, etcd 800 of 3599 functions verified, see "Merge of unit 4c onto the write budget"; `origin/lean` (`1c54ee184`: the backend's unit 6, the write budget and the results over either backend) merged into `lean` on branch `merge-origin4`: the apply thread's specs take both the applied-index ghost and the write budget (`txn.storeWTs`), `applyAll` gains the budget, `server_kv_backend` adapted to unit 5a's `NewStore` (the compaction right frozen, premise `0 ≤ CompactionBatchLimit`); gates 172 axioms, 31 sorries, `server` collection 119 (the union), others unchanged, etcd 794 of 3599 functions verified, see "Merge of `origin/lean` (the backend, unit 6: the write budget)"; the request path's unit 4c on branch `rp-u4c`: the server's goroutines: `run` (the apply loop over the FIFO scheduler, the apply thread's resources chained through saved postconditions, the ready handler, the shutdown), `start` (from the construction premise `isServerBuilt`, named clauses) and `Start` (the read loop and nine names-only monitors through `GoAttach`, proved over Perennial's `WaitGroup`) translated and proved; one `Schedule` axiom with tracked and untracked jobs; `stopping` a capacity-1 channel closed once (`StopChan.lean`); the committed index raised by the ready handler; the backend's write budget carried with a marked hook (not merged); gates 187 axioms (+16, `GoAttach` gone), 31 sorries, server 93/1 (mvcc's pending `schedule.NewJob`), mvcc 35/22, etcd 800 of 3599 functions verified, see "Unit 4c: `run`, `start`, the scheduler and the committed index" under the request path; `lean` (`deccecdff`: the backend's units 1–5 and the request path's 4a/4b) merged into `mvcc` after unit 5a: one backend contract and one store (`isKeyBackendG` with unit 5a's deletable keys, deposit witness, size queries and, under the condition `Cmp`, the compaction-only calls), the bridge extended (snapshots exact, the job's `LockOutsideApply`, `Size`/`SizeInUse` proved of the backend; the deletion from `Key`, the limited range, the `Meta` keys and the safe-range-delete lock not: the backend's model forbids deleting from a safe-range bucket, so `Cmp` is false of it and the compaction's specs take `storeCmp`); gates 172 axioms, 31 sorries (the union), mvcc 34/22, mvcc-compaction 22/22 (+4 bbolt predicates), every other collection unchanged (backend 59/0), etcd 794 of 3599 functions verified, 21 unfinished, see "Merge: lean into mvcc, the backend meets the compaction"; `lean` (`4f2c96322`: the request path's unit 4b, the apply loop and the applied index) merged into `mvcc`: one conflict (this line), no proof changed; gates 118 axioms, 31 sorries, all collections unchanged, see "Merge: lean into mvcc, the request path's unit 4b"; the request path's unit 4b on branch `rp-u4b`: the apply loop and the applied index: `applyAll` translated and proved (under raft's no-snapshot contract), `pkg/wait`'s `wait_time.go` and `pkg/notify`'s `NewNotifier`/`Receive` proved, the read loop's contracts discharged for `*EtcdServer` (`read_server`) and its `raftNode` (`read_raft`, `ReadIndex` and read states in the node contract), the ghost applied index tied to `s.appliedIndex` with a certified log deposited per index at `setAppliedIndex`, so `range_linearizable` says the read's log extends the log applied through an index at least `c`; 4a's `ApplyWait` and notifier clauses adapted; gates 112 axioms (+5: `VerifyBackendConsistency`, `snapshot`, `compactRaftLog`, `createMergedSnapshotMessage`, `sendMergedSnap`), 9 sorries, server 66/0, etcd 720 of 3599 functions verified, see "Unit 4b: the apply loop and the applied index" under the request path; `lean` (`17575d236`: the request path's unit 4a, the read loop) merged into `mvcc` after unit 5a: conflicts only in the baseline (union) and the notes, no proof changed; gates 113 axioms, 31 sorries, all collections unchanged, see "Merge: lean into mvcc, the request path's unit 4a"; mvcc: the store's compaction, unit 5a: the compaction functions translated (with `pkg/schedule`'s jobs), the pure model (`Compact.lean`), the compaction revision's counter and right, the backend contract with deletions, the 21 specs pending (`sorry`); the existing statements are of a store never compacted (`crevFrozen`); 6 new axioms, 22 new sorries (gates 110 axioms, 31 sorries, mvcc 30/22, new collection mvcc-compaction), two findings (`issues/etcd-compaction-*`), see "The store's compaction"; the request path's unit 4a on branch `rp-u4a`: etcd's linearizable read loop (`server/v3/etcdserver/read`) translated with bodies and proved over two contracts (`isReadServer`, `isReadRaft`), `isRead` met by `NewRead`'s result; `isRead` takes a reader slot of `r.mux` (`ReadNames` gains `notifier`), `applyErrIs`' typing clause is for pointer targets; gates 107 axioms (+3: `context.WithTimeoutBackground`, `strconv.FormatUint`, `traceutil.Trace.LogAllStepsIfLong`), 9 sorries, read 12/0, etcd 700 of 3599 functions verified, see "Unit 4a: the read loop" under the request path; `origin/lean` (the backend's unit 5: mvcc's store over the real backend) merged into `lean` (the request path's units 4a/4b) on branch `merge-origin3`: two conflicts (this line; the server collection's baseline, the union), no adaptation needed (the request path's proofs are over `txn.isKV`, which now carries `γ.kb = none`, and never destructure it); gates 166 axioms, 9 sorries, server 66 -> 70, apply 32 -> 36, mvcc 18 -> 22, txn 18 -> 22, v3rpc 46 -> 50 (bbolt's four opaque predicates, which `StoreNames.kb` names), etcd 794 of 3599 functions verified, see "Merge of `origin/lean` (the backend, unit 5)" under the request path; `origin/lean` (the storage backend, units 1–4, and the mvcc bridge) merged into `lean` (the request path's units 4a/4b) on branch `merge-origin2`: no adaptation needed; gates 166 axioms, 9 sorries, collections unchanged (backend 59/0, server 66/0, read 12/0), etcd 794 of 3599 functions verified, see "Merge of `origin/lean` (the backend, units 1–4)" under the request path; unit 6: the txn, apply, server and v3rpc results generic in the backend instance (`txn.isKV` no longer pins `γ.kb = none`): a write token per store write transaction, `txn.storeWTs` one per entry at `applyEntries`; the change bound `2^56` (a delete's range, `TxnPre`); `server_kv_backend` (the apply thread's KV made by `NewStore` over the real backend, on `keySized`); gates 158 axioms, 9 sorries, the `server` collection 114 axioms; see "Unit 6" under the backend; unit 5: mvcc's store over the real backend: the store generic in its backend's instance (`StoreNames.kb`), the late-bound lock resource `lateW`, reader and write tokens, the puts' safe-range condition proved of revision keys, the safe-range discipline in the backend's invariant, an oversized put fatal instead of a premise; `mvcc_NewStore_backend` and `mvcc_store_Write_backend` linked, no `sorry`; the layers above mvcc stay over the assumed backend (`txn.isKV`: `γ.kb = none`); a third reproduction of the cache finding (a range repeats a committed key); gates 158 axioms, 9 sorries, see "Unit 5" under the backend; unit 4, part 2: the backend bridge: mvcc's backend contract generalized (`isKeyBackendG`: reader and session tokens, the puts' condition, the snapshot chosen at `RLock`, `NewStore`'s session) and proved of the real backend (`isKeyBackendG_of_backend`, linked as `mvcc_backend_bridge`, no `sorry`; the range read on the premise `rangeSafe`); schema's `bucket` methods and `Key` translated and proved; mvcc's store not yet over it (five gaps listed); gates unchanged (158 axioms, 9 sorries), see "Unit 4" under the backend; a finding (`etcd-backend-put-value-too-large-fatal`); the backend (`server/v3/storage/backend`) translated with bodies and proved over bbolt as a key-value contract (20 trust-boundary specs): the buffers, the read and batch transactions, the commit, `run`, `Close`, 78 linked results, no `sorry`; the constructor not proved (bbolt's `Options` axiomatized); merged into `lean` with Perennial `a54e1999f` (two proofs adapted: `bucketBuffer.Swap`, Goose's multiple-assignment order; `backend.run`, `Timer.wp_Stop`'s new precondition); gates 158 axioms, 9 sorries, etcd 761 of 3599 functions verified; two findings reproduced, see "The backend"; earlier: `origin/lean` (Perennial `a54e1999f`, its proof layout; the fmt/time/context trust-boundary axioms) merged into `lean` on branch `merge-origin`: no adaptation needed; the `%w` errors of `rangeKeys`/`executeTxn` keep Perennial's model (the axiom cannot give the leaf `applyErrIs` needs without being false of Go), `context.Err` and `context.ErrDone` both kept; gates 104 axioms, 9 sorries, server 61/0, v3rpc 46/0, etcd 691 of 3599 functions verified, see "Merge of `origin/lean` (Perennial `a54e1999f`)" under the request path; `lean` (`a95ad2bb4`: the request path's unit 3b, the read side and `Txn`) merged into `mvcc`: one conflict (this line); their new `specRead` proof of `txn.Txn` takes our `isTxn_toEnd` before `End`, their `v3rpc.txn_end_to_end` loses its four `h_adt_*` hypotheses (the tree's contract is proved); gates 99 axioms, 9 sorries, server 61/0, v3rpc 46/0, etcd 691 of 3599 functions, see "Merge: lean into mvcc, the request path's unit 3b"; adt: unit 4d: `Union` proved over `Visit` and `Insert`; the visitor protocol tells the visitor its position (a third contract correction, for `Insert`'s count bound); no pending spec in any link list, the request path's `checkIntervals`/`Txn` unconditional, see "The watchable store"; `lean` (`fd5d5306e`: the request path `v3rpc` units 0–3a, the raft wrapper, the apply package units 1–3, Perennial `5857c495a`) merged into `mvcc`: the tree's contract reconciled (`InsertAny` gone, our `Insert` is it; `Union` restated at fractions with the count bound, pending for unit 4d; `checkIntervals` adapted, the count bound from a new `delCount` premise), `trace ≠ null` threaded into our write core and `watchableStore.Write`; gates 99 axioms, 9 sorries (the union), adt 0/0, mvcc 18/0, v3rpc 24/0, etcd 674 of 3599 functions, see "Merge: lean into mvcc, the request path"; adt: unit 4c: `Delete` proved with `deleteFixup` (CLRS 13.4's invariant), `min`, `successor`; the hole predicate with its frames' locations (`CtxAt.lean`) for the helpers that walk up through the caller's nodes; the tree's contract fully discharged, no pending spec left, the nine conditional mvcc results now theorems, see "The watchable store", "The whole watchable store"; adt: unit 4b: `Insert` proved with `insertFixup` (CLRS's invariant on a tree with a hole), the rotations, `replaceParent`, `updateMax`, `createIntervalNode`; the watcher budget (ghost tokens: `New` returns `2^63 - 3`, a stream's `Watch` spends one) supplies the tree's count bound; the tree allows equal intervals (the request path inserts the same range twice), see "The watchable store"; adt: the interval tree's proof, unit 4a: the red-black tree's representation (`Tree.lean`, `Defs.lean`: `ownIvt` defined, the `opaque` gone), `ownIvt_split` and the reads proved (`NewIntervalTree`, `Len`, `find`/`Find`, `Intersects`, `visit`/`Visit`/`Stab`); two contract corrections (`Find`/`Stab` lend their pointers; `Stab` needs a proper query), see "The watchable store"; mvcc: the watchable store, unit 3c: the client's receive lemma and the watch-guarantee theorems (`wp_watch_receive`, `watchRecvOk_cert`, `watchGuarantee_unfiltered`, `watchRecvOk_revs`: no `sorry`, no trust-boundary axiom of the package), the watchable store complete but `Restore` and the tree's proof (unit 4), see "The watchable store"; mvcc: the watchable store, unit 3b: the sync machinery and the constructors proved (`syncWatchers`, `moveVictims`, the two loops, `rangeEvents`/`kvsToEvents` over the backend's range read, `New`/`newWatchableStore`/`Close`/`NewWatchStream`); tickers, `time.Since` and `store.Close` axioms; a finding: `syncWatchersLoop` resets its ticker with a zero duration on a coarse clock (`issues/etcd-watch-sync-ticker-reset-zero.md`), see "The watchable store"; `lean` merged into `mvcc` (the apply package, units 0 and A; the batch lock runs the post-lock hook: `storeTxnWriteCore` carries `hookIs`, the watchable `Write`/`End` take the hook's resources as the inner ones), see "Merge: lean into mvcc, the hook (2026-10-12)"; mvcc: the watchable store, unit 3a: the write path proved (`Write`, the wrapper's `End` sealing the revision in the history before `notify`, `notify`, `addVictim`, `watch`, `cancelWatcher`, `send`, `rev`, the progress calls) over the lock invariant and the channel protocol; the history carries the change; the tree contract at a fraction (`ownIvt_split` pending); `storeTxnWriteIs` split; `verify.Verify` axiom, see "The watchable store"; the request path's unit 3b on branch `rp-u3b`: the read side and `Txn`: `EtcdServer.Range`, `Txn` (both branches), `doSerialize`, `newHeader`, the getters and `tracing.go`'s loops verified and linked, `txn.Txn` at a reader (`specRead`), the response headers owned for the reads and `Txn`, the read side's context error through Perennial's `fmt.Errorf` (no `%w`) with an `errorString` leaf premise, the server's contract `raftKV` discharged with no premise but `isServerReq`/`isServerRead` (`range_end_to_end`, `txn_end_to_end`, `range_linearizable`, `txn_applied`, ...), gates 94 axioms, 9 sorries, server 61/0, v3rpc 46/0, etcd 639 of 3599 functions verified, see "Unit 3b" under the request path; Perennial `a54e1999f` pinned (its proof layout; not its current `lean`, whose panic model cannot verify the STM: the port so far on branch `perennial-d0324-wip`); five new trust-boundary axioms for fmt, `time.Duration.String` and `context.Err`, seven strengthened assumptions, every one listed; gates 98 axioms, 9 sorries, see "Perennial `a54e1999f`: the proof layout"; the request path's unit 3a on branch `rp-u3a`: the gRPC `Put`/`DeleteRange` end to end (`put_end_to_end`, `deleteRange_end_to_end`: the handler's `(resp, nil)` is the apply thread's application at the log the entry met, the header filled), the server's contract `raftKV` split per method and discharged for `Put`/`DeleteRange` (`ServerKV.lean`), the response header's id fields owned from the txn package to the handler, `applyErrIs` with the gRPC facts, one new axiom (`context.ErrDone`), gates 94 axioms, 9 sorries, server 48/0, v3rpc 23/0, etcd 625 of 3599 functions verified, see "Unit 3a" under the request path; `origin/lean` merged into `lean` (the raft wrapper, build performance, the iframe race): the Goose configurations' union regenerated, `srvInit` the raft wrapper's and the request path's facts, gates 93 axioms, 9 sorries, server 47/0, server-raft 6/0, etcd 625 of 3599 functions verified, see "Merge of `origin/lean`" under the request path; the request path's units 1 and 2 merged into `lean` (notes and baseline conflicts only; `NewKVServer`'s `TypeRepr` of `EtcdServer` reached the axiomatized fields' `sorry` instances after the merge, fixed by an import; both `errors.Is` axioms kept; gates 91 axioms, 9 sorries, server 44/0, v3rpc 3/0, etcd 615 of 3599 functions verified), see "Merge 1/2"; the request path's unit 1 on branch `rp-u1`: every function of `key.go` but `RangeStream`/`Compact`, `header.go` and `togRPCError` specified and proved over the server's contract `raftKV s A` (parameters units 2/3 instantiate), `check_gives_nodup` (with the key check: unit 0's statement was false), `checkRequestOp_nonempty`; `api.Cluster`, `etcdserverpb.KVServer`/`RangeStreamResponse` translated; one new axiom (`errors.IsDeadlineExceeded`); adt's `InsertAny` (pending); gates 89 axioms, 9 sorries, v3rpc 3/0, etcd 592 of 3599 functions verified; see "Unit 1: the checks and the handlers"; the request path's unit 2 on branch `rp-u2`: `pkg/wait` and `pkg/idutil` verified, the proposal path (`processInternalRaftRequestOnce`, `raftRequest`, `Put`, `DeleteRange`) verified over the raft contract and the wait registry, the apply thread triggering the registry (`waitInv`); results `request_handoff`, `put_applied`, `deleteRange_applied`; 2 new axioms (90), 9 sorries, server 44, etcd 600 of 3599; `Txn` left to unit 3; see "Unit 2: the wait protocol and the proposal path"; the request path's unit 0 on branch `rp-u0`: `v3rpc`'s KV service, the server's request path, `pkg/wait` and `pkg/idutil` translated; the checks as pure functions (`v3rpc/Defs.lean`), the raft contract, the id generator, the wait registry and the read contract (`InvRequest.lean`); 22 new axioms, gates 88 axioms, 9 sorries, server 40/0, v3rpc 2/0; three findings (`checkIntervals` misses a later sibling's delete, `--max-txn-ops` is per level, request ids of two members collide when their ids agree in the low 16 bits), see "The request path"; the server's raft wrapper proved: `raftNode.start` and every method of raft.go, linked, gates 68 axioms, 9 sorries, server 22/0, server-raft 6/0, etcd 587 of 3599; see "etcd's server: the raft wrapper"; build performance on branch `proof-perf`: three proofs verify a common tail once (`wp_join`), `raftOwn_access` frames by name, the Results modules print axioms with full names, Perennial `afc8f0432` (not yet pinned) gives the WP tactics per-thread caches without a lookup per access, see "Build performance"; the intermittent failure of `InvSTMRun.lean` (`stmMethods_ser`) in loaded full builds was a race in Perennial's `iframe` (a global flag shared by declarations elaborated in parallel), fixed in Perennial `fb1ecb030` (in `5857c495a`); the proof unfolds `STMSt.empty` and no longer needs `iframe`'s prepass, see "Parallel elaboration and tactic state"; the apply package's unit 3 on branch `apply-u3`: the server bridge: the apply thread on the proved `apply.Apply` (`applierFor`, `applierFor_persistent`, `apply.Apply_server.wp_proof` gone; `isServer s γ ci TM E`, `srvApplyKV`), the KV threaded through `applyEntryNormal`/`apply`/`applyEntries` (`entryOk`/`entryStep`, `entriesOk`/`entriesStep`), the server's `Results.lean` (`applyEntries_model`, `_kv`, `_replay_no_write`, `_rejected_no_write`); gates 66 axioms, 9 sorries, server 19/0, apply 32/0, apply 71 of 73, etcd 577 of 3599; see "Unit 3: the server bridge" and "The whole package" in the apply section; the apply package's unit 2 merged into `lean`: `uber_applier.go` and `apply.go` specified and proved, `apply.Apply.spec` with the KV (`applyKV`, `applyStep`), the server still on its assumed contract (`apply.Apply_server`, unit 3); the `applyErrIs` gap closed (the contracts' errors and `applyErrVars` the two assumptions; `txn.Range`/`DeleteRange` take `nd`); gates 69 axioms, 9 sorries, apply 32/0, server 18/0, apply 71 of 73 functions verified, etcd 577 of 3599, see "Merge 2" in the apply section; Perennial `5857c495a` pinned: soundness fixes (unsigned `uint32` division, division by zero panics, shift counts not truncated, `^x`; `time.isTimer` unforgeable; `errors.wp_As` requires an interface or `error` target), the ring buffer's three divisions and `leasingKV.acquire`'s `errors.As` repaired, gates unchanged (69 axioms, 9 sorries), see "Perennial `5857c495a`: soundness fixes"; `origin/lean`'s eight small etcd axioms merged into `lean` (`MustUnmarshalMessage` a case per message type, each with its decoding premise; `store.Write` takes the non-nil trace and the hook; gates 69 axioms, 10 sorries, apply 31/0, server 18/0, mvcc 12/0, txn 18/0, etcd 568 of 3599 functions verified), see "Merges of `origin/lean`" in the apply section and "Small etcd axioms"; the apply package's unit 1 on branch `apply-u1`: every function of `backend.go` (but `Compaction`), `quota.go`, `capped.go`, `corrupt.go`, `auth.go` specified and proved, the constructors packaging the layers into `applierSpec`, `chainStep` over `backendStep`, `chain_put`/`_deleteRange`/`_range`/`_txn`; `auth.AuthStore` translated as an interface; a finding (a lease checkpoint entry's several critical sections; fix branch `lease-checkpoint-one-section`); gates 82 axioms, 1 sorry, apply 35/0, apply 63 of 73 functions verified, etcd 557 of 3599, see "Unit 1: the layers"; the apply package's units 0 and A merged into `lean` (the context premise `txnCtx` and the hook premise `csContract ∗ hookIs` both on txn's write path; one `csContract`, mvcc's; `store.Rev` under the hook's `End`; the server's `Link` reuses mvcc's zap results; gates 82 axioms, 1 sorry, apply 17/0, txn 22/0, mvcc 17/0, server 26/0, etcd 494 verified of 3599 functions), see "Merge 0/A"; the apply package's unit A: the backend's post-lock hook in mvcc's contract (`hookIs`, `csContract`), threaded through `store.Write`/`End` and txn's `Put`/`DeleteRange`/`Txn`, see "Unit A: the hook through mvcc"; the server's apply package, unit 0 on branch `apply-u0`: translated with bodies, scaffolding, 12 trust-boundary axioms, the txn functions at `context.TODO()` (`txnCtx`), `store.Rev`, `gen-link.py --apply` and the reuse rule; gates 81 axioms, 1 sorry; a finding (the alarm gauge), see "The server's apply package; a closed theorem about the register's driver in the operational semantics, `register_adequate`, from Perennial's adequacy; package initialization proved for raft, its subpackages, `context` and the register; the account of every axiom and `sorry` it rests on, see "Adequacy of the register's driver; Perennial `f8f01eb44` pinned: `time.wp_Since`/`Time.wp_Add` proved and `context.wp_WithDeadlineCause` proved (the `sorry` the concurrency proofs reached is gone; one new Perennial axiom `Timer.wp_Stop_func`), `isContext` stronger; `context.DeadlineExceededIsError` (a method-set fact, like `ErrorStringIsError`) added to raft's and the register's initialization premises; gates 57 axioms, 9 sorries (all the register's); small etcd axioms replaced by proofs on branch `etcd-small-axioms`: `NewHashStorage`, `UnsafeCreateMetaBucket`, `traceutil.TODO`, `Notifier.Notify`, `ServerConfig.ElectionTimeout`, `AlarmStore.Get`, `EtcdServer.Logger`/`isLeader` (with `MemberID`/`Lead`/`getLead`); `Trace.Step` requires a non-nil trace; `MustUnmarshalMessage`'s axiom made true (an encoding premise); gates on the branch 62 axioms, 1 sorry (57 axioms, 10 sorries once merged into `lean` with the standard-library axioms and the register's adequacy), etcd 505 verified of 3599 functions, 5202 of 45570 lines, see "Small etcd axioms"; a closed theorem about the register's driver in the operational semantics, `register_adequate`, from Perennial's adequacy; package initialization proved for raft, its subpackages, `context` and the register; the account of every axiom and `sorry` it rests on, see "Adequacy of the register's driver"; five standard-library axioms of etcd-grove proved from Perennial `e6ec34885` (pinned): `binary.bigEndian.{Uint64,PutUint64}`, `sort.Sort`, `sort.Reverse`, `errors.Is` (whose axiom was false as stated, now restated with Perennial's premises), see "Standard-library axioms from Perennial"; `origin/lean` merged into `mvcc` (the txn package, units 0–4, and its mvcc changes: the read-only write transaction, `metricsTxnWrite.Rev`/`Changes` of either kind, `idxLogAuth`, reads pinned by tokens; our `zap.Logger.Panic` kept), see "Merge: lean into mvcc (2026-10-12)"; mvcc: the watchable store, unit 2 complete: the batches (`ebAdd`, `batchOf`) and `choose`/`chooseAll` over the members' states, 23 functions of `watcher_group.go`/`watcher.go`; unit 3's design (the store's invariant, the channel protocol of the watch guarantee, three parts), see "The watchable store" and decisions.md "The watchable store's concurrency (unit 3)"; unit 2, first half: the watcher group's sets and structure (11 functions over the tree's contract, 5 of them conditional on it) and the client's watch stream (7 functions over the `watchable` contract; `trace.SpanFromContext` axiom), see "The watchable store"; 2026-10-11: unit 1b: the interval tree's contract (string-affine intervals over the opaque `ownIvt`, seven pending specs, `gen-link.py --adt`) and four pure functions proved, see "The watchable store"; unit 1a: `pkg/v3/adt` (the interval tree) and `watchable_store.go`/`watchable_store_txn.go`/`watcher.go`/`watcher_group.go` translated with bodies, the plan (contract first, the tree's proof last), see "The watchable store"; mvcc: `zap.Logger.Panic`/`Fatal` specified (a panic with the message; an exit, never returning), the key index's `put`/`tombstone`/`get` specified over all inputs (a bad input is the panic, the key index unchanged), `isTreeIndex` with a non-nil logger, see "`key_index.go`'s panics"; the txn units 3 (`Txn`) and 4 (the history laws of the log) merged into `lean` (`2175453f0`; notes-only conflicts, no proof changed; the whole package verified: every translated function of `txn.go`/`put.go`/`range.go`/`delete.go`, txn 39 of 48 functions, 570 of 653 lines; gates 69 axioms, 1 sorry, txn 20/0, etcd 474 verified of 3599 functions, 4943 of 45570 lines), see "Merge 3/4" and "The whole package"; the txn units 1 (`Put`, `DeleteRange`) and 2 (`range.go`) merged into `lean` (`mkGteRange` proved by both: unit 1's kept, `executeRange` adapted, one `wp_slice_literal_nn`; `gen-link.py` every mode reproduces; txn 27 of 48 functions verified, 274 of 653 lines; gates 69 axioms, 1 sorry, txn 20/0, etcd 462 verified of 3599 functions, 4647 of 45570 lines), see "Merge of units 1 and 2"; 2026-10-11: the txn units 0, 0b and 0c merged into `lean` (notes-only conflicts, no proof changed, both `Link.lean`s reproduce; gates 69 axioms, 1 sorry, txn 17/0, mvcc 13/0, etcd 435 verified of 3599 functions, 4373 of 45570 lines), see "Merge of units 0, 0b and 0c"; the server's `txn` package unit 0 on branch `txn-u0`: translated (`txn.toml`, Goose accepts it
as pinned), the requests and responses as the client model's values (`Requests.lean`), `isKV`,
`isTxnLessor`, 13 trust-boundary axioms (`sort.Sort`/`Reverse`, traceutil, `proto.Size`,
`zap.Logger.Panic`, ...), mvcc's read-only write transaction proved, `gen-link.py --txn`, a
finding (`Txn` panics on an empty `RequestOp`, rejected by the gRPC layer), gates 69 axioms, 1
sorry, etcd 435 verified of 3599, see "The server's txn package"; branch `mvcc` merged into `lean`: Perennial `e4e126e46` (one `AllG`: the `[AllG GF]` section variable dropped from the mvcc files), both sides' `gen-link.py` modes and notes kept, the etcd pin `bc8b52a50` (no change to the mvcc sources), see "Merge: mvcc into lean"; mvcc: `index.go` complete: `treeIndex.KeyIndex`/`Insert` proved under the index's history invariant (a reader's pointer lookup; the writer swaps a key's index for an equal one), see "`index.go`, the point operations"; mvcc: `NewStore` proved on a fresh backend: the ghost state allocated, the batch lock's resource deposited at its first `Unlock`, five new trust-boundary axioms, see "The store's constructor"; mvcc: `storeTxnWrite.Range` proved: the bucket view split between `s.revMu` and the batch lock, the batch transaction reads its own puts, `rangeKeys` over an owned reader capability and the index knowledge, see "The writer's range read"; the write transactions proved: `store.Write`, `storeTxnWrite.put`/`Put`/`delete`/`deleteRange`/`DeleteRange`/`End`/`Rev`/`Changes`, the wrappers over a `TxnKind`, `writeView.Put`/`DeleteRange`; the batch transaction's and the lessor's contracts, the revision budget; `proto.Marshal`, `zap.Error`, `zap.Logger.Error` axioms, see "The write transactions"; mvcc: the KV core, phase one: the key index, `index.go` over the verified B-tree, the range reads, the revision encoding, the read transactions opened and closed (`InvStore.lean`: the backend's Key-bucket contract, the store's locks) and the read transaction's `Range` (`rangeOutcome`: the key-values of the certified log at the requested revision, read from the index then the bucket; `traceutil.Trace.Step` and `proto.Unmarshal` axioms) and the wrappers (`metricsTxnWrite.Range`/`End`, `readView`; `traceutil.TODO` axiom) proved on branch `mvcc`, Perennial `bf935cbd5`: Goose ranges over an integer, `float64` of an integer, merged `lean` (panics and `recover`, `client/v3/leasing`), see "mvcc: the KV core, phase one"; Perennial's panics and `recover` adopted (Perennial branch `panic`, not yet pinned: needs `7cea8cc26`), the STM's two panic axioms gone, `lockerMutex.Lock`/`Unlock` specified, four standard-library axioms of `client/v3/leasing` replaced by Perennial's specs, see "Panic and recover"; `client/v3/leasing` unit 5: the monitors, `NewKV` and `Close` proved, every leasing result unconditional, 66 of 67 functions verified; two findings reproduced (`waitRescind`'s `nil` without a delete lets a range delete through another client's lease; a session reset between `acquire` and `Add` leaves a stale entry), see "Unit 5: the monitors; the package"; `client/v3/leasing` units 3 and 4: `txn.go` and `kv.go` but the monitors specified and proved, nested transactions and owned responses in the contract, two new findings (a write of an uncached key applied twice, a failed acquisition ignores the get's options), see "Units 3 and 4"; `client/v3/leasing` units 1 and 2: translated, the protocol as a premise on etcd's history with `leased_value_stable`, the lease cache specified and proved, findings in `EvictRange` and `evalCmp`, see "client/v3/leasing: the protocol premise and the lease cache"; merged upstream's register example, `node.go`, raft from upstream etcd-io/raft and thread tokens into the Mutex/Election/STM line, Perennial `7c93f27aa`, see "Merge: the register, `node.go` and thread tokens"; `STM`: all of `stm.go` specified and proved, atomicity of the serializable levels, Perennial `9276bd1ed`: a map has fewer than `2^63` keys, two trust-boundary axioms for the STM's panic and `recover`, a new history law, the serializable snapshot broken after a retry (a finding, reproduced and fixed on a fork branch), see "STM"; `Election`: all of `election.go` specified and proved, election exclusion, only the leader proclaims, `Campaign` may return `nil` without its key (a finding), see "Election"; `Mutex`: mutual exclusion, Perennial `d240c1732`: `fmt.Sprintf` formats `%s`, `strings.HasPrefix`, see "Mutex: mutual exclusion"; the register example verified over raft: logically atomic `Put`/`Get`, raft proposals over a client log, see "The register example"; the cache's wait-group counter bounded by thread tokens, Perennial `105fb79f5`: the `WaitGroup.Add` overflow assumption reverted, `New` assumes fewer than `2^31 - 3` live threads, see "The wait-group counter and thread tokens"; `node.go` proved: `RestartNode`, `run`, `Propose`, `Step`, `Tick`, `Ready`, `Advance`, see "`node.go`: the concurrent `Node`"; groundwork for `node.go`: a computed `Ready` can be abandoned, Perennial's `wp_slice_append_undo`; pre-vote out of scope at the RawNode level; `Ready`'s messages carry terms at most the node's, see "`node.go` groundwork"; `RawNode.Ready` split into `readyWithoutAccept` and `acceptReady`, for `node.go`; the storage contract has a pending append, for `node.go`; `MemoryStorage.Append` and `NewMemoryStorage` proved; merged upstream's RawNode work into the cache-as-shipped and concurrency line, Perennial `7d0b56b07`, see "Merge: upstream's RawNode work"; `RawNode.Step` takes a `MsgApp` between `Ready` and `Advance`; the `Advance` gap closed; Perennial `f52ce33dc`: Goose with Go 1.22 loop variables, range over arrays, `fallthrough`, `break` in `switch`/`select`, local types; the raft retarget to upstream parked, see "Retargeting raft to upstream"; the TCB and verified-code scripts generic, `--roots`/collections; Perennial `79adaac01`: models of `fmt.Sprintf`, `strings.Join`, `crypto/rand.Int`, three raft axioms gone; Perennial `7d0b56b07`: Goose with per-iteration loop variables, `break` out of `select`, see "Perennial `7d0b56b07`"; merged `cache-as-shipped` into the concurrency work, see "Merge: the cache as shipped and client/v3/concurrency"; the cache as shipped: the verified code is upstream main plus the one real fix, the store has shared writers, Perennial `9092f8eaa`: `WaitGroup.Add`'s overflow a model assumption, see "The cache as shipped"; `client/v3/concurrency`: the transaction and lease model, `Session` proved; the cache sorry-free: Perennial `3ae7dc6a4`, see "Sorry-free"; the cache's linearizability as a model fact, `etcdReached`; merged with upstream's server work: the consistent index and the apply thread, the raft predicate refactors and client-facing RawNode specs; Perennial `8c33774d0`: Goose without `-lean`; the whole cache package specified and proved; `etcdState_modrev_persist`: the owner promoted `queue_fifo_before_claim`'s hypothesis `EtcdModRevPersist` (a key-value lives unchanged from its mod revision while present) to the model's seventh history axiom, the result unconditional, gates 46 axioms, 1 sorry, see "The whole package"; `client/v3/experimental/recipes` unit 2 merged: the whole package verified, 38 of 38 functions, 401 of 401 lines, sorry-free, `pqueue_order` (least priority, then earliest, under `PQKeysWf`), `PriorityQueue.Enqueue` returns `seqKeyPutAt`, the token in `txnCommitErrTodo`, gates 45 axioms, 1 sorry, etcd 373 verified of 3599, see "Merge of unit 2" and "The whole package"; `client/v3/experimental/recipes` units 1b and 3 merged: no proof changes needed, the recipes 28 of 38 functions verified, all sorry-free, 300 of 401 lines, etcd 363 verified of 3599, gates 43 axioms, 1 sorry, see "Merge of units 1b and 3"; `client/v3/experimental/recipes` unit 3: the RWMutex and the double barrier specified and proved, exclusion under unmodified keys, see "Unit 3"; `client/v3/experimental/recipes` unit 1b: `newUniqueKV`, `newUniqueEphemeralKV`, `newSequentialKV` proved, `fmt.Sscanf` an etcd-grove axiom, the client's transaction errors `clientErrIs` (for `errors.Is`), `newSequentialKV` puts but does not create its key, its order under `SeqKeysBelow`, gates 43 axioms, 1 sorry, etcd 353 verified of 3599, see "Unit 1b"; Perennial `e4e126e46` pinned (`cb6a5921e` plus `strings.Split`, `errors.Is`, `fmt.Sprintf`'s integer directives under `ArgsWf`), merged with the one-`AllG` bump and the register's cluster driver, the recipes files without `[AllG GF]` (`waitEvents`' spec names `isSpsc (GF := GF)`), the gates unchanged (42 axioms, 4 sorries; etcd 350 verified of 3599); `client/v3/experimental/recipes` unit 1: the client bundle under the premise that a watch channel is never closed, the client's contracts at `context.TODO()` and its puts, `WithFirstKey`'s options needing a resource, `key.go`/`client.go`/`watch.go` specified and proved but three helpers left to unit 1b, the claim happens at one revision, see "Unit 1"; `client/v3/experimental/recipes` unit 0: translated (a Gooseable commit `bc8b52a50` pinned), the clientv3 option bodies, `gen-link.py --recipes`, the collection, two findings reproduced and fixed on a fork branch (`waitEvents` returns `nil` on a closed watch channel: `Dequeue` panics, `Barrier.Wait` returns released), see "Recipes"; Perennial `cb6a5921e` pinned: one `AllG GF`, provided by `HeapGS`; the `[AllG GF]` section variable dropped from 654 files, see "Perennial `cb6a5921e`: one `AllG`"; the register's cluster driver `Main` proved safe from package initialization, everything allocated in the proof; raft's `isLogger` was unsatisfiable, fixed, see "The register's cluster driver"; 2026-10-10: Perennial's panics and `recover` adopted (Perennial branch `panic`, not yet pinned: needs `7cea8cc26`), the STM's two panic axioms gone, `lockerMutex.Lock`/`Unlock` specified, four standard-library axioms of `client/v3/leasing` replaced by Perennial's specs, see "Panic and recover"; `client/v3/leasing` unit 5: the monitors, `NewKV` and `Close` proved, every leasing result unconditional, 66 of 67 functions verified; two findings reproduced (`waitRescind`'s `nil` without a delete lets a range delete through another client's lease; a session reset between `acquire` and `Add` leaves a stale entry), see "Unit 5: the monitors; the package"; `client/v3/leasing` units 3 and 4: `txn.go` and `kv.go` but the monitors specified and proved, nested transactions and owned responses in the contract, two new findings (a write of an uncached key applied twice, a failed acquisition ignores the get's options), see "Units 3 and 4"; `client/v3/leasing` units 1 and 2: translated, the protocol as a premise on etcd's history with `leased_value_stable`, the lease cache specified and proved, findings in `EvictRange` and `evalCmp`, see "client/v3/leasing: the protocol premise and the lease cache"; merged upstream's register example, `node.go`, raft from upstream etcd-io/raft and thread tokens into the Mutex/Election/STM line, Perennial `7c93f27aa`, see "Merge: the register, `node.go` and thread tokens"; `STM`: all of `stm.go` specified and proved, atomicity of the serializable levels, Perennial `9276bd1ed`: a map has fewer than `2^63` keys, two trust-boundary axioms for the STM's panic and `recover`, a new history law, the serializable snapshot broken after a retry (a finding, reproduced and fixed on a fork branch), see "STM"; `Election`: all of `election.go` specified and proved, election exclusion, only the leader proclaims, `Campaign` may return `nil` without its key (a finding), see "Election"; `Mutex`: mutual exclusion, Perennial `d240c1732`: `fmt.Sprintf` formats `%s`, `strings.HasPrefix`, see "Mutex: mutual exclusion"; the register example verified over raft: logically atomic `Put`/`Get`, raft proposals over a client log, see "The register example"; the cache's wait-group counter bounded by thread tokens, Perennial `105fb79f5`: the `WaitGroup.Add` overflow assumption reverted, `New` assumes fewer than `2^31 - 3` live threads, see "The wait-group counter and thread tokens"; `node.go` proved: `RestartNode`, `run`, `Propose`, `Step`, `Tick`, `Ready`, `Advance`, see "`node.go`: the concurrent `Node`"; groundwork for `node.go`: a computed `Ready` can be abandoned, Perennial's `wp_slice_append_undo`; pre-vote out of scope at the RawNode level; `Ready`'s messages carry terms at most the node's, see "`node.go` groundwork"; `RawNode.Ready` split into `readyWithoutAccept` and `acceptReady`, for `node.go`; the storage contract has a pending append, for `node.go`; `MemoryStorage.Append` and `NewMemoryStorage` proved; merged upstream's RawNode work into the cache-as-shipped and concurrency line, Perennial `7d0b56b07`, see "Merge: upstream's RawNode work"; `RawNode.Step` takes a `MsgApp` between `Ready` and `Advance`; the `Advance` gap closed; Perennial `f52ce33dc`: Goose with Go 1.22 loop variables, range over arrays, `fallthrough`, `break` in `switch`/`select`, local types; the raft retarget to upstream parked, see "Retargeting raft to upstream"; the TCB and verified-code scripts generic, `--roots`/collections; Perennial `79adaac01`: models of `fmt.Sprintf`, `strings.Join`, `crypto/rand.Int`, three raft axioms gone; Perennial `7d0b56b07`: Goose with per-iteration loop variables, `break` out of `select`, see "Perennial `7d0b56b07`"; merged `cache-as-shipped` into the concurrency work, see "Merge: the cache as shipped and client/v3/concurrency"; the cache as shipped: the verified code is upstream main plus the one real fix, the store has shared writers, Perennial `9092f8eaa`: `WaitGroup.Add`'s overflow a model assumption, see "The cache as shipped"; `client/v3/concurrency`: the transaction and lease model, `Session` proved; the cache sorry-free: Perennial `3ae7dc6a4`, see "Sorry-free"; the cache's linearizability as a model fact, `etcdReached`; merged with upstream's server work: the consistent index and the apply thread, the raft predicate refactors and client-facing RawNode specs; Perennial `8c33774d0`: Goose without `-lean`; the whole cache package specified and proved)

Porting the Rocq Raft proof (`new/proof/go_etcd_io/raft/election_proof/`) of
branch `worktree-agent-a22b3746ec9c86178` at `857d09190` (the RawNode branch: it merges
`worktree-raft-replication`'s `feb5c73d4` and adds Ready/Advance/HasReady; the files
were first ported from `main`, then from `feb5c73d4`) to Lean on top of Perennial's Lean
port (mit-pdos/perennial `lean`, pinned at cb6a5921e (2026-10-11: on cb6a5921e: the one `AllG GF` is `GooseGlobalGS.gooseAllG`, provided by `HeapGS`, `ThreadGS`/`ReceiptGS` without their own, see "Perennial `cb6a5921e`: one `AllG`"; on bf935cbd5: Goose ranges over an integer (`for i := range n`, as the three-clause loop) and `float64(n)` of an integer as an uninterpreted function, for mvcc, on upstream's 7cea8cc26 (panics and `recover`, `strings.Compare`/`TrimPrefix`, `(*Time).Add`, `errors.As`), see "mvcc: the KV core, phase one" and "Panic and recover"; on 7cea8cc26 (the `panic` branch merged): the panic outcome, `Catch`, `recover`, standard-library models, see "Panic and recover"; 2026-10-10: on 7c93f27aa: our 9276bd1ed merged with upstream's 105fb79f5 (thread tokens, `wp_fork_tok_*`, the revert of the `WaitGroup.Add` assumption, `wp_slice_append_undo`, the iframe heartbeat option), see "Merge: the register, `node.go` and thread tokens"; on 9276bd1ed: a map has fewer than `2^63` keys, `wp_map_len_lt`, see "STM"; on d240c1732: models of `fmt.Sprintf` formatting `%s` and of `strings.HasPrefix`, see "Mutex: mutual exclusion"; on 7d0b56b07: our `9092f8eaa` merged with upstream's Goose changes (per-iteration loop variables, array ranges, `fallthrough`, `break` out of `switch`/`select`, local types) and `context.wp_WithCancel` building again, see "Perennial `7d0b56b07`"; on f52ce33dc (upstream's, in 7d0b56b07): the Goose features for upstream raft, see "Perennial `f52ce33dc`"; on 79adaac01 (upstream's, in 7d0b56b07): `context.wp_withCancel` builds again; on 9092f8eaa: `WaitGroup.Add`'s overflow a model assumption, the `RWMutex` writer guard, see "The cache as shipped"; on 56b1b6651: our 3ae7dc6a4 merged with upstream's `00b3c10ea` (trusted models and proved specs of `fmt.Sprintf`, `strings.Join`, `crypto/rand.Int`; `math/big`'s `ownInt` normalized, its and `crypto/rand`'s `IsPkgInit` instances now Perennial's), see "Perennial `56b1b6651`"; on 68d220ac8: `fmt.wp_Errorf` proved, `map.forRange` with `wp_map_for_range_mut{,_keys}`, `context.wp_WithCancel` proved; on 3ae7dc6a4: `context.isClosedchanInit`, see "Sorry-free"; on 8c33774d0: upstream's `37416dd10` (Rocq code removed) and `cdf8c0f81` (Goose without `-lean` and the ⁱᵐᵖˡ encoding) merged, see below; on f8b35ddbf: `context.wp_Background`, `wp_WithCancel_Background`; on f35530719: Goose prints an axiomatized generic type in Lean; on 8c7000190: `time.NewTimer`, `Timer.Stop`/`Reset` axioms; on 96ec7016d: `fmt.wp_Printf`, `time.Minute`; on 099c2a08b: `fmt.wp_Errorf`'s `Error()`; on 640a605cc: a `select` case on a nil channel is never ready, `chan.wp_select_blocking_nil`; on 48e1192c7: rlocker, `Cond.wp_Wait_with`, `time.wp_Since`) on cbb85c041: upstream's `11fd2db` merged with
`bytes.Compare`, on Lean's module system since 2026-10-09). The Goose translations of
etcd-raft and etcd's `cache` package are this repository's `Code/` and `GeneratedProof/`,
generated and checked by `etc/goose.py`. Files are laid out by kind and Go package path
(`Spec/go_etcd_io/raft/v3/raft__Step.lean`) and every file is a module of Lean's module
system (2026-10-08; decisions.md, "Layout by kind and Go package path" and "Lean's
module system").

## The backend (`server/v3/storage/backend`, 2026-10-12/13, branch `worktree-backend`)

Design: `notes/decisions.md`, "The backend: the buffers, bbolt as a key-value contract, the locks
and the views" (and "The backend's proofs: what changed from the plan"). Off `origin/lean`
`5a04bdf29`, Perennial `5857c495a`.

- **Translation** (unit 0): `storage/backend.toml` translates `tx_buffer.go`, `read_tx.go`,
  `batch_tx.go`, `hooks.go` and the core of `backend.go` (the constructor, `ReadTx`, `BatchTx`,
  `ConcurrentReadTx`, `ForceCommit`, `run`, `Close`, the metrics getters, `begin`) with bodies;
  the snapshot, the hash, defragmentation, `verify.go` and `metrics.go` names only.
  `bbolt.toml` now imports `time` and `internal/common` (so `Tx`, `TxStats`, `Bucket` are
  structs; `Options` stays axiomatized: its `OpenFile` names `os.FileMode`, an alias Perennial
  axiomatizes); `bbolt/errors` and `encoding/hex` are names only. The package-init instances the
  backend needs moved to `storage/backend/Base.lean` (from `etcdserver/Base.lean`,
  `BaseApply.lean`, mvcc's `Base.lean`).
- **The buffers** (unit 1, `tx_buffer.go`, 20 functions): `Model.lean` (entries, `canon`: sorted,
  newest wins; `bbRange`; the write and read buffers' transitions), `InvBuffer.lean`. `writeback`
  takes the premise that a bucket's buffered puts have distinct keys (`WBuf.Wf`).
- **bbolt's key-value contract** (`InvBbolt.lean`, `Spec/go_etcd_io/bbolt/*_kv*.lean`): bbolt is the
  trust boundary (its proof, branch `bbolt`, is physical: pages and cursor stacks, and is not
  merged); 20 function specs (`bbolt.<T>.<M>_kv.spec`, the read and write transactions' `_kvr`/
  `_kvw`) over 15 axiomatized predicates (the database's committed data, read snapshots, the
  writer's contents, slices valid while the transaction is open), with their instances.
- **The locks and the views** (units 2 and 3, 58 functions of `read_tx.go`, `batch_tx.go`,
  `hooks.go`, `backend.go`): `Model2.lean` (the batch state `BSess`, the readers' view `vData`,
  `hookStep`, `rtRange`), `InvBackend.lean`, `InvBatch`/`InvCommit`/`InvStop.lean` (write side),
  `ReadSide`/`ReadLemmas.lean` (read side). The clients' contract: `bView γ q vd` (their half of
  the readers' view), `batchLocked γ P b st` (a session), `rdTok`/`rtHeld` (the shared read
  transaction), `crtSnap` (a `ConcurrentReadTx`), `wbTok` (a write-back's or a client commit's
  budget), `bOpen` (open; `Close` takes all of it). An `Unlock` after a session that changed what
  readers see takes the clients' whole half of the view and gives it back at the writer's contents
  (off the pre-commit hook's buckets); readers see the view they agree with.
- **Linked**: `Proof/.../backend/Link.lean` (`gen-link.py --backend`, 78 results, all without
  `sorry`); the collection `etc/tcb-collections/backend.txt` (59 axioms: bbolt's contract,
  `sort.Stable`, `verify.Assert`/`Verify`, verify.go's three lock checks, zap's `Error`,
  `Stringer`, `Stack`, `Logger.Fatal`, `time.Duration.Seconds`). The gates: 147 axioms, 9
  sorries (were 93, 9); etcd 695 of 3599 functions verified (was 625), the backend package 70 of
  112 (556 of 1281 lines). After the merge into `lean` (2026-10-13, Perennial `a54e1999f`: its
  umbrella module `Perennial.Proof.sync` in place of `sync_proof.*`; `bucketBuffer.Swap` and
  `backend.run` adapted): 158 axioms, 9 sorries, etcd 761 of 3599.
- **Findings** (`issues/`): `etcd-backend-duplicate-put-stale-read` (two puts of one key in one
  session: `ReadTx` reads the older; reproduced), `etcd-backend-read-buffer-cache-stale-after-commit`
  (the `ConcurrentReadTx` cache keyed by a version a commit does not change: a deleted key or a
  hook-rewritten key's old value read back; two reproductions). Both not filed.
- **Assumptions to know**: verify.go's `ValidateCalled*` return (the `ETCD_VERIFY` lock checks
  off); bbolt's contract as stated (an axiom per function); `Close` and `run` are stated at
  `HasLC.hasLC` (Perennial's broadcast channels); the hook's puts must not repeat a key between
  write-backs (etcd's consistent-index hook does after two commits: harmless in Go, but the
  server's hook cannot be proved against this contract as it stands).
- **Not done**: the constructor (`New`, `NewDefaultBackend`, `newBackend`: bbolt's `Options` is
  axiomatized), so `isBackend`'s invariants are allocated by assumption; `UnsafeForEach` (three
  functions); the snapshot, the hash, defragmentation; cindex's `isMetaBackend` from this contract; mvcc's
  store over it (the bridge proves mvcc's general contract, the store uses the instance without
  tokens: "Unit 4" below);
  bbolt's proof of the contract.

### Unit 4: the backend meets mvcc (2026-10-13)

Design: `notes/decisions.md`, "The backend meets mvcc (unit 4)". Part 1 (`bdef1e5e3`): the
backend's lock resource split as mvcc's (`W`, `Pk`), `LockInsideApply` in mvcc's hook shape, the
post-lock hook read-only once set, `Unlock` without the view for a session that changed nothing
readers see; mvcc's contract weakened where false of bbolt (slices tied to the reader's token).
Part 2, **the bridge** (`Proof/.../storage/mvcc/BackendBridge.lean`, no `sorry`):

- **The result**: `mvcc.isKeyBackendG_of_backend`: `isBackend γ P W Pk b ∗ plHookRO γ f ∗
  rangeSafe γ P b ⊢ isKeyBackendG (b as a Backend) (bkView γ) (bkRT γ P b qo) (wbTok γ) bkPutOk
  W Pk #f`, for `bridgeParams P` (the table has schema's `Key` (1) and `Meta` (2); the hook's
  buckets are all but `Key`) and `f ≠ nil`; linked with the backend's results and schema's
  `bucket` methods in mvcc's `Results.lean` (`mvcc_backend_bridge`: bbolt's contract, verify's
  and zap's axioms, no `sorry`). Its instance: `bkView γ q m` the backend's clients' view whose
  `Key` bucket is `m`; `bkRT` a reader's slot (`rdTok`) and a share of the backend open;
  `bkLocked γ P b l` the batch lock in a session whose write buffer's `Key` bucket is the puts
  `l`, with a write-back's budget; `bkLockedO` `NewStore`'s session.
- **mvcc's contract, generalized** (`InvStore.lean`): `isKeyBackendG b View RT WT PutOk W P f`
  (`batchTxSpecG`, `batchTxInitSpec`, `isBatchTxG`); the store's `isKeyBackend b View W P f` is its
  instance with `RT = WT = True` and no condition (`noPutCond`), so no spec above mvcc changed.
  What changed, every statement: a reader's token `RT` taken by `ConcurrentReadTx`/`ReadTx` and
  given back by `RUnlock`, lent to `LockInsideApply`, `LockOutsideApply`, `ForceCommit`; a
  session's token `WT` spent by `LockInsideApply`/`LockOutsideApply`/`ForceCommit` (the
  backend's write-back budget); `UnsafeSeqPut` with the condition `⌜PutOk l k v⌝`; the snapshot
  split: `keyReadSnap View RT rt m L` is `RLock`, which takes the caller's view `View q m` (and
  keeps it) and *chooses* the slices' predicate and the token (`keyReadLocked RT rt m Rd Tok`:
  `RUnlock`, the reads, `rdCap`): the shared read transaction reads the interval its `RLock`
  finds (mvcc holds `s.revMu`'s view then: `store.Read`, `rangeEvents`); `NewStore`'s calls
  as their own triples (`batchTxInitSpec`: `LockOutsideApply` gives `LockedO 0`, two creations of
  `Key`/`Meta` (`globalAddr ↦□ b`), `Unlock` from `LockedO n`); `schema.UnsafeCreateMetaBucket`'s
  callback on the `Meta` bucket's value, from `P` to `Q`. mvcc's proofs adapted (`store.Read`,
  `rangeEvents`, `storeTxnRead.End`, `storeTxnCommon.Range`, `store.Write`, `storeTxnWrite.put`/
  `delete`, `NewStore`; `batchTxSpec_reader`).
- **schema** (`schema.toml`): `bucket`'s methods (`ID`, `Name`, `String`, `IsSafeRangeBucket`),
  `Key`, `keyBucketName`, `metaBucketName` translated; the methods proved
  (`Proof/.../storage/schema/bucket__*.lean`, linked in mvcc's `Link.lean`); `schemaInit` states
  `Meta`'s and `Key`'s values (`bucketIs`: the `bucket` struct, its name's bytes), from which
  `isBucket` follows (`key_isBucket`, `meta_isBucket`); the nine users of `schemaInit` adapted.
- **The range read** (`keyRangeReadSpec`, the watchable store's): the backend's `UnsafeRange` of a
  range is bbolt's window then the read buffer's; `rtRange_safe` (pure, proved) makes it the
  bucket's range when the read buffer's `Key` keys are above bbolt's (`keySafe`). The premise
  `rangeSafe γ P b` (every readers' state of a read transaction is `keySafe`) is not given by the
  backend's invariant: a client may overwrite a key or put one below bbolt's (the safe-range
  discipline Go's `IsSafeRangeBucket` documents; see also `etcd-backend-duplicate-put-stale-read`).
- **What the composition (mvcc's store over the real backend) still needed** (done in unit 5, below):
  1. *mvcc's view is its own*: the store's `bucketView γ` is a ghost map of mvcc's (`γ.bucket`,
     given fresh to `NewStore`); the bridge's view is the backend's (`bkView`). The store would
     take the backend's names (e.g. in `StoreNames`) and `bucketView := bkView`.
  2. *The lock resource is fixed at the backend's creation*: `isBackend`'s `W` is chosen when the
     backend is made, but mvcc's `writerRes s γ` names the store's location and ghost names,
     which `NewStore` allocates (its premise quantifies over them). Needs a late-bound resource
     (the backend made with `W := unset ∨ ∃ s γ, registered (s, γ) ∗ writerRes s γ`, `NewStore`
     registering at its first `Unlock`).
  3. *The tokens*: mvcc's store passes `RT = WT = True`. `RT` can live in `storeReader` (one per
     reader slot, a saved proposition in the store's names: the store keeps its readers'
     tokens, `NewStore` given a supply); but `WT` cannot: every `Unlock` with a pending operation
     writes back (`bufVersion++`, a `uint64`; the backend's proof budgets write-backs below
     `2^40` so that a stale cache never looks current), and mvcc's write transactions that
     change nothing return their revision token, so they are unbounded: `store.Write` would need
     a session token from its callers (the txn/apply/server layers), or the backend a different
     argument for the version.
  4. *The puts' condition* `bkPutOk`: at most `2^56` puts per session (mvcc's `put` takes
     `pend.length + 1 < 2^63`), keys increasing (revisions: true, a `revBytes` order lemma),
     a value of at most `MaxValueSize` bytes (mvcc does not bound the encoded `KeyValue`:
     `issues/etcd-backend-put-value-too-large-fatal.md`).
  5. *`rangeSafe`*: the safe-range discipline added to the backend's batch-lock invariant and
     `UnsafeSeqPut`'s premise.
- **Gates**: 158 axioms, 9 sorries (unchanged); the collections mvcc, backend, txn, apply,
  server, v3rpc unchanged; `etc/goose.py --check` up to date.
- **Tactic note**: `wp_apply` of the backend's `Unlock` spec aborted without a message in
  `bt_unlock` (the same call in `bt_unlockO` is applied by hand too) (the goal left untouched, reported as unsolved at `by`); applying the
  triple by hand (`iapply (spec ...) $$ %Φ [...] HΦ`) works.

### Unit 5: mvcc's store over the real backend (2026-10-13)

Design: `notes/decisions.md`, "The store over the real backend (unit 5)". The five gaps of
unit 4, closed or narrowed:

- **The instance** (gaps 1 and 2): `StoreNames` gets `kb : Option KBReal` (`none`: mvcc's assumed
  contract over the store's ghost map, as before; `some d`: the real backend, named by data: its
  ghost names, table, `hookMax`, limit, location and the lock-resource registration name `gx`).
  `bucketView γ` is `kbView γ.kb γ.bucket` (the real one is `bkView d.γB`, moved from the bridge
  to `InvStore.lean`, with `keyView`), and `isStore` holds `isKeyBackendG b (bucketView γ)
  (storeRT γ) (storeWT γ) (storePutOk γ) (storeW s γ) (kbWi γ.kb) Ph fh` and `storeRegd s γ`; the
  store's tokens are functions of `γ.kb` (`kbRT`, `kbWT`, `kbPutOk`, `kbPutMax`), so no saved
  proposition and no later credit. mvcc now imports the backend's `InvBackend`.
- **The late-bound lock resource** (gap 2): the real backend is made with `W := lateW gx`
  (`InvStore.lean`): unset (half of `gx` at `none`, the creator holding the other half,
  `lateReg`) or set for good to `(s, γ)` with `writerRes s γ`. `NewStore`'s first `Unlock`
  registers the store (`storeW_register`); `storeW_get`/`storeW_put` convert under the store's
  persistent `storeRegd s γ`. No backend proof changed: `isBackend` is generic in `W`. mvcc's
  `batchTxInitSpec` gains the lock's initial resource `Wi` (`LockOutsideApply` returns it: the
  bridge no longer drops `W`).
- **The tokens** (gap 3): `storeReader s γ` holds a reader token `storeRT γ` (the real one:
  `rdTok ∗ ∃ q, bOpen q`, `bkRTx`), lent to `ConcurrentReadTx`/`ReadTx`/`LockInsideApply` and
  returned by `RUnlock`/`End`; `txReader` takes `γ`. `store.Write` (and `watchableStore.Write`,
  `writeView.Put`/`DeleteRange`) spends a write token `storeWT γ` (the real one: `wbTok`, the
  backend's write-back budget); `NewStore` takes one reader token per reader slot and two write
  tokens.
- **The puts** (gap 4): mvcc's contract's `UnsafeSeqPut` takes the caller's view of the bucket
  and `PutOk m l k v`; the real condition `keyPutOk` (at most `2^56` puts, key of
  `1..MaxKeySize` bytes, above every key of the bucket and of the session's puts) is proved of
  mvcc's revision keys (`storePutOk_next`, from `RevOrder.lean`: `revBytes` ordered by (main,
  sub), the bucket's keys earlier revisions', the pending puts' earlier positions). The per-txn
  bound is `putMax γ` (`2^63`, or `2^56` for the real backend) in mvcc's `put`/`Put`/`delete`/
  `deleteRange`/`DeleteRange` and the metrics wrappers, and in the txn package's `put`,
  `deleteRange`, `executeTxn`, `txn`. The value bound is gone: bbolt's `Put` kv-spec now covers
  an oversized value (a non-nil error, contents unchanged: true of Go, the axiom keeps its name)
  and the backend's `unsafePut` takes the `lg.Fatal` branch, so the backend's put specs drop
  `vb.length ≤ maxValueSize` (`issues/etcd-backend-put-value-too-large-fatal.md`).
- **The safe range** (gap 5): `BParams` gets `SB` (the safe-range buckets; `Wf`: not the hook's);
  the batch state's invariant (`sessWf`'s new conjunct `safeSt`) keeps, for a safe bucket, the
  read buffer's and the write buffer's keys above the committed data's, and the committed keys in
  the writer's contents; `UnsafePut`/`UnsafeSeqPut` on a safe bucket require the key above every
  key of the writer's bucket, `UnsafeDelete`/`UnsafeDeleteBucket` a bucket not safe; the readers'
  states keep `safeRv` (`rtCore`), exported as `rtHeld_safe`. The bridge's premise `rangeSafe` is
  replaced by `keySized` (fewer than `2^62` entries of `Key` in a held state: the range's limit is
  `2^63 - 1` and nothing bounds a bucket's size; an honest premise of the composition, not
  discharged). A `ConcurrentReadTx` no longer promises a range read (`keyReadSnap`/`keyReadLocked`
  take `rng`): false in Go, see the finding below.
- **The composed results** (`StoreBackend.lean`, linked in mvcc's `Results.lean`):
  `mvcc_NewStore_backend` (`NewStore` on a fresh backend of the real instance `d`:
  `isBackend d.γB d.P (lateW d.gx) Pk d.be`, `plHookRO`, `keySized`, the creator's empty view,
  `lateReg`, two `wbTok`s and one `bkRTx` per reader slot, gives a store with `γ.kb = some d`) and
  `mvcc_store_Write_backend` (`store.Write` at such a store, for a `wbTok`); every other store
  result is generic in `γ.kb` and holds at `some d` as stated. The bridge: `storeBackend_of_backend`
  (the contract `NewStore` takes, for every store of the instance). `#print axioms`: bbolt's
  contract, verify's and zap's axioms and the store's trust boundary (`restore`, ...), no `sorry`.
- **Above mvcc**: `txn.isKV` carries `γ.kb = none`: the txn, apply, server and v3rpc results stay
  over mvcc's assumed backend (unchanged statements; the txn package's internal `put`,
  `deleteRange`, `executeTxn`, `txn` take `putMax γ`). Re-targeting them needs: a write token per
  write transaction (every `Unlock` writes back: the apply thread's `kvOwn`/`soleWriter` would
  carry a counted supply, and the server's apply loop a bound on its writes, since `soleWriter`'s
  budget is a function of the log and empty write transactions spend a write-back too); the
  per-transaction change bound `2^56` from the request layer (a `DeleteRange` tombstones every
  key of its range, so the request limits do not give it); the `keySized` premise at the server's
  creation.
- **Finding** (`issues/etcd-backend-read-buffer-cache-stale-after-commit.md`, a third
  reproduction): a `ConcurrentReadTx` after any commit reuses its cached read buffer over the new
  bbolt transaction, and a range of `Key` returns a written-back, committed key twice
  (`cache_range_dup_test.go`, fails at the pin). Not reached by mvcc (its `ConcurrentReadTx` reads
  one revision key at a time).
- **Gates**: 158 axioms, 9 sorries (unchanged); the collections mvcc, txn, apply, server, v3rpc
  updated (four bbolt-contract predicates, `rBkt`, `rtxSnap`, `rtxStats`, `txLive`, now in their
  statements' terms: the store's reader token names the backend's); backend unchanged; every Link
  builds. The axiom `mvcc.store.restore.wp_proof` is generalized (any backend contract, not only
  the assumed one: it does not use it); bbolt's `Bucket.Put_kv.wp_proof` extended (above).
- **Tactic note**: `wp_apply` of `RUnlock` in `rangeEvents` aborted (an unsolved goal at the
  call): applied by hand; a projection of `dghostVar_split` misparsed, `dghostVar_persist` of one
  half used instead.

### Unit 6: the layers above mvcc over the real backend (2026-10-13)

Design: `notes/decisions.md`, "The layers above mvcc over the real backend (unit 6)". The txn,
apply, server and v3rpc results are now generic in the store's backend instance (`γ.kb`): they
hold for mvcc's assumed backend and for the real one (`γ.kb = some d`), whose results rest on
the backend's proof and bbolt's key-value contract.

- **`txn.isKV`** drops `⌜γ.kb = none⌝` (`txn/Defs.lean`); new there: `txn.putMax_ge` (`2^56 ≤
  putMax γ`), the counted supply `txn.storeWTs γ n` (free over the assumed backend, `ownToks
  d.γB.wb n` over the real one: `n` write-back tokens) and `storeWTs_split`.
- **The write budget** (gap 1 of unit 5): every call that may open a store write transaction
  spends one `mvcc.storeWT γ`, which the caller supplies:
  `txn.Put.spec`, `txn.DeleteRange.spec`, `txn.Txn.specSole` (also on a failed lease check, a
  failed `checkTxn` or a read-only request: wasted), `txn.put_soleWriter_of`,
  `txn.deleteRange_soleWriter_of` and their `Results.lean` restatements (`put_soleWriter`,
  `deleteRange_soleWriter`, `txn_runTxn`, `txn_readonly_no_revision`,
  `txn_check_error_no_write`); the applier's `putPre`/`deletePre`/`txnPre`/`revokePre`
  (`apply/Chain.lean`, so every layer's triple of `Put`, `DeleteRange`, `Txn`, `LeaseRevoke`),
  the lessor contract's `Revoke` (`isApplyLessor`: its range deleter is the store's `Write`),
  `uberApplier.dispatch`, `uberApplier.Apply`, `apply.Apply` and the server's
  `applyEntryNormal` (one token each); the server's `apply` takes `txn.storeWTs E.γ ms.length`
  and `applyEntries` `txn.storeWTs E.γ (unapplied ai ms).length`: **one token per entry**
  (the premise of the top result `applyEntries_model`; a conf change's or a replayed entry's
  token is wasted). The count is a resource the caller holds, not a function of the log (empty
  write transactions spend a write-back too).
- **The change bound** (gap 2): the per-transaction bound is `2^56` at the request level (both
  instances: `putMax γ ≥ 2^56`). `txn.DeleteRange.spec`: `(rangeIn (stateAfter ilog) o).length <
  putMax γ` (was the whole state `< 2^63`); `apply.delOk log o`: room for a revision and
  `(rangeIn (stateAfter log) o).length < 2^56` (takes the request now; `rqOk`'s delete case is
  `∀ o, rq.deleteRange = some o → delOk log o`); `txn.TxnPre`'s change bound `< 2^56` (was
  `2^63`). The narrowest honest premise: a delete tombstones exactly its range's keys.
- **`keySized` at the server** (gap 3): `server_kv_backend` (`etcdserver/Results.lean`, linked,
  no `sorry`): `NewStore` on a fresh backend of the real instance (premises: `isBackend` with
  `lateW`, `plHookRO`, **`keySized`**, the clients' empty view, `lateReg`, `ownToks d.γB.wb (N +
  2)`, a reader token per slot, the lessor) gives a store with `γ.kb = some d` that is
  `txn.isKV`, its reader slots, `txn.soleWriter γ [[], []]` and `txn.storeWTs γ N`: the apply
  thread's `kvOwn` (with the empty state's leases) and `applyEntries`' write budget. The
  backend's constructor is not proved, so these are the backend creator's resources, premises.
- **Gates**: 158 axioms, 9 sorries (unchanged); every Link builds (full `lake build`); the
  collections mvcc, txn, apply, v3rpc, backend, cache, recipes, leasing, concurrency,
  register, server-raft unchanged; `server` updated (65 → 114: `server_kv_backend` reaches
  bbolt's contract, the backend's axiomatized predicates, `sort.Stable`, verify's and zap's
  axioms, `mvcc.store.restore`, `schedule.NewFIFOScheduler`, `zap.NewNop`).
- **What still separates the client's Put/Get from a fully verified flow**:
  1. *Raft is a contract* on the request path (the raft wrapper's `raft.Node`, etcd's raft v3.7
     in `EtcdDeps/`, is not linked to the Raft proof of `Code/go_etcd_io/raft/`; the two
     translations define the same names and never meet).
  2. *The server's creation* (`NewServer`, the apply loop's `run`) is not proved: `isServer`,
     the environment `E` (its store being the one `server_kv_backend` makes), the wait registry,
     the request path's `isServerReq` are premises; `server_kv_backend` composes only the KV.
  3. *The backend's constructor* (`newBackend`: bbolt's `Options` is axiomatized), so
     `isBackend`, the write-back and reader tokens are allocated by assumption; the
     write-back budget (`2^40`) bounds the server's lifetime writes (`N`).
  4. *The other writers of the backend* are assumed contracts that do not account for the real
     backend's sessions: the lessor, the auth store, the membership, the alarm store, and the
     consistent index (`isMetaBackend` not derived from the backend's contract; the
     consistent-index hook repeats puts between write-backs, which the backend's contract
     forbids), so their own `Unlock`s spend no write-back token here.
  5. *bbolt is a contract* (20 axioms); `keySized` is a premise.
  6. *The linearizable read* (`range_linearizable`) rests on raft's `ReadIndex` contract
     (`LinearizableReadNotify`'s); the serializable read and the read-only `Txn` read the store
     directly (generic now).
  7. Compaction is out of the model; `ConcurrentReadTx` promises no range read (the cache
     issue).

## Perennial `a54e1999f`: the proof layout (2026-10-12)

Perennial `5857c495a` → `a54e1999f`, branch `worktree-perennial-bump`. `a54e1999f` is Perennial's
one-spec-per-file layout of its own proofs (`Perennial/{Spec,Proof}/<pkg>/<F>.lean`, linked in
`Perennial/Proof/<pkg>/Link.lean`, umbrellas at the old module paths), with what `lean` had
before it: Goose's evaluation order for `s[a:]`, multiple assignment and select sends; fmt/log
specs only for arguments of predeclared basic types (`ArgsWf`); `time`'s `NewTimer`/`Stop`/`Reset`
translated and proved (`Timer.wp_Stop` for `isTimer ∨ isFuncTimer`); `make(chan T, n)` stuck where
`makechan` may panic; `errors.wp_New` with `IsPointerError`; `math.bits.wp_Len` exact.

**Why not Perennial's current `lean` (`d0324b842`).** Since Perennial `3fbe65749` (panics on
the exception monad) the model does not propagate a panic to the caller, so etcd's STM
(`stm.fetch`/`commit` panic with `stmError`, recovered by `runSTM`'s goroutine) is not provable;
an axiom for it would contradict the model's own (stuck) code. The port to `d0324b842` so far is
on branch `perennial-d0324-wip` (`notes/perennial-d0324-wip.md` there): it waits for Perennial to
propagate panics to the caller's deferred functions.

**What changed here.**
- Translations regenerated (`etc/goose.py`: raft 1, etcd 9, register 1 file); imports of
  Perennial's moved modules (`sync_proof.mutex`, `context_proof.context_init`, `sort_proof.*`,
  `slices_proof.*` → the umbrellas `Perennial.Proof.{sync,context,sort,slices}`,
  `slices.SortBasics`).
- fmt with basic arguments: explicit `ArgsWf` proofs (`validateRevisions`, `store.getSnapshot`,
  `newCache`, `store.applyEventsLocked`, `concurrency.Mutex.Unlock`, `EtcdServer.applyEntries`,
  `newRaft` (`.1` of `Sprintf`'s spec)).
- Timers: `realTimer.Stop`, `demux.resyncLoop` take `wp_Stop`'s `isTimer` case;
  `idutil.NewGenerator` uses `Time.wp_ptr_UnixNano`.
- Evaluation order: `btree.node.remove` (the multiple assignment's bounds check first).
- `register_adequate` from `goose_adequacy` (`goose_adequacy_nopanic` is gone; its third
  conclusion gives the "no unrecovered panic" conjunct; the statement is unchanged).
- New link modes `etc/gen-link.py --fmt`, `--context` (`etc/link-lean-first-{fmt,context}.txt`):
  the fmt and context trust-boundary results are linked once (`Proof/fmt/Link.lean`,
  `Proof/context/Link.lean`) and used as `@` callees by the cache's and mvcc's links.

**Trust added (to remove later)** — the user approved trust-boundary axioms for these, to be
replaced by proofs (most need Perennial specs):
1. `fmt.Errorf.wp_proof` (axiom, `Proof/fmt/Errorf.lean`): `Errorf` on arguments each basic
   (`ArgWf`) or with an `Error()`/`String()` that returns some string (`fmt.argsOk`) returns an
   error whose `Error()` returns some string. True assuming no argument implements
   `fmt.Formatter`. Removable by a Perennial `wp_Errorf` for such arguments.
2. `fmt.Printf.wp_proof` (axiom, `Proof/fmt/Printf.lean`): the same for `Printf`.
3. `fmt.SprintfNamed.wp_proof` (axiom, `Proof/fmt/SprintfNamed.lean`): `Sprintf` with arguments
   nil, `ArgWf`, or of a type in `fmt.methodlessNamedTypes` (only `client/v3.LeaseID`, `type
   LeaseID int64`, no methods) gives `SprintfOut format xs s`. For `Mutex.tryAcquire`,
   `Election.Campaign`.
4. `time.Duration.String.wp_proof` (axiom, `Proof/time/Duration__String.lean`): returns some
   string (Go's is translatable: a proof is possible here or in Perennial).
5. `context.Err.wp_proof` (axiom, `Proof/context/Err.lean`): for `isContext c s`, `c.Err()` is as
   `isContext` says and a non-nil error it returns has an `Error()` returning some string. True
   of the standard library's and gRPC's contexts (`Canceled` is `errors.New`, `DeadlineExceeded`'s
   `Error` returns a constant); assumed for user-defined contexts (stated for any semantics
   instance). For `cache.watchEvents` (`mvcc.storeTxnCommon.rangeKeys` no longer: the merge
   of `origin/lean` into the request path, 2026-10-13).
6. `rpctypes.Error.wp_proof` (existing axiom, strengthened,
   `Spec/go_etcd_io/etcd/api/v3/v3rpc/rpctypes/Error.lean`): the result's `Error()` returns some
   string when the argument's does (`□ (errStrOk err -∗ errStrOk err')`).
7. `status.Error.wp_proof` (existing axiom, strengthened,
   `Spec/google_golang_org/grpc/status/Error.lean`): `errStrOk` of the result.
8. `cacheInit` (assumed init facts, strengthened, cache `Base.lean`): `ErrUnsupportedRequest`'s
   `Error()` returns some string (it is `errors.New`).
9. `rpctypesInit` (assumed init facts, strengthened, cache `Base.lean`): `ErrFutureRev`'s
   `Error()` returns some string (an `EtcdError`).
10. `isEtcdKVE` (new client contract, `InvEtcd.lean`): `isEtcdKV` plus a `Get` error's `Error()`
    returns some string; replaces `isEtcdKV` in the cache only (`isCacheFields`, `New`).
11. `watchRespOk` (client contract, strengthened, `InvEtcd.lean`): an error response's
    `closeErr` satisfies `errStrOk`.
12. `isEtcdProgressNotifier` (client contract, strengthened, `InvEtcd.lean`): a non-nil
    `RequestProgress` error's `Error()` returns some string.

**Statements changed.**
- `newWatcher`: `0 ≤ bufSize < 2^32` (was `0 ≤ bufSize`), with `CfgBounded` and
  `isCacheFields`' `Hbuf`; `newCache.spec`, `New.spec` inherit it (a huge `PerWatcherBufferSize`
  makes `makechan` panic too: added to `issues/cache-ready-after-retry.md`).
- `errStrOk err` added to the postconditions of `validateRevisions`, `demux.Broadcast`,
  `store.applyEventsLocked`, `store.Apply`, `Cache.applyStorage`, `Cache.watch` (and its
  `applyErr` handoff predicate `watchP`), `Cache.getWatch`, `Cache.get`'s error branch,
  `Cache.watchEvents`' first disjunct; `WatchResponse.Err`: `□ (errStrOk resp.closeErr' -∗
  errStrOk err)`.
- `New`/`newCache`: `isEtcdKVE` instead of `isEtcdKV`, and items 8, 9, 11, 12 above.
- New callee hypotheses (statements unchanged): `validateGet`, `validateWatch` (`wp_Errorf`),
  `conditionalProgressRequestor.run` (`wp_Printf`), `getWatchLoop` (`wp_Printf`,
  `wp_DurStr`), `watchEvents` (`wp_ctxErr`), `rangeKeys` (`hCtxErr`, `hErrorf`; dropped again in
  the merge into the request path, 2026-10-13),
  `Mutex.tryAcquire`, `Election.Campaign` (`fmt.SprintfNamed.spec`).

Gates: `lake build` (3654 jobs), `etc/goose.py --check`, every `gen-link.py` mode reproduces,
`etc/tcb-report.py --check`: 98 axioms (93 + items 1–5), 9 sorries (Perennial's renamed
`initialize'` sorries); every collection's `--check` (updated: apply, cache, concurrency, mvcc,
txn, register).

## The request path (`v3rpc`, `v3_server.go`, `wait`, `idutil`)

Plan: `notes/decisions.md`, "The request path: raft as a contract, the wait registry, the checks
as the premises' discharge" (units 0, then 1 and 2 in parallel, 3, then 4 optional).

### Unit 0: translation and scaffolding (2026-10-12)

Branch `rp-u0` (worktree `/shared/etcd-grove-rp0`, off `lean` at `18d71cc20`; Perennial
`5857c495a` as a path dependency, `.lake/manifest-5857c49.json`).
- **Translation**: a new package `server/v3/etcdserver/api/v3rpc` (`v3rpc.toml`): `key.go`'s
  `NewKVServer`, the six handlers (`Range`, `RangeStream`, `Put`, `DeleteRange`, `Txn`,
  `Compact`), the seven checks, `headerFillingRangeStream.Send`, `header.go`
  (`newHeader`, `fill`, `fillWithoutRevision`) and `util.go`'s `togRPCError`, with bodies; the
  error map `toGRPCErrorMap` (a map literal over sixty errors of seven packages), the other
  services and `metrics.go` names only (19 of the package's 116 functions translated, 269 of
  1722 lines). `etcdserver.toml` adds `v3_server.go`'s `Range`, `Put`, `DeleteRange`, `Txn`,
  `raftRequest`, `doSerialize`, `processInternalRaftRequestOnce`, `getRequestType`,
  `newHeader`, `AuthInfoFromCtx`; `tracing.go`'s `first*`; `util.go`'s `exceedsRequestLimit`,
  `isPriorityRequest`; `server.go`'s `KV`, `AuthStore`, `Cluster`, `getAppliedIndex`,
  `getCommittedIndex`, `getTerm`, `Term`, `Leader`, `FeatureEnabled`, `parseProposeCtxErr`;
  `interface.go`'s `LinearizableReadNotify`; `RaftKV`; and `raft.Node`'s `Propose`. `pkg/wait`
  (`New`, `list.Register`/`Trigger`/`IsRegistered`, `waitWithResponse`) and `pkg/idutil`
  (`NewGenerator`, `Next`, `lowbit`) get bodies; `server/v3/features` is new (names only, the
  two feature constants); `etcdserverpb.toml` adds the getters the path calls and
  `KV_RangeStreamServer`; `codes.Unknown` translated. No Gooseable change (the pin
  `bc8b52a50` translates as is).
- **What Goose needed**: (1) a method promoted through two embeddings ending in an interface
  (`raftNode` embeds `raftNodeConfig` embeds `raft.Node`) is emitted as `MethodUnfold` wrappers
  only if both levels are listed (`raftNode.Propose`, `raftNodeConfig.Propose`); (2)
  `RaftKV` names `etcdserverpb.KV_RangeStreamServer`, an alias of the generic
  `grpc.ServerStreamingServer[...]`: an untranslated alias is emitted without the `.ty` its
  users name (a known gap), so it is listed, with `google.golang.org/grpc` imported, which
  resolves the package's other stream aliases too (more of `etcdserverpb` translated, nothing
  else changed); (3) `codes.Unknown` must be translated for `status.Error`'s `≠ OK` premise.
  Package instances: grpc's moved before `etcdserverpb`'s (cache `Base`), `log`'s (`wait`
  imports it), `features`' and `strconv`'s (`BaseApply`), and the server's package fact is no
  longer `True`: `srvInit` (the metrics `requestDurationSec`, `proposalsFailed` with
  `counterSpec`, `proposalsPending` with `gaugeSpec`; `traceutil.Tracer`; `srvErrVars`, the
  error variables the path returns as `errors.New` errors). Every existing proof built unchanged.
- **The checks** (`v3rpc/Defs.lean`, pure): `ReqOp` (a `RequestOp` as the checks read it: the
  txn package's `OpFull` for a range, put, delete, since a `TxnOp` forgets the put's value and
  lease), each check a function to its first error (`rangeCheck`, `putCheck`, `deleteCheck`,
  `opCheck`/`opsCheck` with the per-level budget `n - txnWidth`, `txnCheck`; `CheckErr.var` the
  `rpctypes` variable), the `*Ok` predicates ("returns `nil`"), and `checkIntervals` as the code
  computes it (`ivCheck` = `ivNest` then `ivFinish`, over `adt.ivlCmp`: a `"\x00"` range end is
  the empty interval `[k, "\x00")`; `Union` filtered by `["\x00", +∞)`). `ReqOp.toTxnOp` gives the
  txn package's model. **`intervalsOkCheckStmt`** (a `Prop`, unit 1 proves it): a branch passing
  the check, run by `txn.srvOps`, has distinct put keys none of which is deleted
  (`keys_nodup_iff_check`'s condition), **under two exclusions**: no from-key delete
  (`noFromKeyDelL`, the known finding) and no nested put deleted by a later sibling
  (`siblingSafeL`, new finding below); false without either. The range end is the denotation
  (`rangeEndOf`), the request's bytes off the wire; an empty non-nil `RangeEnd` (never off the
  wire) is unit 1's premise.
- **The request vocabulary** (`etcdserver/InvRequest.lean`):
  - the raft contract: `ServerRaftNames` (`cLog`, `fresh`, `props`, `committed`), `srvCLog`,
    `srvPropFresh`, `srvDeposited`, `srvIsProp`, `srvPropTok`, `srvPropAu`, `srvPropArg`,
    `srvPropRes` (the register's `propArg`/`propRes`/`propAu`, namespace `srvRaftN`);
    `raftPropose γ n` := `∃ ni, n = ok ni ∗ □ ∀ ctx cd data_sl data Q fresh, {{ txnCtx ctx cd ∗
    data_sl ↦*□ data ∗ srvPropArg γ data Q fresh }} ni.Propose(ctx, data_sl) {{ err; srvPropRes γ
    data Q fresh }}`; `srvRaftNode s γ` (the `s.r.raftNodeConfig.Node` field and the contract);
    the apply side `batchCommitted γ γi cs ms` := `srvCommittedLb γ (cs ++ batchData ms) ∗ [∗list]
    d ∈ batchData ms, srvDeposited γ d ∗ (∀ rq id, irrDecode d = some rq ∧ irrId rq = some id -∗
    idClaim γi id d)`, with `batchData` and `appendFirstOcc` (the client log's meaning);
  - ids: `IdNames` (`cred`, `issued`, `slot`), `idCred γi n` (`◯ n : Auth Nat`), `idFresh γi id`
    := `idUnclaimed γi id ∗ idSlot γi id`, `idClaim γi id d` (persistent, agreeing), `idIssued pfx
    s0 k id`, and `idGen γi g` := the `prefix` field, `s0 < 2^48`, and `inv idN (∃ k I S, suffix ↦
    s0 + k ∗ ● (2^48 - 1 - k) ∗ k ≤ 2^48 - 1 ∗ both ghost maps' authorities, their domains the
    issued ids)`;
  - the wait: `isWait w γi R` (Register `{{ idSlot γi id ∗ □ R id Ψ }} → {{ ch; ∃ γh, waitRecv γh
    ch Ψ }}`; Trigger `{{ (∃ γh, x = nil ∗ handoffConsumer γh false) ∨ waitTrig R id x }}`;
    IsRegistered a boolean), `waitRecv γh ch Ψ` (a handoff channel of `waitVal γh Ψ x := Ψ x ∨ (x =
    nil ∗ handoffConsumer γh false)` and its consumer token), `waitTrig R id x := ∀ Ψ, R id Ψ -∗ Ψ
    x`, `resultΨ E rq x` := `∃ ar, x = *apply.Result ar ∧ ar ≠ nil ∗ ∃ y y' out, applyStep rq true
    y y' out ∗ applyResultIs rq true y.log ar out ∗ idxCert E.γ.idx y'.log`, `reqWaitR γi E id Ψ`
    := `∃ d rq, idClaim γi id d ∗ irrDecode d = some rq ∧ Ψ = resultΨ E rq`, `waitInv w γi E :=
    isWait w γi (reqWaitR γi E)`. The apply package's `waitOk` (in `srvFieldsAt`) stays until unit
    2 replaces it;
  - reads: `ReadNames`, `appliedAtLeast`, `committedAtLeast` (mono-nat lower bounds),
    `readIndexOk γr c := ∃ ci₀, c ≤ ci₀ ∗ appliedAtLeast γr ci₀`, `isRead r γr`
    (`LinearizableReadNotify` with `committedAtLeast γr c` returns `nil` only with `readIndexOk γr
    c`); the auth store's request side `isReqAuth st` (`AuthInfoFromCtx`/`FromTLS`: `authInfoOpt`);
    `isRaftKV kv s` (the `kv` field is `*EtcdServer` `s`).
- **Axioms** (22 new, each `Spec/`+`Proof/`; justification in each Proof file):
  `traceutil.Tracer.Start` (on the tracer the package variable holds: a `txnCtx` of the input's
  descriptor with other values, and a span), `trace.WithAttributes`,
  `attribute.String`/`Int64`/`Bool`/`Int` (span attributes: no effect the model sees),
  `strconv.FormatBool` (Perennial's `strconv` is names-only), `time.Duration.Seconds` (a float),
  `time.Time.After` (some boolean), `prometheus.HistogramVec.WithLabelValues` (an observer whose
  `Observe` returns: `prometheus.observerSpec`), `traceutil.Trace.LogIfLong`/`GetStartTime`/
  `SetStartTime`/`InsertStep` (non-nil trace; returns), `txn.WarnOfExpensiveReadOnlyRangeRequest`/
  `TxnRequest` (loggers, as `WarnOfExpensiveRequest`), `status.Errorf` (non-nil for a code not
  `OK`), the server's `isConnectedSince`/`isConnectedToQuorumSince` (transport queries, some
  boolean), `config.ServerConfig.ReqTimeout` (some duration), `membership.RaftCluster.ID` (as
  `Members`), and `proto.MarshalIRR` (`proto.Marshal` of an `InternalRaftRequest`: an error, or
  bytes `irrDecode` reads as `rq'` with `irrWireOf rq rq'`: the same id, header and kind, and
  `rq' = rq` when no KV range end is `[0]` (`irrNoZeroEnd`), the model's ambiguity of `"\x00"` and
  an empty non-nil slice; `apply.withHeader` for unit 2). Generalized, not new:
  `trace.isSpan` (`SpanFromContext`'s) adds `AddEvent`/`RecordError` (mvcc's
  `watchStream.Watch` pattern takes the extra conjunct); `context.WithValue` takes
  `traceutil.StartTimeKey` and returns, for any `txnCtx` of the parent, one of the child at the
  parent's descriptor with other values, now at `HasLC.hasLC` (the backend's `Authenticate`
  adapted: two patterns). Not axioms: `context.WithTimeout` (Perennial's `wp_WithTimeout`),
  `errors.Is` (Perennial's), `status.Error` (existing), the components (contracts above).
- **adt, for the mvcc session**: `Spec/go_etcd_io/etcd/pkg/v3/adt/intervalTree__Union.lean`
  (`t.Union(t', ivl)`: inserts, in some order, the entries of `t'` that `stab (b, e)` selects;
  `t'` unchanged; no newness premise), listed `intervalTree__Union: ?` in
  `etc/link-lean-first-adt.txt` (the adt Link imports its spec; the adt collection unchanged, 0
  axioms). And a caveat: `intervalTree.Insert`'s spec requires the interval to be new
  (`(b, e) ∉ L.map Prod.fst`), but `checkIntervals` inserts the same interval twice when a
  transaction deletes the same range twice (a legal request): unit 1 needs an `Insert` without
  that premise (the model's `ivtInsert` already places a duplicate after the equal ones).
- **Links**: `gen-link.py --v3rpc` (namespace `v3rpc`, the package's assumptions, `EtcdDeps` among
  the spec roots, `EXTRA_IMPORTS` for the package's `Base` while no proof of it is linked),
  `etc/link-lean-first-v3rpc.txt` (`status_Error`, `status_Errorf`, `errors_Is`; the server's
  `MemberID`, txn's `IsDefaultOrdering`/`HasRevisionFilters`, adt's intervals as `@`; the
  package's 19 functions commented out with their callees), the server's list with the 21
  server-side axioms linked and the request path's 27 functions and `wait`/`idutil`'s commented
  out; `v3rpc/Results.lean` (skeleton: prints the three linked results' axioms) and the request
  path's section in the server's `Results.lean`; `etc/tcb-collections/v3rpc.txt`.
- **The plan's suspects**: (1) `wait.Register`'s dup-id panic: `tsLen = 40`, `cntLen = 8`,
  `suffixLen = 48`; within a process a duplicate needs `2^48` ids (the budget premise,
  `idGen`); but across members the prefix is `uint16(memberID)`, so two members whose ids agree
  in the low 16 bits collide once one's counter reaches the other's timestamp range: a finding
  (`issues/etcd-request-id-member-prefix.md`, reproduced) and a premise of the raft contract's
  apply side. (4) `header.fill` replaces only a `0` revision; every successful response has a
  revision ≥ 1 (mvcc's `currentRev` starts at 1; a put/delete/txn header is the write's or the
  read view's revision, a range's the store's current one), so `rev()` is never called on a
  success path: no hazard. (5) `exceedsRequestLimit` is called only by
  `processInternalRaftRequestOnce`: reads (`doSerialize`) are never limited; with
  `PriorityRequest` (alpha, off by default) a `LeaseRevoke` gets twice the gap. No bug. (7)
  `checkTxnRequest`'s budget is per level (`maxTxnOps - opc` for the nested ones): nesting
  exceeds `--max-txn-ops` in total (39 operations pass `maxTxnOps = 9`), against the flag's text
  ("in a transaction"): `issues/etcd-max-txn-ops-nested.md` (documentation). (2), (3), (6) read
  as the plan says (for units 2 and 3).
- **Findings**: `issues/etcd-txn-check-intervals-sibling.md` (`checkIntervals` accepts a put in
  a nested transaction and a delete of the key in a later sibling nested transaction, while the
  flat and the reversed orders are rejected; reproduced; no crash found: a put and a delete of
  one key in a revision), `issues/etcd-max-txn-ops-nested.md`,
  `issues/etcd-request-id-member-prefix.md`. The reproductions are Go tests run with `go test
  -overlay` against `/shared/etcd` (no change to the checkout).
- **What the plan got wrong, for units 1 and 2**: the checks cannot be stated over `TxnOp`
  (the put check reads what `putTxnOp` forgets): `ReqOp`; `intervalsOk → nodup` needs the sibling
  exclusion too; `proto.Marshal`'s round trip is up to the model's `[0]` ambiguity
  (`irrWireOf`); the wait needs a registration condition, not a registry of predicates, and the
  apply thread's knowledge of the proposer's request goes through cluster-wide id claims (a
  premise on member ids); `context.WithValue` needed a descriptor (the `Put`/`Txn` contexts);
  `RaftCluster.ID` and the transport queries were missing from the plan's axiom list; `Insert`'s
  newness premise (above). `exceedsRequestLimit`/`getRequestType` read many fields
  (`r.LeaseRevoke`, ...): their specs take `internalRaftRequestIs`.
- **Gates**: full `lake build` clean (2962 jobs; no `sorry` of ours: the only ones are the raft
  `Init.lean` stubs of the baseline and the generated axiomatized-type instances);
  `goose.py --check --project etcd --perennial /shared/perennial-5857c49` passes; every
  `gen-link.py` mode reproduces its `Link.lean` (`--v3rpc --apply --server --mvcc --txn --leasing
  --cache --recipes --concurrency --register --adt`; `--apply`'s regenerated: `context.WithValue`
  moved to the `hasLC` section; `--adt`'s: Union's spec imported); `tcb-report.py --check
  --update`: 66 → 88 axioms, 9 sorries, the diff exactly the 22 above; collections: server 19 →
  40 (the 21 server-side axioms), v3rpc 2 (new: `status.Error`, `status.Errorf`), the others
  unchanged (apply 32, txn 18, mvcc 12, cache 10, concurrency 12, recipes 11, leasing 8, register
  1/9, raft 1, adt 0, btree 0); `verified-code.py --reuse --package …/api/v3rpc`: 116 functions,
  0 verified, 19 translated (269 of 1722 lines; `key.go` 15 functions, 236 lines);
  `--package …/etcdserver`: the `etcdserver` package 279 functions, 11 verified, 5 assumed (the
  two `isConnected*` new), 27 translated (`v3_server.go` 10, `tracing.go` 4); `pkg/wait` 8
  translated, `pkg/idutil` 3; etcd 577 of 3599 functions verified (unchanged), 33 assumed.

### Unit 1: the checks and the handlers (2026-10-12)

Branch `rp-u1` (worktree `/shared/etcd-grove-rp1`, off `lean` at `f9f133010`, unit 0's merge;
Perennial `5857c495a` as a path dependency). Every function of `key.go` but `kvServer.RangeStream`
and `kvServer.Compact`, `header.go`'s three and `util.go`'s `togRPCError` specified
(`Spec/.../api/v3rpc/`) and proved (`Proof/.../api/v3rpc/`), linked (`gen-link.py --v3rpc`);
the results in `v3rpc/Results.lean`.
- **The checks** (each returns `nil` iff its pure check of `Defs.lean` does, else the `rpctypes`
  error it names, `checkRes`): `checkRangeRequest` (over the sort-name maps' contract, a new
  package fact `sortNameMaps`: `RangeRequest_SortOrder_name`/`SortTarget_name` hold exactly the
  enumerations' values), `checkPutRequest`, `checkDeleteRequest`, `checkRangeStreamRequest`
  (`streamOk`: the default sort, no revision filter; the error a non-nil `status` error),
  `checkRequestOp` ↔ `checkTxnRequest` (one Löb induction, `CheckLemmas.lean`, over the
  checked request `reqOpIs`/`txnReqIs`, `InvKV.lean`), and `checkIntervals` over the interval
  tree's contract (pending, the mvcc session's: hypotheses of it and of `kvServer.Txn`): `nil`
  iff `ivCheck` says so, the map's keys the computed puts (as a set: the map ranges in any
  order), the tree's intervals a permutation of the computed deletes (`Union` inserts in
  `Visit`'s order); its recursion by Löb induction (`checkIntervals.lean`, 1135 lines).
- **`check_gives_nodup`** (`CheckNodup.lean`, pure, `intervalsOkCheckStmt_holds`): a branch
  passing `checkRequestOp` and `checkIntervals`, with no from-key delete (`noFromKeyDelL`) and
  no nested put a later sibling deletes (`siblingSafeL`), run by the server, puts distinct keys
  none of which it deletes; `checkIntervals_nodup` (Results): with `DelsPresent`, the changes'
  keys are distinct (`keys_nodup_iff_check`). The two exclusions are the code's findings
  (`etcd-txn-delete-then-ignore-put`, `etcd-txn-check-intervals-sibling`); **unit 0's statement
  was false** without the key check (`intervalsOkNoKeysStmt_false`: the affine order reads `""`
  as +∞, so a put and a delete of the empty key pass `checkIntervals`); the handler runs
  `checkTxnRequest` first, so the premise costs nothing.
- **`checkRequestOp_nonempty`** (`CheckPure.lean`): a transaction passing `checkTxnRequest` has
  no empty `RequestOp` at any depth (`toTxnOps` is defined): the txn package's
  `etcd-txn-empty-requestop` precondition discharged at the API; `checkTxnRequest_ok` the pure
  characterization (width within the budget, comparison keys non-empty, every op at the budget
  less the width). For units 2/3: `reqOpsIs_requestOpsIs`, `txnReqIs_txnRequestIs`
  (`CheckLemmas.lean`): a checked request as the txn package's `requestOpsIs`/`txnRequestIs`.
- **The server as the handlers call it** (`InvKV.lean`: `raftKV s A`, persistent, in
  `kvServerIs`): the triples of `*EtcdServer`'s `Range`, `Put`, `DeleteRange`, `Txn` (on checked
  requests), `KV().Rev()`, `Cluster().ID()`, `MemberID`, `Term`, `Leader`, over parameters
  `A : KVAns GF` (`call`, `ok`, `err`, `revR`) that units 2 and 3 instantiate and prove (unit 0's
  `isRaftKV`, the `kv` field's value, is kept; `kvServerIs` states the field). For `Put`:
  `{{ A.call ctx ∗ txn.putRequestIs r o ∗ ⌜putReqOk o⌝ }} s.Put(ctx, r) {{ resp err; kvAnswer A
  (.put o) (&resp.Header) resp err }}`, `kvAnswer` := `(err = nil ∧ resp ≠ nil ∗ ∃ h r, Header ↦□
  h ∗ hdrW h ∗ hdrRevIn A.revR h r ∗ A.ok q resp h r) ∨ (resp = nil ∗ srvErrIs err ∗ A.err q err)`;
  `Txn`'s precondition `txnReqIs r cs ts es ∗ ⌜txnReqOk n cs ts es ∧ intervalsOk ts ∧ intervalsOk
  es⌝` (some budget `n`). The handlers' answer (`kvOut`): the check's error (and `A.call` back),
  or the server's answer with the header filled (`hdrFilled h cid mid`: the header's ids, some
  term and leader; the revision `r` kept if not `0`, else `rev()`'s, `hdrRevOut`), or `nil` and a
  non-nil error (the server's through `togRPCError`).
- **What units 2/3 must provide that the apply side does not have yet**: the response header's
  `ClusterId`, `MemberId`, `RaftTerm`, `LeaderId` owned (`hdrW`; the txn package's
  `putResponseIs` and the others keep only the revision, read-only), an error `togRPCError` can
  take (`srvErrIs`: `applyErrIs`, a safe map key, an `Error()` that returns), and the getters'
  triples.
- **The header and `togRPCError`**: `newHeader` (the closure `rev` over the persisted `s`),
  `fill`/`fillWithoutRevision` (a `nil` header panics: `hdrW` says it is not), `NewKVServer`
  (`kvServerIs`). `togRPCError`: `errors.Is` at `context.Canceled` (Perennial's `errors.wp_Is`;
  that `Canceled` is a pointer error is a v3rpc package fact, `ctxCanceledPtr`, since `context`'s
  keeps only that it is a typed error), at `context.DeadlineExceeded` (**a new axiom**,
  `errors.IsDeadlineExceeded`: an empty struct, which `wp_Is` does not take), the error map
  (`SafeMapKey` of the error), `status.Error(codes.Unknown, err.Error())`.
- **Not verified**: `kvServer.RangeStream` (the server's `RangeStream` is out of the model) and
  `kvServer.Compact` (compaction is out of the model, as in the apply package; and
  `AuthAdmin.isPermitted`). `headerFillingRangeStream.Send` is, over the wrapped stream's
  contract (`streamSendOk`).
- **Translation** (`goose.py`): `etcdserver/api.Cluster` (`api.toml` imports `types`,
  `membership`, `semver`; its package instance moves after theirs, `apply/Base.lean`),
  `etcdserverpb.KVServer` and `RangeStreamResponse` (`etcdserverpb.toml`; with `context`
  imported, the package's other service interfaces too): names-only interfaces do not reduce a
  method call or a conversion. Every existing proof built unchanged.
- **adt, for the mvcc session**: `Spec/go_etcd_io/etcd/pkg/v3/adt/intervalTree__InsertAny.lean`
  (`Insert` without the newness premise: `checkIntervals` inserts one interval twice when a
  transaction deletes the same range twice; the code adds a second node after the equal ones,
  as `ivtInsert` does), `intervalTree__InsertAny: ?` in `etc/link-lean-first-adt.txt`; `ownIvt`'s
  documentation ("distinct intervals") must allow duplicates, as `Union`'s spec already does.
- **A premise**: `checkIntervals`' deletes are as off the wire (`reqOpsWire`, `txnReqWire`: a
  `RangeEnd` is `nil` or not empty, as protobuf-go decodes it), unit 0's announced premise: the
  code reads an empty non-`nil` range end as a point, the model (as mvcc) as no upper bound.
- **Where the plan (and unit 0) was wrong**: `intervalsOkCheckStmt` needs the key check (false
  without it, above); `errors.Is(err, context.DeadlineExceeded)` is not Perennial's (`wp_Is` takes
  pointer targets: an axiom), and `context.Canceled`'s pointer error is not in `context`'s package
  fact (a v3rpc fact); `newHeader` and `NewKVServer` go through two names-only interfaces
  (`api.Cluster`, `pb.KVServer`: translated), and `Send` through an untranslated message
  (`RangeStreamResponse`: translated); `header.fill` writes the response header, so the apply
  side must hand the header's id fields over owned (`hdrW`: not in the txn package's response
  predicates); `checkIntervals` needs `Insert` of a present interval (`InsertAny`) and the
  wire premise on range ends; `store.Rev` is not called on any success path (the header's `rev()`
  runs only for a `0` revision), so the handlers take the KV's `Rev()` as a contract (`A.revR`),
  not `store.Rev`'s spec.
- **Gates**: full build clean (3003 jobs; no `sorry` of ours); every `gen-link.py` mode reproduces;
  `goose.py --check` up to date; `tcb-report.py --check`: 89 axioms (88 + `errors.IsDeadlineExceeded`),
  9 sorries (the register's), baseline updated; collections all match, `v3rpc` updated to 3 axioms
  (`status.Error`, `status.Errorf`, `errors.IsDeadlineExceeded`; the interval tree's contract is a
  hypothesis, not an axiom); `verified-code.py --reuse --package …/api/v3rpc`: 116 functions, 15
  verified, 2 unfinished (`checkIntervals` and `kvServer.Txn`: they rest on the interval tree's
  pending contract), 2 translated (`RangeStream`, `Compact`), 159 of 1722 lines verified (`key.go`
  11 of 15 functions, `header.go` 3 of 3, `util.go`'s `togRPCError`); etcd 592 of 3599 functions
  verified (577 before), 6035 of 45570 lines, 9 unfinished.

### Unit 2: the wait protocol and the proposal path (2026-10-12)

Branch `rp-u2` (worktree `/shared/etcd-grove-rp2`, off `lean` at `f9f133010`; Perennial
`5857c495a` as a path dependency). Verified and linked (server's list): `pkg/idutil`
(`lowbit`, `NewGenerator`, `Generator.Next`), `pkg/wait` (`New`, `list.Register`/`Trigger`/
`IsRegistered`, `NewWithResponse`, `waitWithResponse.Register`/`Trigger`), and in the server
`processInternalRaftRequestOnce`, `raftRequest`, `Put`, `DeleteRange`, `parseProposeCtxErr`,
`AuthInfoFromCtx`, `AuthStore`, `FeatureEnabled`, `getAppliedIndex`, `getCommittedIndex`,
`exceedsRequestLimit`, `isPriorityRequest`, `getRequestType`, and etcdserverpb's
`PutRequest.GetKey`, `DeleteRangeRequest.GetKey`/`GetRangeEnd`. The apply thread's
`applyEntryNormal`/`apply`/`applyEntries` now trigger through the registry.
- **The ids** (`idutil/Defs.lean`, moved from `InvRequest.lean`): `idGen γi g` (its prefix's 48
  low bits are 0, its suffix a plain `uint64` updated by `atomic.AddUint64`, in an invariant with
  the credits' authority and the two ghost maps); `NewGenerator` allocates it with
  `idCred γi (2^48-1)`; `Next` with one credit returns `idFresh γi id` and the shape `pfx |
  ((s0 + j) & (2^48-1))`, `1 ≤ j < 2^48`. `lowbit(x, n) = x & (2^n - 1)` for `n ≤ 64`
  (Perennial's untruncated shifts: `MaxUint64 >> (64 - n)`, `0` for `n = 0`). Lemmas
  `idClaim_make`, `idClaim_agree`, `idClaim_unclaimed`, `idSlot_excl`.
- **The registry** (`wait/Defs.lean`, `wait/List.lean`): `isWait w γi γw R RD` is `New`'s
  contract, for any registration condition `R`. `Register(id)` takes `idSlot γi id ∗ □ R id Ψ`
  and returns `∃ γh, waitRecv γh ch Ψ ∗ waitRegd γw id γh.takenName` (a handoff channel of
  `waitVal γh Ψ x := Ψ x ∨ (x = nil ∗ handoffConsumer γh false)`, never closed without a send;
  `waitRegd`: a persistent element of the ghost map of every id ever registered). `Trigger(id,
  x)` takes `waitTrig R id x := ∀ Ψ, R id Ψ -∗ Ψ x`, or `x = nil` with a consumer token and the
  `waitRegd` naming it (the records agree on the token's name, so the `nil` the proposer sends
  carries its own token: a proposer that later received it would hold two tokens). `IsRegistered`
  takes and returns `RD`, the 64 shards' `RWMutex` reader slots (Perennial's `RWMutex` bounds
  readers; `New` returns `RD` once, the apply thread holds it). Each shard: a fractional lock
  invariant (`ownMap` and half a ghost map of the shard's ids) and an invariant with the other
  half and each registered id's resources (handoff, producer token, `□ R id Ψ`, `waitRegd`);
  the registered-ids invariant keeps every registered id's `idSlot` forever, so `Register`'s
  `log.Panicf("dup id")` is unreachable (two exclusive slots).
- **The server's condition** (`InvRequest.lean`): `reqWaitR γi E id Ψ` (the id claimed for
  data that decode to `rq`, `Ψ = resultΨ E rq`), `waitInv w ρ E := ∃ RD, isWait w ρ.ids ρ.wait
  (reqWaitR ρ.ids E) RD`; `resultIs E rq ar` (non-nil, `applyStep rq true y y' out`,
  `applyResultIs rq true y.log ar out`, `idxCert E.γ.idx y'.log`), `resultΨ` its interface value.
  `ReqNames` = `{raft, ids, wait}`.
- **The apply side**: `isServer s γ ci TM E ρ`, its
  fields with `waitInv` in place of `waitOk`; `srvApplyKV` holds the wait's reader (`apply.waitOk
  w RD ∗ RD`; the apply package's `waitOk` is now `IsRegistered` with `RD`, and `apply.Apply`
  threads `RD`). `applyEntryNormal` takes `entryWaitOk ρ E m` (a normal entry's data, decoding to
  a request with an id, claimed under that id) and proves `waitTrig` at both triggers: the
  registration's claim agrees with the entry's (`idClaim_agree`), so the expectation is `resultΨ`
  of the entry's request, met by `apply.Apply`'s post and `applyKV_idxCert`. `apply` takes
  `batchWaitOk` (also: a conf change's id `ccIdOf m.data`, from pbutil's restated spec, is no KV
  registration), `applyEntries` passes it. The `Trigger` inside `GoAttach`'s closure (the
  `ErrNoSpace` alarm path) is not verified: `GoAttach`'s axiom does not run its closure.
- **The proposer** (`InvProposer.lean`, `ProposerLemmas.lean`): `isServerReq s E ρ` (the
  request path's fields: generator, wait, raft node, the configuration's `MaxRequestBytes`,
  feature gate, `ClientCertAuthEnabled`, election ticks and tick length, the auth store, `done`,
  member id, the leader and index atomics, cluster, transport; the **mint** invariant: raft's
  fresh-token authority, each token of data claimed under their id; the **client-log**
  invariant: the other half of `srvCLog`, so the deposited update is the trivial one,
  `srvPropAu_trivial`, `Q = True`: the server does not linearize at raft's commit, its result
  comes through the wait). `srv_claim_mint`: claiming a fresh id for data that decode to a
  request with that id mints the data's fresh token.
- **`processInternalRaftRequestOnce`** (`request_handoff`): `∀ s E ρ ctx cd p rq, rq.id = 0 →
  {isPkgInit ∗ isServerReq s E ρ ∗ srvLeadTimeReader s ∗ idCred ρ.ids 1 ∗ context.isContext
  ctx cd ∗ irrNoHdrIs p rq ∗ ∃ h0, p.Header ↦ h0} s.processInternalRaftRequestOnce(ctx, p)
  {(res, err); srvLeadTimeReader s ∗ ((err = nil ∗ ∃ hm rq', ⌜irrWireOf (withHeader rq hm)
  rq'⌝ ∗ resultIs E rq' res) ∨ (res = null ∧ err ≠ nil ∗ srvMaybeDeposited ρ rq))}`. The proof:
  the request limit, `Next`, the header (auth info from `AuthInfoFromCtx`, joined), `Marshal`,
  the size limit, the claim and mint, `Register` with `resultΨ E rq'`, `WithTimeout`, `Propose`
  through the promoted wrappers to the raft contract (`srvPropArg … true`), then the `select`:
  the result (the handoff's receive: the `nil` disjunct contradicts the consumer token, a close
  without a send is `False`; the type assertion from `resultΨ`), the context (`Trigger(id, nil)`
  with the consumer token, `parseProposeCtxErr`), the stop; the three defers (gauge, cancel,
  metrics) at every return. `srvLeadTimeReader`: a reader slot of `s.leadTimeMu`, which
  `parseProposeCtxErr` read-locks (each request goroutine holds one: Perennial's `RWMutex`).
- **`raftRequest`**: success is `appliedOk E rq' resp` (dispatched, the apply package's
  `dispatchAnswer` with no error, `idxCert` of the log after); failure the apply's error
  (`appliedErr`) or the proposal's. **`Put`**, **`DeleteRange`** (`put_applied`,
  `deleteRange_applied`): `(resp, nil)` is `putOutcomeIs x.log op resp nil o` of the request
  with the server's header (`withHeader (irrPut op) hm`, the encoding exact for a put), resp.
  `deleteOutcomeIs x.log op' …` of the decoded request's delete `op'` (`op` unless its range end
  is `[0]`), dispatched at `x` to `x'` with `idxCert E.γ.idx x'.log`; an error is the apply's or
  the proposal's (`put_err`: the right disjunct). `put_applied_model`, `deleteRange_applied_model`
  (pure): through `alarmChain ns cr`, `alarmPut`/`alarmDelete` (`putModel`/`deleteModel` or a
  layer's rejection) and the outcome's log (`apply.apply_kv`).
- **Trust boundary**: two new axioms, `context.ValueStartTime` (a context's `Value` at
  `traceutil.StartTimeKey`: `nil` or a time) and `errors.IsCtxErr` (`errors.Is` of a context's
  error at `Canceled`/`DeadlineExceeded`: no error tree for a context's `Err`; unit 1's
  `errors.IsDeadlineExceeded` takes a tree, which `cctx.Err()` does not have: the merge should
  keep both or generalize unit 1's). Restated (stronger, same names): `context.WithValue` and
  `traceutil.Tracer.Start` keep `isContext`; `time.Duration.Seconds` returns a word
  (Perennial's float64: a `let` of an abstract `val` does not step); `pbutil.MustUnmarshalMessage`'s
  conf-change id is `ccIdOf bs`; `isServerReq` states `&s.Cfg ≠ null` (for `ReqTimeout`).
  Translation: raft's `Node` (importing `context`) and `None`, rafthttp's `Transporter`
  (importing its method set's packages), otel's `Tracer` (importing `context`) are interfaces /
  constants now, not axiomatized types (the path loads `s.r.Node`, `s.r.transport`,
  `traceutil.Tracer` and compares with `raft.None`). A local instance `NotInterface go.int64`
  (Perennial states it only of the type constructors) lets `time.Duration`'s methods resolve.
- **Not done** (for unit 3): `Txn` (one function: its read-only branch is the read side; its
  span attributes call the `first*` loops over the requests' oneofs; `s.Logger()` needs a reader
  slot of `s.lgMu` too), `Range`, `doSerialize`, `newHeader`. For unit 4: `batchCommitted`
  from the raft loop gives `entryWaitOk` of normal entries; a conf change's needs typed claims
  (`configure` claims its id for the conf change). **Gap for the handlers** (unit 1's `raftKV`):
  the answers' header fields `ClusterId/MemberId/RaftTerm/LeaderId` are not owned in the apply
  package's response predicates (`txn.putResponseIs` keeps only `Revision`, read-only), and the
  errors are `applyErrIs` without `SafeMapKey`/`Error()`: `srvErrIs` needs both; a change to the
  txn/apply response predicates (own the four fields from `newHeader`) and to the error facts.
  `resultΨ` admits a `SkipRangeExecution` run of a transaction (`IsRegistered` is "some boolean").
- **Where the plan moved**: the registry's `Trigger(id, nil)` needs the registration's record
  (`waitRegd`) to name the consumer token; `IsRegistered` needs a reader slot (the apply
  package's `waitOk` changed, not `waitInv ⊢ waitOk`); the channel must exclude a close without
  a send (`Wc = False`); the deposited update is trivial (`Q = True`: the result comes through
  the wait); the fresh token is minted from the id's claim (`srvMintInv`); the conf-change trigger
  needed `ccIdOf`; the `Value`/`Is` axioms, the translations above, `Seconds`' word, the reader
  slot of `leadTimeMu`, the `Cfg` non-nil fact were not in the plan.
- **Gates**: full `lake build` clean (3024 jobs; no `sorry` of ours: the request
  path's proofs were checked for `sorryAx` dependencies, see the `TypeRepr` note below); every
  `gen-link.py` mode reproduces (`--server` regenerated: 94 results; `--apply --mvcc --txn
  --v3rpc --leasing --cache --recipes --concurrency --register --adt` unchanged); `goose.py
  --check --project etcd --perennial /shared/perennial-5857c49` passes (after the three
  translation changes); `tcb-report.py --check --update`: 88 → 90 axioms (`context.ValueStartTime`,
  `errors.IsCtxErr`), 9 sorries; collections: server 40 → 44 (the two, and `trace.SpanFromContext`,
  `context.WithValue` now reached), the others unchanged (apply 32, txn 18, mvcc 12, cache 10,
  concurrency 12, recipes 11, leasing 8, register 1/9, raft 1, adt 0, btree 0, v3rpc 2);
  `verified-code.py --reuse`: etcd 577 → 600 of 3599 functions (6177 of 45570 lines);
  `pkg/v3/wait` 7 of 12 (46 of 77 lines; `waitWithResponse.IsRegistered` and `WaitTime`'s are
  not), `pkg/v3/idutil` 3 of 3; the `etcdserver` package 11 → 24 of 279, 5 assumed
  (`v3_server.go` 6 of 49, `server.go` 16 of 109). **`TypeRepr`**: a proof that steps
  `StructFieldRef` on `EtcdServer`, `ServerConfig`, `raftNode` or `raftNodeConfig` without the
  high-priority `TypeRepr` instances (`InvServer.lean`, `InvProposer.lean`) reaches the `sorry`
  instances of the structs' axiomatized field types (`TLSInfo`, `URLs`, `DiscoveryConfig`,
  `Storage`) through their `IntoValTyped`: the first TCB check caught it.

### Merge 1/2 (2026-10-12)

Units 1 (`rp-u1`, merged into `lean` at `ea3ae885d`) and 2 (`rp-u2`, 10 commits
`f9f133010..35a9e2cfe`) ran in parallel off unit 0's merge `f9f133010`; unit 2 merged into
`lean`. Built with `lake build --packages=.lake/manifest-5857c49.json` (3065 jobs).
- **Conflicts** (notes and the baseline only): `notes/STATUS.md` (the "Last updated" line: unit
  1's items, then unit 2's, then the common history; the request-path section keeps both units'
  subsections, unit 1's first), `notes/decisions.md` (both units' entries), `etc/tcb-baseline.txt`
  (the union: `errors.IsDeadlineExceeded`, `errors.IsCtxErr`, `context.ValueStartTime`). Without
  conflict: the link lists, the collections, the Goose configurations (unit 1 `etcdserverpb`,
  `etcdserver/api`; unit 2 raft v3.7, `rafthttp`, otel's `trace`: disjoint), the server's and
  v3rpc's `Link.lean`. `etc/goose.py --check` passed without regenerating (no generated file
  conflicted); every `gen-link.py` mode (`--cache --concurrency --server --register --leasing
  --recipes --mvcc --txn --apply --adt --v3rpc`) reproduces its `Link.lean`.
- **The build after the merge** was clean, but `tcb-report.py --check` found 8 new `sorry`s
  (the `IntoValTyped`/`TypedPointsto` instances of `TLSInfo`, `URLs`, `DiscoveryConfig`,
  `Storage`), all reached by unit 1's `v3rpc.wp_NewKVServer`: unit 2's `InvRequest.lean` no
  longer imports `InvApplier` (and through it `InvServer`'s high-priority `TypeRepr` of
  `EtcdServer`), so `NewKVServer` found `TypeRepr` through `EtcdServer`'s `IntoValTyped` (unit
  2's `TypeRepr` note, from the other side). Fixed by importing `InvServer` in `v3rpc/InvKV.lean`.
- **Two `errors.Is` axioms, kept**: `togRPCError`'s error is any error the applier returns, known
  only by its error tree (`applyErrIs`), not a context's (`isTypedErr`), and `parseProposeCtxErr`'s
  is `cctx.Err()`, a typed context error with no error tree: neither statement's premise holds at
  the other's use, and one axiom covering both would be their disjunction.
- **Gates**: `tcb-report.py --check` 91 axioms (88 + `IsDeadlineExceeded`, `IsCtxErr`,
  `ValueStartTime`), 9 sorries (the register's), baseline unchanged from the union; every
  collection matches with no update (server 44, v3rpc 3, apply 32, txn 18, mvcc 12, cache 10,
  concurrency 12, recipes 11, leasing 8, register 1/9, raft 1, adt 0, btree 0);
  `verified-code.py --reuse`: etcd 615 of 3599 functions verified (6336 of 45570 lines; 592 and
  600 on the two branches, no overlap), 9 unfinished, 33 assumed; under `server/v3/etcdserver` 158
  of 969 (the `etcdserver` package 24 of 279, `v3rpc` 15 of 116); `pkg/v3/wait` 7 of 12,
  `pkg/v3/idutil` 3 of 3.
- **For unit 3** (the read side, and discharging unit 1's `raftKV s A` from unit 2's `Put`/
  `DeleteRange`): the header gap (`hdrW`: the handler fills `ClusterId`, `MemberId`, `RaftTerm`,
  `LeaderId`, so they must reach it owned; `txn.putResponseIs` and the apply answers keep only
  the revision, read-only) and the error gap (`srvErrIs` needs `SafeMapKey` and an `Error()` that
  returns, which `applyErrIs` does not give) are both open; see the two units' notes above.

### Merge of `origin/lean` (2026-10-12): the raft wrapper, build performance, the iframe race

`origin/lean` at `698b8c9cb` (merge base `18d71cc20`) into `lean` at `11ab1e6e7`: branches
`server-raft` (the server's raft wrapper, "etcd's server: the raft wrapper" below), `proof-perf`
("Build performance") and `flaky-iframe` ("Parallel elaboration and tactic state"); Perennial
`5857c495a` on both sides. Merge commit `9351c6192`.
- **Conflicts**: the Goose configurations `etcdserver.toml`, EtcdDeps' `raft/v3.toml`,
  `rafthttp.toml` (the union: raft.go's functions and v3.7's `IsEmptySnap`/`IsEmptyHardState`/...;
  the request path's entry points, `raft.Node`'s `Propose`, `None`, `Transporter`); the
  generated `Code/.../etcdserver.lean` and EtcdDeps' `raft/v3.lean`, regenerated with
  `goose.py` (exactly the union: no line in neither side; the dropped lines are axioms now
  translated); `etc/link-lean-first-server.txt` (the raft wrapper's 26 entries, then the request
  path's); the server's `Link.lean` (regenerated); `etc/tcb-collections/server.txt` (union);
  `apply/Base.lean` (the `api` instance after `membership`, ours; `storage` after `raftpb`,
  theirs); the notes (both sides' sections; the "Last updated" line: ours' items, theirs', the
  common suffix).
- **The server's package fact**: both sides replaced `srvInit` (`True` at the base): the raft
  wrapper with five metrics (`hasLeader`, `isLeader`, `proposalsCommitted` gauges with
  `gaugeSetSpec`, `leaderChanges`, `heartbeatSendFailures` counters), the request path with its
  metrics, tracer and error variables. Now `srvInit := srvRaftInit ∗ srvReqInit`, all three
  abbreviations (`srvRaftInit_persistent` kept); six proofs' `icases` patterns take the pair
  (`⟨⟨raft wrapper's⟩, -⟩` in `raftNode.start`/`processMessages`, `⟨-, ⟨request path's⟩⟩` in
  `Put`, `DeleteRange`, `processInternalRaftRequestOnce`, `parseProposeCtxErr`).
- **`Results.lean`**: `v3rpc/Results.lean` adopts `proof-perf`'s `set_option pp.fullNames true`;
  every `Results.lean` now has it.
- **`TypeRepr`**: no duplicate high-priority instance (the raft wrapper declares none of
  `EtcdServer`/`raftNode`/`raftNodeConfig`; ours stay in `InvServer`/`InvProposer`), and the TCB
  check found no new `sorry`.
- **Gates**: the build clean on the first run (3115 jobs; the flaky files passed);
  `goose.py --check` passes; every `gen-link.py` mode (`--cache --concurrency --server --register
  --leasing --recipes --mvcc --txn --apply --adt --v3rpc`) reproduces (raft's skipped: needs the
  Rocq directory); `tcb-report.py --check` 93 axioms (91 + `zap.Duration`, `zap.Logger.Fatal`),
  9 sorries (the register's), matching the merged baseline with no update; every collection
  matches with no update (server 47/0, server-raft 6/0, v3rpc 3, apply 32, txn 18, mvcc 12, cache
  10, concurrency 12, recipes 11, leasing 8, register 1/9, raft 1, adt 0, btree 0);
  `verified-code.py --reuse`: etcd 625 of 3599 functions verified (6537 of 45570 lines), 9
  unfinished, 33 assumed; under `server/v3/etcdserver` 168 of 969 (the `etcdserver` package 34 of
  279, `v3rpc` 15 of 116).

### Unit 3a: the handoff gaps and the end-to-end Put/DeleteRange (2026-10-12)

Branch `rp-u3a` (worktree `/shared/etcd-grove-rp3a`, off `lean` at `5a04bdf29`; Perennial
`5857c495a` as a path dependency). Plan: the request-path plan's "Unit 3, revised" (3a).
- **The header's four fields owned** (unit 1's `hdrW`): `txn.respHdrOwn hf` (`Requests.lean`: the
  header the field `hf` points to, not nil, `ClusterId`/`MemberId`/`RaftTerm`/`LeaderId` owned) in
  the success posts of `txn.put`/`Put`/`deleteRange`/`DeleteRange` and the sole-writer wrappers
  (`put_soleWriter`, `deleteRange_soleWriter`); the apply package's `appliedHdr log hf` (the
  fields, and `2 ≤ log.length ∧ log.length + 4 ≤ 2 ^ 63`: the revision is not `0`) beside the
  persistent outcome in `putAnswerIs`/`deleteAnswerIs` (`Chain.lean`; the chain's triples, the
  layers' specs, `dispatchAnswer`, `putAnswerIs_nil`/`_errIs`); `EtcdServer.Put`/`DeleteRange`'s
  success: applied (`.applied l false`), `putOutcomeIs`/`deleteOutcomeIs`, `appliedHdr`, `idxCert`.
  `txn.soleWriter` keeps `2 ≤ log.length` (`NewStore`'s `[[], []]`; `soleWriter_len`): the
  delete's revision `writeRev` is at least `1`. `putOutcomeIs`/`putResponseIs` unchanged and
  persistent; nothing kept `resultΨ`/`appliedOk` under `□` (the wait's handoff transfers it).
  `Txn` and `Range` not done (their headers: `newTxnResp`, `executeRange`; 3b).
- **The error facts**: `applyErrIs` (`apply/Base.lean`) strengthened by `errKeyMsg` (`nil`, or a
  `SafeMapKey` whose `Error()` returns), `errVarLeaf` by the message triple (package facts,
  `errors.wp_New`'s), `applyErrIs_tree` for `errors.Is`'s users, `safeMapKey_ptrErr`. The
  proposal's errors carry it: the auth store's `AuthInfoFromCtx` and raft's `Propose` contracts
  (`InvRequest.lean`), `proto.MarshalIRR`'s error (axiom restated), `parseProposeCtxErr`'s results
  (now only its variables: `errors.IsCtxErr` is `true` at the target itself, and **a new axiom**
  `context.ErrDone`, a done context's `Err()` is `Canceled` or `DeadlineExceeded`, so the
  `default` branch, which returned `cctx.Err()`, is unreachable);
  `processInternalRaftRequestOnce`/`raftRequest`/`Put`/`DeleteRange`'s failure: `applyErrIs err`.
  `srvErrIs_of_applyErrIs` (`ServerKV.lean`).
- **The server's contract** (`v3rpc/InvKV.lean`, `ServerKV.lean`): `raftKV s A` split into
  `kvRangeOk`, `kvPutOk`, `kvDeleteOk`, `kvTxnOk`, `kvGetOk` (the five handler proofs take their
  conjunct); `srvKVAns s E ρ A0` (call: `srvCall`, the context, one id credit, a `leadTimeMu`
  reader slot, and `A0.call`; ok/err of `Put`: `putAppliedOk`/`putErrOk`, of `DeleteRange`:
  `deleteAppliedOk`/`deleteErrOk`, the reader slot back in each; `Range`, `Txn`, `revR`: `A0`'s);
  `kvPutOk_of_server`, `kvDeleteOk_of_server` (from `EtcdServer.Put`/`DeleteRange`'s specs),
  `raftKV_of_server` (the read side's three conjuncts as premises); `kvServerAt` (`kvServerIs`
  without `raftKV`), `kvServerIs_of_at`.
- **Results** (`v3rpc/Results.lean`): `put_end_to_end`, `deleteRange_end_to_end` (`kvServer.Put`/
  `DeleteRange` with the server's triples discharged; premises `isServerReq`, `kvServerAt`,
  `kvRangeOk`/`kvTxnOk`/`kvGetOk` at `srvKVAns s E ρ A0`; a check error, or `(resp, nil)` with
  `hdrFilled`, `hdrRevOut` and `putAppliedOk`/`deleteAppliedOk`, or `nil` and
  `putErrOk`/`deleteErrOk`); their axioms: the request path's 23 (the proposal's trust boundary:
  otel, prometheus, traceutil, the transport queries, `MarshalIRR`, `context.WithValue`/
  `ValueStartTime`/`ErrDone`, `errors.IsCtxErr`/`IsDeadlineExceeded`, `status.Error`,
  `RaftCluster.Members`, `ReqTimeout`, ...), no `sorry`; `put_end_to_end_model` (pure: through
  `alarmChain ns cr`, the log after is the log met with the client's put change, `ns = cr =
  false`), `deleteRange_end_to_end_model` (the log after commits `delChanges`), on `propext` and
  `Quot.sound`.
- **For 3b** (the read side): `kvRangeOk`, `kvTxnOk` and `kvGetOk` at `srvKVAns s E ρ A0` with an
  `A0` of its own (`Range`'s and `Txn`'s answers and errors, what `KV().Rev()` needs); the header
  of a `Txn`/`Range` response owned (`respHdrOwn` in `txnResponseIs`'s and `rangeResult`'s producers,
  `newTxnResp`/`executeRange`; the read-only `Txn`'s and `Range`'s header is the txn package's too,
  through `doSerialize`); their errors `applyErrIs` (a `Range` at a done context returns mvcc's
  `fmt.Errorf("%w", ctx.Err())`, which `applyErrIs` excludes today: `txn.Range`'s `nd`); the
  `Cluster().ID()`/`MemberID`/`Term`/`Leader`/`KV()` getters (`MemberID` is proved).
- **Where the plan was wrong**: the handler also needs the revision not `0` (`hdrRevIn`), which
  the outcome did not say (a delete of nothing has the store's current revision, `log.length - 1`):
  `soleWriter`'s length fact and `appliedHdr`'s bounds; the error gap was not only the applier's:
  the proposal's errors (auth store, marshal, raft, the context) reach the handler too, and the
  context's needed the `ErrDone` axiom (Perennial's `isContext` does not say which error `Err`
  returns); the header conjunct is beside `putOutcomeIs` (`putAnswerIs`), not in it (the handler's
  `A.ok` keeps the outcome while `hdrW` takes the fields).
- **Gates**: full build clean (3118 jobs); every `gen-link.py` mode reproduces (`--server`
  regenerated: `context.wp_ErrDone`); `tcb-report.py --check --update`: 93 → 94 axioms
  (`context.ErrDone.wp_proof`), 9 sorries (the register's); collections: server 47 → 48 (ErrDone),
  v3rpc 3 → 23 (the end-to-end results reach the proposal's trust boundary), the others unchanged
  (apply 32, txn 18, mvcc 12, cache 10, concurrency 12, recipes 11, leasing 8, register 1/9, raft
  1, adt 0, btree 0, server-raft 6); `verified-code.py --reuse`: etcd 625 of 3599 functions (no
  function changed state: this unit composes), under `server/v3/etcdserver` 168 of 969. No Go
  finding.

### Unit 3b: the read side and Txn (2026-10-12)

Branch `rp-u3b` (worktree `/shared/etcd-grove-rp3b`, off `lean` at `fd5d5306e`, unit 3a's merge;
Perennial `5857c495a` as a path dependency). Plan: the request-path plan's "Unit 3, revised" (3b).
The work ran as a specification layer (all shared definitions and spec statements, built), then
five parallel proof workers on disjoint leaf files, then the links, the contract and the results.
- **Verified and linked** (server's list): `EtcdServer.Range`, `Txn` (both branches),
  `doSerialize`, `newHeader`, `LinearizableReadNotify` (the one-line delegation, over `isRead`),
  `KV`, `Cluster`, `getTerm`, `Term`, `Leader`, `tracing.go`'s `firstCompareKey`/`firstOpKey`/
  `firstOpType`/`firstOpLease` (loops over the oneofs), and etcdserverpb's `RangeRequest.Get*`
  (six), `TxnRequest.GetCompare`/`GetSuccess`/`GetFailure`, `RequestOp.GetRequest`,
  `PutRequest.GetLease`. The read side's vocabulary: `InvRead.lean` (`isServerRead`,
  `srvRdCall`, `storeSmall`, `rangeReadOk`, `txnReadOk`, `txnAppliedOk`, `txnErrOk`,
  `applyErrIs_errorf`).
- **The server as a reader sees it** (`isServerRead s E γr`, persistent): the read loop
  (`isRead`), the KV as the bare store of the applier's environment (`txn.isKV`, the apply
  package's standing premise) and its `ReadView`, the lessor's and the auth store's contracts
  (`apply.isApplyLessor`, `apply.isAuthStore`), the logger, `WarningApplyDuration`, the term's
  atomic, a certificate of a log of `NewStore`'s two revisions (every read's revision is then not
  `0`), and **`storeSmall`**: every certified log has at most `2 ^ 62` changes (`txn.LogSmall`,
  the sort's premise; a premise, as the apply thread's `rangeOk`/`TxnPre` of its entries). A read
  call's resources (`srvRdCall`): the store's reader slots, a reader slot of `s.lgMu` (the
  `Logger()` unit 2 noted), and `committedAtLeast γr c` (the committed index the caller knew of).
- **The read contract's use** (`isRead`, `InvRequest.lean`, now also: its error is `applyErrIs`):
  a linearizable read's success carries `readIndexOk γr c` (the applied index reached an index at
  least `c`); the link between the applied index and the KV's log is unit 4's.
- **The response headers owned** (3a's `respHdrOwn` for the reads and `Txn`): `asembleRangeResponse`
  and `newTxnResp` allocate the header and hand its id fields over (`txn.rangeHdr resp err` beside
  `rangeResult` in `executeRange`/`Range`; `respHdrOwn` in `newTxnResp`, `txn.txn`, `Txn`'s
  success); the apply package threads `Txn`'s as `put`'s (`apply.txnAnswerIs`: `txnOutcomeIs` and
  `appliedHdr`, in the chain's triples, the five layers' `Txn`, `dispatchAnswer`, `WrapLemmas`,
  `DispatchLemmas`, `Results.chain_txn`). A `Range` through the apply thread (an `IRR.Range`, which
  the server never proposes) keeps `rangeOutcomeIs` without the header.
- **`txn.Txn` at a reader** (`Spec/.../txn/Txn.lean`: `Txn.spec := specSole ∧ specRead`, one
  function's two triples by caller): `specRead` runs a read-only request (`txnReadonly`; top-level
  gets only) with a reader's slots, tokens and certificate, at any context (`txnCtx`: it may be
  done); `executeTxn` and `txn.txn` take a never-done flag `nd` (`nd = false` only for read-only
  runs, whose lease premises are dropped) and the context-error outcome. Premises: the gets within
  the model (**`txn.txnGetsOk`**: revision `0`, a sort not cut early, a valid sort target; the model's
  gets in a transaction are the client's `txnOpOf`) and `LogSmall` of the certified logs the read
  may see. `txn.Range`'s sort premise is now asked of certified logs only (a wand over `idxCert`):
  the server's readers know only that.
- **The read side's errors** (`applyErrIs`). A range at a done context returns mvcc's
  `fmt.Errorf("rangeKeys: context cancelled: %w", ctx.Err())`, and `executeTxn` wraps it again.
  **Perennial's model of `fmt.Errorf` does not model `%w`**: it is `errors.New(format)`, an
  `*errors.errorString` leaf (`Perennial/TrustedCode/fmt.lean`). So the model's error is a pointer
  leaf, not Go's `*fmt.wrapError`: `togRPCError` maps it to `codes.Unknown` in the model where Go
  maps it to `ErrGRPCCanceled`/`ErrGRPCDeadlineExceeded` (no claim is false: the handler's spec
  says only "a non-nil error"). What the proof needs and records: `mvcc.errorfIs err` (the
  `*errorString` value and its `Error()`; `mvcc.wp_Errorf_errorfIs` proves it of Perennial's
  `Errorf`, `Proof/.../mvcc/Errorf.lean`) in mvcc's `rangeOutcome` and txn's `rangeResult`
  context-error disjuncts, and **one premise**: `*errors.errorString` has no `Is`, `As` or `Unwrap`
  method (`errLeaf`), a method-set fact the semantics leaves uninterpreted (as Perennial's
  `context.ErrorStringIsError`), stated as the last conjunct of the server's `srvErrVars` (package
  facts); `applyErrIs_errorf` then gives `applyErrIs`. Not an axiom; `errors.Is` is not involved.
- **`EtcdServer.Range`**: `rangeReadOk` (or no response and an `applyErrIs` error: the read
  loop's, the auth store's, `ErrFutureRev`, the context's). **`EtcdServer.Txn`**: read-only,
  `txnReadOk` and the id credit back, or an error (the response may be non-nil: a context done
  during a range returns the partly filled response with the error; the handler returns `nil`);
  writing, as `Put` (`txnAppliedOk`: the decoded request's transaction `t'`, `t` unless a range
  end is `[0]`; `skip` unconstrained: **`SkipRangeExecution` is admitted**, the wait's
  `IsRegistered` being "some boolean", so a waiter's result may show header-only ranges, which Go
  produces only for a waiter that had timed out; suspect 2) or `txnErrOk`. `doSerialize`: over a
  permission check's triple and the read's (`{G} get() {Q}`): `Q`, or an `applyErrIs` error and
  `G ∨ Q`; an auth info's field points-tos make the struct points-to `chk` takes.
- **`traceutil.EnsureTrace`'s axiom restated** (not new): an `isContext` of its argument stays one
  of the result (as `Tracer.Start`'s; Go returns `ctx` or `WithValue(ctx, …)`): the writing `Txn`
  passes it to `raftRequest`.
- **The server's contract discharged** (`v3rpc/ServerKV.lean`): `KVAns` gains `pre : KVReq → Prop`
  (default `True`; the handlers' specs take `⌜A.pre q⌝`); `kvAnswer`'s error case no longer says
  `resp = null`. `srvKVAns s E ρ γr c` is concrete (3a's `A0` gone): call `srvCall ∗ srvRdCall`;
  `pre` of a transaction `txnInModel` (`txnGetsOk` but the sort target, which the check gives:
  `txnGetsOk_of_check`); answers `putAppliedOk`, `deleteAppliedOk`, `rangeAnsOk`, `txnReadAns`/
  `txnAppliedAns` (the server's answers but the header's fields, which `hdrW` takes), every
  resource back but a write's id credit; `revR` the store's reader slots. `kvRangeOk_of_server`,
  `kvTxnOk_of_server`, `kvGetOk_of_server` (`KV().Rev()` is `store.Rev` on the bare store),
  `raftKV_of_server`: no premise but `isServerReq` and `isServerRead`.
- **Results** (`v3rpc/Results.lean`): `raftKV_server`, `put_end_to_end`, `deleteRange_end_to_end`
  (restated: no read-side premises), `range_end_to_end`, `txn_end_to_end` (over the interval
  tree's pending contract, as `kvServer.Txn`'s link; premise `txnInModel`); the server's
  `Results.lean`: `range_linearizable`, `range_serializable` (client terms,
  `txn.rangeResultClient`, for a sort not cut early), `txn_readonly`, `txn_applied`,
  `txn_applied_model` (pure: `alarmTxn` through `alarmChain`). Their `#print axioms`: the request
  path's trust boundary plus the txn package's (traceutil, zap, protobuf, otel attributes), no
  `sorry`; `txn_end_to_end` takes the four `adt` hypotheses.
- **Where the plan was wrong**: the read-only `Txn` could not use the txn package's `Txn` (the
  sole writer's, at a never-done context): a reader-mode triple and the `nd` generalization of
  `executeTxn`/`txn.txn` were needed; the read side needs per-request premises the handlers'
  contract had no place for (`KVAns.pre`) and a size premise of the store (`storeSmall`); the
  context error is not wrapped in the model (`fmt.Errorf` without `%w`), so `applyErrIs` needed the
  `errorString` leaf premise rather than an error tree through the wrapping; a read-only `Txn`
  answers a non-nil response with its error (`kvAnswer` relaxed); `EnsureTrace`'s spec lost
  `isContext`; `isRead`'s error had no gRPC facts; `newHeader` is not on the KV path
  (lease/alarm services) but proved.
- **For unit 4**: the read loop (`read/read.go`) discharging `isRead` (`readIndexOk`) from raft's
  `ReadIndex`/`ReadState` contracts, and the applied index tied to the KV's log; the raft loop's
  `batchCommitted`/`entryWaitOk`; `IsRegistered` tied to the registration (would exclude
  `SkipRangeExecution` for a live waiter); `storeSmall` from a write budget.
- **Gates**: full build clean (3170 jobs; no `sorry` of ours); every `gen-link.py` mode reproduces
  (`--server`, `--txn` regenerated; `--cache --concurrency --leasing --recipes --register --mvcc
  --adt --apply --v3rpc` unchanged; raft's skipped); no `.toml` changed; `tcb-report.py --check`
  94 axioms, 9 sorries (unchanged: no new axiom); collections: server 48 → 61, v3rpc 23 → 46 (the
  read side reaches the txn package's trust boundary: traceutil, zap, protobuf, otel attributes,
  `RaftCluster.ID`, the read-only loggers), the others unchanged (apply 32, txn 18, mvcc 12, cache
  10, concurrency 12, recipes 11, leasing 8, register 1/9, raft 1, adt 0, btree 0, server-raft 6);
  `verified-code.py --reuse`: etcd 625 → 639 of 3599 functions (6721 of 45570 lines), under
  `server/v3/etcdserver` 182 of 969 (the `etcdserver` package 34 → 48 of 279: `v3_server.go` 10
  of 49, `tracing.go` 4 of 4). No Go finding.

### Merge of `origin/lean` (Perennial `a54e1999f`) (2026-10-13)

`origin/lean` (`746f6e8da`: Perennial `5857c495a` → `a54e1999f`, its proof layout, and the
fmt/time/context trust-boundary axioms, "Perennial `a54e1999f`: the proof layout" above) merged
into `lean` (`c45a0bb0e`: units 3b, the watchable store 3a–3c, the interval tree 4a–4d), on
branch `merge-origin`.

- **Conflicts**: `notes/STATUS.md` (the "Last updated" line: both sides' items); mvcc's
  `Link.lean` (regenerated; every `gen-link.py` mode reproduces); `etc/tcb-collections/mvcc.txt`
  (rewritten by the check); `storeTxnCommon__rangeKeys.lean` (ours, below).
- **Adaptation**: none needed beyond the merge: every file of our side built against
  `a54e1999f` as it was (none imports a moved module or calls `fmt` with non-basic arguments
  through Perennial's spec). `etc/verified-code.py` skips the Links of standard-library packages
  (`Proof/{fmt,context}/Link.lean`, origin's), which it refused ("no project translates
  context").
- **`fmt.Errorf` and the error models**: origin's `rangeKeys` took `fmt.Errorf.spec` (the
  axiom: `Error()` returns) and `context.Err.spec`; ours takes neither and keeps
  `mvcc.wp_Errorf_errorfIs` (Perennial's model's body: an `*errors.errorString`), which
  `executeTxn`'s wrapping also uses. The request path needs `applyErrIs` of the error, a leaf
  pointer error (`errLeaf`); Go's `%w` error is a `*fmt.wrapError`, whose `Unwrap` `errors.Is`
  follows, so the axiom cannot be extended with the leaf without being false of Go, and a
  pointer-type clause (true of Go) does not give `applyErrIs`. Go's tree (the wrapped
  `ctx.Err()`) would need `applyErrIs` restricted to pointer targets (`DeadlineExceeded` is not a
  pointer error), a redesign: `notes/decisions.md`, "`fmt.Errorf`'s `%w` errors: the model's
  body, not the axiom". **Known gap**: a canceled read's error facts rest on Perennial's model of
  `Errorf`, which Perennial documents as not modeling `%w`.
- **`context.Err` and `context.ErrDone`**: both kept, neither follows from the other (`Err`:
  any context, the error's `Error()` returns; `ErrDone`: a done context, the error is
  `Canceled`'s or `DeadlineExceeded`'s value, nothing of its `Error()`), each doc comment says
  so. `context.Err` is now the cache's alone; the txn and apply collections lose
  `context.Err`/`fmt.Errorf` (as `lean` had them).
- **Trust base**: 104 axioms (99 + origin's `context.Err`, `fmt.Errorf`, `fmt.Printf`,
  `fmt.SprintfNamed`, `time.Duration.String`), 9 sorries (Perennial's `initialize'` sorries,
  five renamed `X.initialize'.wp_proof` by its layout).

Gates: `lake build` (3816 jobs, no `sorry` but the register's), `etc/goose.py --check`, every
`gen-link.py` mode reproduces, `etc/tcb-report.py --check` (104 axioms, 9 sorries), every
collection's `--check` (adt 0/0, apply 32/0, btree 0/0, cache 14/0, concurrency 13/0, leasing
8/0, mvcc 18/0, raft 1/0, recipes 11/0, register 1/9, server-raft 6/0, server 61/0, txn 18/0,
v3rpc 46/0), `etc/verified-code.py`: etcd 691 of 3599 functions verified (etcd-raft 200 of 323,
register 20 of 28).

### Unit 4a: the read loop (2026-10-13)

Branch `rp-u4a` (worktree `/shared/etcd-grove-rp4a`, off `lean` at `164492796`; Perennial
`a54e1999f`). Design: `notes/decisions.md`, "The read loop's notifier: deposited lower bounds".
- **Translation**: `read.toml` translates the package in full (`NewRead`, `Read`, the `server` and
  `raftInterface` interfaces, `LinearizableReadNotify`, `LinearizableReadLoop`,
  `requestCurrentIndex`, `sendReadIndex`, `uint64ToBigEndianBytes`, `isStopped`, `notifier`,
  `newNotifier`, `notify`, the metrics, `init`); `etcdserver.toml` adds `EtcdServer.ApplyWait`,
  `Done`, `LeaderChanged`, `NextRequestID`, `RequestTimeout`, `Stopping`,
  `FirstCommitInTermNotify`, `AppliedIndex`, `CommittedIndex` and the promoted
  `raftNode.ReadIndex`/`raftNodeConfig.ReadIndex` (translated, for 4b; no type dragged in).
- **Verified and linked** (`read/Link.lean`, `etc/gen-link.py --read`, namespace `read`): all nine
  functions but `init`. `read/Results.lean`: `read_new` (`NewRead.spec`: `isRead r γr`, the loop's
  precondition, the reader slots), `read_loop`, `read_notify`; `#print axioms`: no `sorry`.
- **The ghost protocol** (`read/Inv.lean`): each notifier `nc` has a need `γn` (mono nat);
  `readInv γr` (invariant): the current `(nc, γn)` (`ghostVar γr.notifier`, half; the lock's
  resource `readMuP r γr q` holds `r.notifier ↦{q} nc` and `q/2` of it), the waiters' view and the
  right to notify it (`notifierIs`, `notifierOwn`), the need's authority `n` and `committedAtLeast γr
  n`. A client deposits its `c` (`read_deposit`), the loop swaps and freezes (`read_swap`,
  `needFrozen γn n := inv (monoNatAuthOwn γn 1 n)`), the close tells `notified nc γn γr := ∃ err,
  nc.err ↦□ err ∗ applyErrIs err ∗ (⌜err ≠ nil⌝ ∨ frozenOk γn γr)`, `frozenOk γn γr := ∃ n i,
  needFrozen γn n ∗ appliedAtLeast γr i ∗ ⌜n ≤ i⌝` (`read_frozenOk_readIndexOk`).
- **The contracts** (persistent; unit 4b discharges them): `isReadServer srv γr LR NR` (`Done`,
  `Stopping`, `LeaderChanged`, `FirstCommitInTermNotify` return closed-only channels, `bcastChan ch
  True`; `Logger` with the caller's resource `LR`, given back; `AppliedIndex` an
  `appliedAtLeast`; `ApplyWait(d)` a channel closed with `appliedAtLeast γr d`; `NextRequestID` for a
  resource `NR`; `RequestTimeout` some duration) and `isReadRaft rf γr RQ` (`ReadState()`: a bag
  channel of read states each `readStateOk RQ rs`: its context eight bytes, read-only, and `RQ id n
  → n ≤ rs.Index` for the id they encode; `ReadIndex(ctx, beBytes id)` at `committedAtLeast γr n`:
  `applyErrIs err`, and if `nil`, `□ RQ id n`). The loop's spec takes `LR` and `□ (|==> NR)`.
- **Premises** (recorded here): the raft contract is sound only if request ids do not repeat
  within the process (the request path's `2^48` id budget): a repeated id would let an old read
  state answer a new request's bound; the id budget itself (`□ |==> NR`: one id resource per
  `ReadIndex`, unboundedly many) is the server's premise; raft's read states carry the 8-byte
  contexts `ReadIndex` was given (the server's `raftNode` is only called by the loop).
- **Changes outside the package** (forced, see the decisions entry): `ReadNames` gains `notifier`
  and `isRead`'s triple takes and returns `readReader r γr` (Perennial's `RWMutex` bounds readers);
  `srvRdCall` gains `srvReadReader s γr`, threaded through `EtcdServer.Range`/`Txn`/
  `LinearizableReadNotify`; `applyErrIs`' `TreeTyped` clause holds for pointer targets
  (`ptrTarget`, what `errors.wp_Is` takes), so a done context's `DeadlineExceeded` (a struct) is
  one (`applyErrIs_valLeaf`); `readState_countable` moved from `InvRaftNode.lean` to
  `InvRequest.lean`; the read package's facts (`readInit`, in `BaseApply.lean`: its counters, the
  retry time, `ErrStopped`/`ErrLeaderChanged`/`ErrTimeout`, raft's `ErrStopped`, `context.Canceled`
  as `errVarLeaf`, `ctxDeadlineLeaf`: `DeadlineExceeded` a non-pointer leaf, a safe key, its
  `Error()` returns) replace `True`; the cache's link list names its `newNotifier`/`notify`
  `v3_…` (the read package has the same names).
- **New axioms**: `context.WithTimeoutBackground` (Perennial's `WithTimeout` needs an `isContext`
  parent, `Background()` is none), `strconv.FormatUint` (names-only `strconv`),
  `traceutil.Trace.LogAllStepsIfLong` (names-only `traceutil`).
- **Go**: no finding. `isStopped(err)` returns without closing the pending notifier: its waiters
  leave by their context or `Done()` (stated in the loop's spec). A dropped `waitC` signal needs
  nothing: the pending signal's iteration swaps after the client's deposit.
- **For 4b**: prove `isReadServer s' γr (srvLgReader s) NR` for `*EtcdServer` (the applied index tied
  to `appliedAtLeast`, `ApplyWait` to the wait-time registry, `NextRequestID`'s credit as `NR`) and
  `isReadRaft` for the server's `raftNode`; allocate `γr.notifier` and call `NewRead`; hand the
  reader slots to the request goroutines (`srvReadReader`).
- **Gates**: full build clean (3843 jobs); `goose.py --check` passes; every `gen-link.py` mode
  reproduces (`--cache` regenerated: import order only); `tcb-report.py --check --update`: 104 →
  107 axioms, 9 sorries; collections unchanged (adt 0, apply 32, btree 0, cache 14, concurrency 13,
  leasing 8, mvcc 18, raft 1, recipes 11, register 1/9, server-raft 6, server 61, txn 18, v3rpc 46),
  new `read` 12/0; `verified-code.py`: etcd 691 → 700 of 3599 functions (7856 of 45570 lines),
  `server/v3/etcdserver/read` 9 of 10 (174 of 178 lines; `init` not).

### Unit 4b: the apply loop and the applied index (2026-10-13)

Branch `rp-u4b` (worktree `/shared/etcd-grove-rp4b`, off `lean` at `17575d236`; Perennial
`a54e1999f`). Design: `notes/decisions.md`, "The applied index: a certified log per index".
- **Translation**: `wait.toml` adds `wait_time.go` (`WaitTime`, `closec`, `init`, `timeList`,
  `NewTimeList`, `timeList.Wait`, `timeList.Trigger`); `notify.toml` `Notifier`, `NewNotifier`,
  `Notifier.Receive`; `etcdserver.toml` `EtcdServer.applyAll`, `applySnapshot`, `Backend`,
  `snapshotIfNeededAndCompactRaftLog`, `shouldSnapshotToDisk`, `shouldSnapshotToMemory`,
  `memorySnapshotCount`. No type Goose cannot translate was dragged in.
- **Verified and linked** (the server's `Link.lean`): `wait.NewTimeList`, `timeList.Wait`,
  `timeList.Trigger` (`wait/TimeList.lean`: `isWaitTime wt P`, `isTimeList tl P`; `Wait(d)` returns
  a channel closed with some `Q` with `□ (Q -∗ P d)`, `Trigger(d)` takes `□ P d`; `P` monotone
  downward), `notify.NewNotifier`, `Notifier.Receive` (`notifyReader n`, a reader slot of `n.mu`);
  the nine `server` methods of `*EtcdServer` (`ApplyWait`, `Done`, `LeaderChanged`,
  `NextRequestID`, `RequestTimeout`, `Stopping`, `FirstCommitInTermNotify`, `AppliedIndex`,
  `CommittedIndex`); `raftNode.ReadIndex`; `applyAll`, `applySnapshot` (under raft's no-snapshot
  contract: it returns at `IsEmptySnap(nil)`; verified-code counts its 102 lines, all but the
  check unreachable under the premise), `Backend`, `snapshotIfNeededAndCompactRaftLog`,
  `shouldSnapshotToDisk`, `shouldSnapshotToMemory`; `getAppliedIndex`, `getCommittedIndex`,
  `setAppliedIndex`, `apply`, `applyEntries`, `applyEntryNormal`, `setTerm`, `raftNode.start`,
  `raftNode.ReadState` restated.
- **The read loop's contracts discharged**: `read_server` (`isReadServer (*EtcdServer s) γr
  (srvReadLR s) (idCred ρ.ids 1)` from `isServerReq s E ρ ∗ isServerRead s E γr`;
  `ReadServer.lean`), `read_raft` (`isReadRaft (*raftNode r) E.γr E.RQ` from `isRaftNode E γ r`;
  `ReadRaft.lean`), `wait_time` (`isWaitTime (*timeList tl) P` from `isTimeList tl P`). `LR :=
  srvReadLR s` = `srvLgReader s` and a reader slot of each of `s.leaderChanged` and
  `s.firstCommitInTerm`; `NR := idCred ρ.ids 1` (the loop's `□ |==> NR` is the server's id-budget
  premise).
- **The raft contract** (`InvRaftNode.lean`): `RNEnv` gains `γr : ReadNames` and `RQ`;
  `isRaftNodeIfc` gains a `ReadIndex` conjunct (at `committedAtLeast E.γr n`: `applyErrIs err`, if
  `nil` `□ E.RQ id n`: the trust-boundary claim that a read index is at least the committed index
  at the call); `rnReadyData`'s read states are each `readStateOk E.RQ` (`ReadStates' = nil` until
  then); `isRNReadStateC E c := isReadStateC c E.RQ`; `raftNode.start` forwards
  `rd.ReadStates[len-1]` to `readStateC` (or warns after `time.After`, or returns on `r.stopped`;
  joined by `wp_join (Q := …)` with a `returnVal` case), taking `zap.Duration`/`Logger.Warn`.
- **The ghost applied index**: `ReadNames` gains `logs` (a ghost map, index ↦ KV log);
  `appliedLogAt γr i L := i ↪[γr.logs]□ L` (`appliedLogAt_agree`); `srvAppliedInv s E γr` (the
  atomic at `v`, `monoNatAuthOwn γr.applied ½ v`, the map's authority with keys `≤ v`,
  `appliedLogAt γr v L`, `idxCert E.γ.idx L`) replaces `srvAtomicU64 appliedIndex`;
  `srvAppliedOwn γr v` (the other half) is the apply thread's, carried by `apply`/`applyEntries`/
  `applyAll` beside `ep.appliedi ↦ v` with `appliedLogAt γr v x.log`; `setAppliedIndex` takes
  `srvAppliedOwn γr v`, `v < v'`, `idxCert L` and gives `srvAppliedOwn γr v' ∗ appliedAtLeast γr v'
  ∗ appliedLogAt γr v' L` (deposited at the atomic store); `srvCommittedInv s γr` likewise (no log;
  the writer's half `srvCommittedOwn` is 4c's). `isServer`/`srvAtomics` take `γr`; the proposer's
  `srvReqFieldsAt` holds `srvIndexInvs s E := ∃ γr, srvAppliedInv s E γr ∗ srvCommittedInv s γr`
  (a deviation from the brief, which threaded `γr` through `ReqFields`: the proposer reads the
  indices only for the request limit, so the names do not matter, and `isServerReq`'s 39 uses keep
  their signature); `srvReadFieldsAt` holds them at `γr`, with `applyWait` (`isWaitTime …
  (appliedAtLeast γr)`), `leaderChanged`, `firstCommitInTerm`, `stopping` (`srvDoneChan`).
  `readIndexOk_log`, `readIndexOk_logR`; `rangeReadOk`/`txnReadOk` (and v3rpc's `rangeAnsOk`/
  `txnReadAns`) in the linearizable case: `readLogOk γr c log` (`readIndexOk γr c ∗ ∃ ci₀ L₀, c ≤
  ci₀ ∗ appliedLogAt γr ci₀ L₀ ∗ L₀ <+: log`; `Range`/`Txn` pass the longer of their `log₀` and
  `L₀` to `txn.Range`/`txn.Txn`). Results (`Results.lean`): `range_linearizable` restated with the
  log, `applyAll_model`, `applied_log_at` (`setAppliedIndex`'s and `apply`'s deposits,
  `appliedLogAt_agree`), `read_server`, `read_raft`, `wait_time`.
- **Changes to 4a's contracts** (`read/Inv.lean`): `ApplyWait(d)` returns `∃ Q, bcastChan ch Q ∗ □
  (Q -∗ appliedAtLeast γr d)` (`Wait` returns the package's `closec`, closed with nothing, when `d`
  was triggered; Perennial's broadcast idiom has no way to view a closed channel at another
  content); `LeaderChanged()`/`FirstCommitInTermNotify()` take and return `LR` (`srvChanOkR`:
  `Receive` read-locks the notifier). The loop's proofs (`Read__LinearizableReadLoop`,
  `Read__requestCurrentIndex`) pass `HLR` and apply the wand after the receive.
- **Premises**: the id budget (`□ |==> idCred ρ.ids 1`, the loop's `NR`); raft's no-snapshot
  contract (`ap.snapshot = nil`, `rnApP`); `closec` closed (`waitClosecInit`, a premise of
  `NewTimeList` carried by `isTimeList`, as Perennial's `context.isClosedchanInit`: the package
  facts are at any `HasLC`, the broadcast idiom needs later credits, so `wait`'s `isPkgInit` stays
  `True` and `init` is not proved); `P` monotone downward and `□ P 0` for `NewTimeList`. Monotone
  triggers are **not** needed (the lock keeps `□ P last`; a lower `Trigger(d)` brings `□ P d`):
  documented in `TimeList.lean`. The server's package facts gain `srvApplyLoopInit`
  (`proposalsApplied` a gauge with `Set`, `schema.AllBuckets` some slice).
- **New axioms** (trust boundary, names-only callees of `applyAll`): `backend.VerifyBackendConsistency`
  (verification code, as `verify.Verify`), `EtcdServer.snapshot` (frames `ep`'s applied index,
  term, conf state, `srvApplyKV`, the backend, the applying index; keeps `loopOk`/`ciEff`; may move
  `srvSnapState`), `EtcdServer.compactRaftLog`, `EtcdServer.createMergedSnapshotMessage`,
  `EtcdServer.sendMergedSnap`. `proposalsApplied.Set` is a package fact (`gaugeSetSpec`, as the raft
  wrapper's gauges), not an axiom.
- **Go**: no finding. `applyAll` triggers `applyWait` after `applyEntries`, before `<-notifyc`: a
  waiter is released once the KV applied through `d`, which is what a read sees (no WAL read).
  `applyEntries`' gap panic is ruled out by its spec's premise `f0 ≤ ai + 1` (4c derives it from
  `rnApP`'s consecutive `cum`). `SnapshotCount = 0` is not used by the proof. `Trigger` may lower
  `lastTriggerDeadline`; the API's documentation promises no more than the code does.
- **For 4c** (`run`/`start`): allocate `γr` (`applied`, `committed`, `notifier`, `logs`) with
  `srvAppliedInv` at the snapshot index and the KV's log then (`appliedLogAt γr ai x.log`), keep
  `srvAppliedOwn γr ai` for the apply loop and `srvCommittedOwn` for `updateCommittedIndex`
  (raising `γr.committed` at the raft loop's commit; `isReadyHandler`'s `updateCommittedIndex` gets
  a real spec); allocate `γr.notifier` and call `NewRead` with `read_server`/`read_raft`; hand out
  the reader slots (`readReader`/`srvReadReader` to request goroutines, `srvReadLR s`: one
  `srvLgReader` and one `notifyReader` of each notifier to the read loop, `srvBemuReader` to the
  apply loop); build `RNEnv` with `γr`/`RQ` for the raft node contract; `stopping` is
  `make(chan struct{}, 1)`: Perennial's broadcast allocation needs an unbuffered channel (`.Idle`),
  so stating `srvDoneChan stopping` needs a capacity-1 broadcast idiom (a Perennial addition) or a
  closed-only invariant for `Buffered []`; `waitClosecInit` from the package's initialization;
  `applyAll`'s per-`toApply` facts (`taSnapshotAddr ap ↦□ nil`, `isUnitBag notifyc`) from `rnApP`.
- **Gates**: full build clean; `goose.py --check` passes; every `gen-link.py` mode reproduces;
  `tcb-report.py --check --update`: 107 → 112 axioms, 9 sorries; collections: server 61 → 66, the
  others unchanged (adt 0, apply 32, btree 0, cache 14, concurrency 13, leasing 8, mvcc 18, raft 1,
  read 12, recipes 11, register 1/9, server-raft 6, txn 18, v3rpc 46); `verified-code.py`: etcd
  700 → 720 of 3599 functions (8053 of 45570 lines), `server/v3/etcdserver` 48 → 63 of 279 (923 of
  4637 lines), `pkg/v3/wait` 7 → 10 of 12 (73 of 77 lines; `init` not translated as a function),
  `pkg/v3/notify` 3 of 3, `server/v3/etcdserver/read` 9 of 10.

### Unit 4c: `run`, `start`, the scheduler and the committed index (2026-10-13)

Branch `rp-u4c` (worktree `/shared/etcd-grove-rp4c`, off `lean` at `5dfc2c339`; Perennial
`a54e1999f`; not rebased on the backend's unit 6, `278bfe56f`). Design: `notes/decisions.md`,
"The server's goroutines: the FIFO scheduler as a chain of saved postconditions, the construction
premise".
- **Translation**: `etcdserver.toml` adds `EtcdServer.run`, `start`, `Start`, `GoAttach`,
  `setCommittedIndex`, `setLead`, `DefaultSnapshotCount`, `DefaultSnapshotCatchUpEntries` (axioms
  until then: `start` stores them) and imports `pkg/v3/schedule`, `api/v3/version` (new, names-only,
  `version.toml`) and `Masterminds/semver`; raft v3.7's `raftpb.toml` adds
  `SnapshotMetadata.GetTerm`. The etcdserver package's types now cost exactly proofgen's threshold
  (300): its `GeneratedProof` chunks are gone (one module). `BaseApply.lean`: `version`'s package
  fact (`Version` holds some string); `apply/Base.lean`: `membership`'s (`ClusterVersionMetrics`
  holds some `*GaugeVec`).
- **The FIFO scheduler's contract** (`pkg/v3/schedule/Defs.lean`, one axiom
  `Scheduler.Schedule`): a queue of saved postconditions (`schedQueue γ Ps`, a mono list whose first
  slot names the stop token); a **tracked** `Schedule(j)` with `Pre`, `Prev` (the previous job's
  saved `Post`) and `Post` extends the queue by `post`; the job runs with `schedRunning γ` (the
  worker's run token and thread token) ∗ `Pre` ∗ `Prev` and returns `schedRunning γ ∗ Post`; an
  **untracked** one needs `Prev = Post = True` and `schedLive γ` (mvcc's `scheduleCompaction`). The
  job's triple (`jobDoSpec`/`jobIs`, through `NewJob`/`job.Do`) takes `Prev`. `NewFIFOScheduler`
  returns `isFifo`, the stop token and the queue `[n, p₀]` with `savedProp p₀ True`; new axiom
  `Scheduler.Stop` (`{isFifo ∗ schedStopTok ∗ schedQueue}`). mvcc adapted at one call site
  (`NewStore`: `schedLive_of_stopTok`, `isScheduler` folded); its list adds `Scheduler__Stop`.
- **`run`** (`EtcdServer__run.lean`, `InvRun.lean`): proved, linked as `server_run`. `isServerRun`
  (named conjuncts): `isServer`, `isServerApplyAll`, the raft wrapper (`isRaftNode Er γn`, with
  **`Er.C = srvC ρ E ai₀ c₀ x₀`**: the log after the snapshot index `ai₀`, consecutive from
  `ai₀ + 1` and below `2^64` (`srvIdxOk`), meeting the KV's premises from `x₀` at the consistent
  index `c₀` (`entriesOk`), each entry's id claimed (`batchWaitOk`)), `run`'s fields
  (`srvRunFieldsAt`: `errorc`, `stop`, `done`, `cancel`, the compactor, the stats, the notifier,
  `leadTimeMu`, the committed index's invariant, `GoAttach`'s protocol), `□ |==> Er.T`, the
  snapshot contract once (`rnSnapOnce`), the raft wrapper's tokens at `[]`, the committed index's
  writer half, `done`'s closer view, the closer's token, the apply thread's start
  (`applyStart`), `run`'s logger slot, and the write budget `WB N` (`WB (a+b) ⊣⊢ WB a ∗ WB b`,
  `2^64 ≤ N`). The apply thread's resources are defined once (`applyRes C A`, the log `A` applied
  since `ai₀`); the loop invariant holds `applyRes`'s saved name in the queue, `rnApplyTok γn A`,
  the ready handler's `R`, `WB (N - |A|)`; each batch's job has `Pre := batchWaitOk ∗ fields ∗
  WB |ce|`, `Prev := applyRes C A`, `Post := applyRes C (A ++ ce)` (`run_job_body`). The ready
  handler (`isReadyHandler rh R`, `R` the committed index's writer half): `getLead`, `updateLead`
  (`setLead`), `updateLeadership` (`isLeader`, the lessor's `Demote`, the compactor,
  `leadTimeMu`, `Notify`, `BecomeLeader`), `updateCommittedIndex` (`setCommittedIndex` raises
  `γr.committed`). The shutdown: `wgMu.Lock`, `close(stopping)` (`goAttach_shutdown`), cancel,
  `sched.Stop`, `wg.Wait`, `r.stop`, `Cleanup`, `close(done)`.
- **The unit-6 hook** (the backend's write budget, `txn.storeWTs E.γ`, merged on `lean` at
  `278bfe56f`, not here): `run` carries `WB` and splits it per batch (`HWBsplit`); the batch's share
  `HWBc` is dropped in the job closure (`EtcdServer__run.lean`, the comment "the backend's unit 6,
  on merge: `HWBc` … goes to `applyAll`", before `iclear HWBc`) and `run_job_body` marks where
  `applyAll` takes it (the comment "the backend's unit 6, on merge: `applyAll` also takes this
  batch's write tokens"). On merge: instantiate `WB := txn.storeWTs E.γ` (the split lemma
  `storeWTs γ (a+b) ⊣⊢ storeWTs γ a ∗ storeWTs γ b`, to prove in the txn package), pass `HWBc` to
  `run_job_body` and on to `applyAll`.
- **`stopping`** (`StopChan.lean`, no Perennial change): a capacity-1 channel closed once, never
  sent on: `stopChanInv` (`Buffered []` with the closer's flag at `½ false`, or `Closed []` with `□
  Q` and the flag discarded), `ownStopChan ch γ Q st` (as Perennial's broadcast idiom), `stopChan
  ch` (a receiver's view); `alloc_stop_chan` (from `make(chan struct{}, 1)`), `stop_chan_receive`,
  the non-blocking receives (open: with a fraction of the flag, as `GoAttach` sees it; closed),
  `stop_close_au` (`_internal`). `srvReadFieldsAt` and `isReadServer`'s `Stopping()` (`srvStopOk`)
  state `stopChan`; the read loop's proofs receive with `stop_chan_receive`.
- **`GoAttach`** (`InvGoAttach.lean`): proved over Perennial's `WaitGroup`: a ghost flag `open`
  (half in `wgMu`'s resource, half in the invariant), the closer's flag of `stopping` (a fraction per
  reader), the wait group's counter with one deposited thread token per goroutine (the bound
  `threadBound GF ≤ 2^31`), no waiter while open; `run`'s shutdown takes it all (`goAttach_shutdown`)
  and `wg.Wait()`s. A caller holds `srvGoRes s` (a `wgMu` reader slot and its thread token); `P` is
  consumed whether `f` runs or not.
- **`start`** (`EtcdServer__start.lean`, `InvStart.lean`): proved, `server_start`. **The construction
  premise `isServerBuilt`**, clause by clause: `#Hci` (`isServerCI`); `#Hfb` (`srvFieldsBuilt`:
  `isServer`'s fields but `w`); `#Hreqb` (`srvReqBuilt`: `isServerReq`'s but `w`, `done` and the
  indices); `#Hrdb` (`srvReadBuilt`: `isServerRead`'s but `read`, `applyWait`, `leaderChanged`,
  `stopping` and the indices); `#Hrunb` (`srvRunBuilt`: `errorc`, compactor, stats, `leadTimeMu`);
  `#Hsab` (`msgSnapC`); `#Hai`, `#Hti`, `#Hci'` (the applied, term and committed atomics'
  invariants at `γr`); `#Hrn`, `%HEr` (the raft node contract, `Er.C = srvC …`, `Er.γr = γr`);
  `#HT`; `Hsnap`; `Hloop`, `Happly`, `Hrdone`; `#HNR` (`□ |==> idCred ρ.ids 1`, the read loop's ids);
  `#Hcv` (`clusterVersionOk`: `ClusterVersion()` is `nil` until known, non-`nil` from then on, a
  ghost witness); `#Hcci`, `#Hwci` (`context`'s and `wait`'s `closedchan`/`closec` facts);
  `%Hbound` (`threadBound GF ≤ 2^31`); the fields `start` sets (`Hw`, `Haw`, `Hdone`, `Hstop`,
  `Hstopping`, `Hctx`, `Hcancel`, `Hread`, `Hlc`, `Hsc`, `Hscu`: any values), `Hwg`/`HwgMu` (zero);
  `Hcomm` (the committed index's writer half); `Hnot` (`γr.notifier`'s ghost variable, for
  `NewRead`); `Happ` (`applyBuilt`: `applyStart` but the `wgMu` slot and the wait); `Hlr`, `Hlrl`
  (`lgMu` reader slots: `run`'s, the read loop's); `Hfcr` (a `firstCommitInTerm` reader slot, the read
  loop's); `HWB`. **Deviation**: `γr` is the premise's, not allocated by `start` (the raft node's
  contract, `NewServer`'s, is stated over `γr`: `Er.γr = γr`, the read registrations), so the
  premise carries its invariants and ghost state at the snapshot; `w`'s names are fresh
  (`wait.New`), so the views are at `{ ρ with wait := γw }`. `start`'s post: `∃ γw, isServerReq s E
  {ρ with wait := γw} ∗ isServerRead s E γr ∗ srvStarted s γr ρ Er.RQ` (a `wgMu` slot for `Start`;
  the read loop's precondition with `srvReadLR s` and `□ |==> idCred`; the reader slots left).
- **`NewRead` restated** (`read/NewRead.lean`, 4a's): it takes the server's `Done()` (`srvDoneOk`)
  instead of `isReadServer`/`isReadRaft`, and returns the loop's precondition as `□ ∀ RQ LR NR,
  isReadServer … -∗ isReadRaft … -∗ isReadLoopPre …`: `start` calls it before it sets
  `s.leaderChanged`, which `isReadServer`'s `LeaderChanged()` reads.
- **Which slots a request goroutine gets, and from whom**: `srvReadReader s γr` (a reader slot of
  `s.read.mux`, `srvRdCall`'s): from `NewRead`, all of them, through `start`'s post (`Start` passes
  them on); `srvWgReader s` (to `GoAttach`): `start` sets up `wgMu` and keeps all but two (the apply
  thread's, `Start`'s); `s.leaderChanged`'s reader slots: all but the read loop's; `srvLgReader s`
  (`lgMu`, made by `NewServer`): the premise's (`run`'s, the apply thread's, the read loop's;
  `Start` takes two more: its `GoAttach`es', given back, and `monitorFileDescriptor`'s), the rest
  `NewServer`'s to hand out; `mvcc.storeReader`: the store's, `NewServer`'s.
- **`Start`** (`EtcdServer__Start.lean`): proved, `server_Start`: `start`, then ten `GoAttach`es:
  the read loop (`LinearizableReadLoop`, verified: `P :=` its precondition with `srvReadLR s` and
  `□ |==> idCred`), and nine names-only monitors with trust-boundary contracts `{True} m() {True}`
  (assumed): `adjustTicks`, `publishV3` (after the verified `Cfg.ReqTimeout()`), `purgeFile`,
  `monitorFileDescriptor` (after `Logger()`, with its own `lgMu` slot), `monitorClusterVersions`,
  `monitorStorageVersion`, `monitorKVHash`, `monitorCompactHash`, `monitorDowngrade`. `Start`'s pre:
  `isServerBuilt` ∗ the caller's thread token ∗ two `lgMu` slots.
- **The committed index**: `setCommittedIndex` (`v ≤ v'`: the writer half moves, the lower bound
  given) and `setLead` translated and proved; `getCommittedIndex` takes `srvCommittedOwnOpt`
  (exactly `v` when the writer reads); `updateCommittedIndex`/`raftNode.start` take the ready
  handler's resource `R`.
- **Results** (`Results.lean`): `server_run`, `server_start`, `server_Start`, `start_gives_views`
  (from `isServerBuilt` alone: `isServerReq`, `isServerRead`, `read_server`'s contract and the
  `srvReadReader` slots: `range_linearizable`, `txn_applied` and the v3rpc results are conditional on
  the construction premise and each call's resources), `scheduler_fifo` (the `Schedule` axiom
  restated).
- **New axioms** (16; one gone): the trust boundary of names-only callees: `Scheduler.Stop`
  (schedule), `EtcdServer.revokeExpiredLeases`, `EtcdServer.Cleanup`,
  `v2stats.ServerStats.BecomeLeader` (`run`), `EtcdServer.adjustTicks`, `publishV3`, `purgeFile`,
  `monitorClusterVersions`, `monitorStorageVersion`, `monitorKVHash`, `monitorCompactHash`,
  `monitorDowngrade`, `monitorFileDescriptor` (`Start`'s monitors), `version.Cluster`,
  `prometheus.GaugeVec.With` (`start`'s log line and gauge), and the contract
  `EtcdServer.raftRequestAlarm` (`AlarmContract.lean`: the alarm goroutine's `raftRequest`, whose
  proof needs the request path's resources the apply thread does not have). Gone:
  `EtcdServer.GoAttach` (proved). Contracts in premises (not axioms): `rnSnapOnce`, `lessorOk`'s
  `Demote`/`ExpiredLeasesC`, `compactorOk`, `clusterVersionOk`, the ready handler's `R`.
- **Go**: no issue. `run`'s "empty confstate" panic is unreachable: raft v3.7's
  `MemoryStorage.Snapshot` returns `EnsureSnapshot(…)` (non-nil metadata and conf state, no error),
  so `rnSnapOnce` is true of it (its index and term are the premise's). `GoAttach` after `stopping`
  is closed drops `f` (documented: "should interrupt on StoppingNotify"); `Start` after `Stop`
  starts nothing. `Schedule` after `Stop` panics, but `sched` is local to `run`, stopped in its
  deferred shutdown after the loop returns: no job is scheduled after.
- **Gates**: full build clean; `goose.py --check` passes; every `gen-link.py` mode reproduces
  (`--backend` included; the raft mode needs the Rocq tree); `tcb-report.py --check --update`: 172
  → 187 axioms, 31 sorries (unchanged); collections: server 70/0 → 93/1 (the new axioms, those
  `start`'s callees already had, and mvcc's pending `schedule.NewJob` `sorry`, which `run` reaches),
  mvcc 34/22 → 35/22 (`Scheduler.Stop`), the others unchanged (adt 0, apply 36, backend 59, btree 0,
  cache 14, concurrency 13, leasing 8, mvcc-compaction 22/22, raft 1, read 12, recipes 11, register
  1/9, server-raft 6, txn 22, v3rpc 50); `verified-code.py`: etcd 794 → 800 of 3599 functions (8778
  of 45570 lines), `server/v3/etcdserver` 69 of 279 (1088 of 4637 lines).
- **For 4d** (the wrap-up): merge `lean` (unit 6) and close the hook (`WB := txn.storeWTs E.γ`, the
  split lemma, `HWBc` to `applyAll`); prove `schedule.NewJob`/`job.Do` (mvcc's pending `sorry`s,
  which `run` now reaches); state what `NewServer` must discharge for `isServerBuilt` (or prove
  it); consider proving `raftRequestAlarm` from the request path's resources.

### Merge of unit 4c onto the write budget (2026-10-13)

`rp-u4c` (`32e0eb964`: unit 4c above) merged into `lean` (`278bfe56f`: the backend's unit 6, the
write budget), on branch `merge-u4c`. Same Perennial pin (`a54e1999f`); the Goose translation of the
union is the pinned translator's (no regeneration).

- **Conflicts** (12 files): the four apply-thread specs and proofs (`EtcdServer.apply`,
  `applyEntries`, `applyEntryNormal`, `applyAll`): independent conjuncts, each takes both 4c's
  `srvGoRes s` (pre and post) and unit 6's write budget (`txn.storeWTs E.γ …`, `mvcc.storeWT E.γ`
  for `applyEntryNormal`), the proofs naming and passing both (`Hgr` and `HW`/`Hwt`); the server's
  `Results.lean` (both sections: unit 6's `backend` with `server_kv_backend`, 4c's `goroutines`);
  `etc/tcb-collections/server.txt` (the header lines of both, the baseline the union); this file
  (the "Last updated" line; both sections kept) and `notes/decisions.md` (both entries).
- **The write-budget hooks closed**: 4c's abstract budget `WB` is `txn.storeWTs E.γ`. `isServerBuilt`
  (`InvStart.lean`) and `isServerRun` (`InvRun.lean`) drop the `WB` parameter, their `"HWB"` is
  `txn.storeWTs E.γ N`; `run.spec`, `start.spec`, `Start.spec` and `start_gives_views` drop `WB` and
  the split hypothesis, keeping `2 ^ 64 ≤ N` (the indices `srvC` allows are below `2 ^ 64`, so the
  budget never runs out). The split is `txn.storeWTs_add γ a b : storeWTs γ (a + b) ⊣⊢ storeWTs γ a
  ∗ storeWTs γ b` (`txn/Defs.lean`, next to `storeWTs_split`; from `ownToks_add`, `True` over the
  assumed backend). `run` splits each batch's `ce.length` tokens off its remaining `N - A.length`,
  the job's `Pre` carries them, and `run_job_body` takes `txn.storeWTs C.E.γ ce.length` and passes
  exactly that to `applyAll` (whose pre asks `(unapplied ai ce).length`, equal since every entry of
  the batch is above the applied index, `unapplied ai ce = ce`): nothing dropped.
- **Gates**: full build clean (first try); `goose.py --check` passes; every `gen-link.py` mode
  reproduces; `tcb-report.py --check`: 187 axioms, 31 sorries (4c's baseline: unit 6 added no
  axiom); collections: server 141/1 (the union of unit 6's 119 and 4c's 93: 4c's 22 new axioms
  over unit 6's backend and bbolt ones, and mvcc's pending `schedule.NewJob` `sorry`), mvcc 35/22,
  the others unchanged (adt 0, apply 36, backend 59, btree 0, cache 14, concurrency 13, leasing 8,
  mvcc-compaction 22/22, raft 1, read 12, recipes 11, register 1/9, server-raft 6, txn 22, v3rpc
  50); `verified-code.py`: etcd 800 of 3599 functions (8778 of 45570 lines, 21 unfinished),
  `server/v3/etcdserver` 69 of 279 (1088 of 4637 lines).
- **For 4d**: the hook item of 4c's list is done; the rest stands (`schedule.NewJob`/`job.Do`,
  `NewServer`'s discharge of `isServerBuilt`, now with `txn.storeWTs E.γ N` from
  `server_kv_backend`'s supply, and `raftRequestAlarm`).

### Merge of `origin/lean` (the backend, units 1–4) (2026-10-13)

`origin/lean` (`10f2d82eb`: the storage backend, units 1–4, "The backend" above, with unit 4's
generalized mvcc backend contract `isKeyBackendG` and its proof of the real backend,
`mvcc_backend_bridge`) merged into `lean` (`4f2c96322`: the request path's units 4a and 4b), on
branch `merge-origin2`. Same Perennial pin (`a54e1999f`) and `lake-manifest.json` on both sides.

- **Conflicts**: `etc/gen-link.py` (`NAMESPACED`: both `--backend` and `--read`);
  `etc/tcb-baseline.txt` (the union, which `--check` then confirmed exactly); `notes/STATUS.md`
  (the "Last updated" line: both sides' items); `notes/decisions.md` (both entries: ours, "The read
  loop's notifier" and "The applied index", then origin's "The backend meets mvcc"). The other 296
  files merged cleanly; the mvcc files (`InvStore`, `BackendBridge`, `Base`, ...) are origin's
  exactly.
- **Adaptation**: none. Every file of our side builds against origin's contract as it is: the
  request path's proofs (`EtcdServer.Range`/`Txn`, `InvRead`'s `srvRdCall`, v3rpc, `applyAll`)
  use mvcc's store-level predicates (`isStore`, `isTxnRead`, `idxCert`, `storeReader`), not
  `storeTxnReadIs`' inside (whose reader moved to `txReader`, which origin's own txn files already
  adapted to) nor `isKeyBackend`; origin's move of the `backend`/`verify`/bbolt package-init
  instances to `storage/backend/Base.lean` does not meet our `BaseApply.lean` additions (`readInit`,
  `srvApplyLoopInit`, `strconv`), and `schema`'s instance now naming the buckets (`bucketIs`) is
  not used by our proofs. No result restated.
- **Not yet connected**: the request path's results still take mvcc's store as built on the
  token-free contract (`isKeyBackend` = `isKeyBackendG` with `True` tokens and no put condition);
  origin's bridge proves `isKeyBackendG` with the backend's tokens (`bkRT`, `wbTok`, `bkPutOk`), so
  carrying the request path down to the real backend is still to do. Our trust-boundary
  `backend.VerifyBackendConsistency` stays an axiom (origin translates `verify.go` names only).
- **Trust base**: 166 axioms (ours 112 + origin's 158 − 104 shared; none new), 9 sorries.

Gates: `lake build` (4141 jobs, no `sorry` but the generated axiomatized types' and raft `Init`'s),
`etc/goose.py --check` (no regeneration), every `gen-link.py` mode reproduces (cache, concurrency,
server, register, leasing, recipes, mvcc, txn, apply, adt, v3rpc, fmt, context, read, backend),
`etc/tcb-report.py --check` (166 axioms, 9 sorries), every collection's `--check` unchanged (adt
0/0, apply 32/0, backend 59/0, btree 0/0, cache 14/0, concurrency 13/0, leasing 8/0, mvcc 18/0,
raft 1/0, read 12/0, recipes 11/0, register 1/9, server-raft 6/0, server 66/0, txn 18/0, v3rpc
46/0), `etc/verified-code.py`: etcd 794 of 3599 functions verified (etcd-raft 200 of 323,
register 20 of 28).

### Merge of `origin/lean` (the backend, unit 5) (2026-10-13)

`origin/lean` (`2722abe88`: the backend's unit 5, "Unit 5: mvcc's store over the real backend"
above: the store generic in its backend's instance `StoreNames.kb`, the late-bound lock resource
`lateW`, reader and write tokens, the puts' condition, `mvcc_NewStore_backend` and
`mvcc_store_Write_backend`) merged into `lean` (`fe0a47aaf`: the request path's units 4a and 4b,
merged with the backend's units 1–4), on branch `merge-origin3`. Same Perennial pin (`a54e1999f`)
and `lake-manifest.json` on both sides.

- **Conflicts**: `etc/tcb-collections/server.txt` (the baseline only, the `roots` lines identical:
  our 4b axioms `VerifyBackendConsistency` and the four `EtcdServer` names-only contracts, their
  bbolt predicates `backend.rBkt`/`rtxSnap`/`rtxStats`/`txLive`; the union, which `--check` then
  confirmed exactly); `notes/STATUS.md` (the "Last updated" line: both sides' items). The other
  91 files merged cleanly; the mvcc files (`InvStore`, `BackendBridge`, `StoreBackend`, `Base`,
  the `Spec`s) are origin's exactly.
- **Adaptation**: none. The request path meets unit 5 only through `txn.isKV`, which now carries
  `⌜γ.kb = none⌝`: our 4a/4b files (`EtcdServer.Range`/`Txn`/`applyAll`/`apply`/`applyEntries`,
  `InvRead`, `InvApplyAll`, `ReadServer`, v3rpc's `rangeAnsOk`/`txnReadAns`) keep `isKV` folded
  (the two places that destructure it, `EtcdServer.newHeader` and v3rpc's `kvGetOk_of_server`,
  origin already adapted), and never call `store.Write`/`NewStore` directly (the txn package's
  `put`/`deleteRange`/`txn` do, and origin adapted them with `storeWT_none`/`putMax_none`). No
  result restated.
- **What unit 5 leaves the request path**: everything above mvcc is still over mvcc's assumed
  backend (`γ.kb = none`), so the request path's results (`range_linearizable`, `put_end_to_end`,
  `applyAll`'s, ...) are about a store whose backend is the token-free contract. Putting them over
  the real backend needs `txn.isKV` generic in `kb` (dropping `γ.kb = none`), and with it: a write
  token (`storeWT γ`, `backend.wbTok`) per write transaction carried from the server's state into
  the apply package (`srvApplyKV`, `apply.applyKV`) and down to txn's `store.Write`; the bound
  `mvcc.putMax γ` (`2 ^ 56` over the real backend) in place of `2 ^ 63` in the apply package's
  premises; the reader tokens of the store's slots (`kbRT`), which `storeReader` already carries;
  and the server's construction of the store over `backend.New` (not translated with bodies).
- **Trust base**: 166 axioms (both sides' 166 and 158 share the 158; none new), 9 sorries. The
  collections that reach mvcc's `StoreNames` (apply, mvcc, server, txn, v3rpc) gained bbolt's four
  opaque predicates in origin's unit 5; the server's is the union (66 + 4 = 70).

Gates: `lake build` (4143 jobs, no `sorry` but the generated axiomatized types', raft `Init`'s
and Perennial's), `etc/goose.py --check` (no regeneration), every `gen-link.py` mode reproduces
(cache, concurrency, server, register, leasing, recipes, mvcc, txn, apply, adt, v3rpc, fmt,
context, read, backend), `etc/tcb-report.py --check` (166 axioms, 9 sorries), every collection's
`--check` as merged (adt 0/0, apply 36/0, backend 59/0, btree 0/0, cache 14/0, concurrency 13/0,
leasing 8/0, mvcc 22/0, raft 1/0, read 12/0, recipes 11/0, register 1/9, server-raft 6/0, server
70/0, txn 22/0, v3rpc 50/0), `etc/verified-code.py`: etcd 794 of 3599 functions verified
(etcd-raft 200 of 323, register 20 of 28).

### Merge of `origin/lean` (the backend, unit 6: the write budget) (2026-10-13)

`origin/lean` (`1c54ee184`: the backend's unit 6, "Unit 6: the layers above mvcc over the real
backend" above: `txn.isKV` generic in the store's backend instance, a write token per store write
transaction `txn.storeWTs E.γ n` threaded through the apply package into the apply thread, the
change bound `2 ^ 56`, `server_kv_backend`) merged into `lean` (`5dfc2c339`: the request path's
units 4a/4b and the backend's units 1–5, merged with the mvcc session's unit 5a, the compaction's
scaffolding), on branch `merge-origin4`. Same Perennial pin (`a54e1999f`) and `lake-manifest.json`.

- **Conflicts** (9 files): the apply thread's three specs and proofs (`EtcdServer.apply`,
  `applyEntries`, `applyEntryNormal`), the server's `Results.lean` (the imports only),
  `etc/tcb-collections/server.txt` (the header and the baseline) and this file (the "Last
  updated" line). The other files merged cleanly; the mvcc files are origin's with our unit 5a's
  additions (`storage/mvcc/Results.lean` merged cleanly: origin's doc paragraph and 5a's compaction
  `#print axioms`; no mvcc file needed a hand resolution).
- **The two spec changes combined**: the applied-index ghost (ours, 4b) and the write budget
  (theirs, unit 6) are independent conjuncts, so each spec takes both. `applyEntryNormal`: `γr`
  (ours) and `mvcc.storeWT E.γ` (theirs) in the pre. `apply`: pre `… srvApplyKV s E x ∗
  srvAppliedOwn γr (f0 - 1) ∗ txn.storeWTs E.γ ms.length`, post unchanged (ours: `srvAppliedOwn
  γr appliedi`, `appliedLogAt γr appliedi x'.log`; the tokens are spent). `applyEntries`: pre
  `… srvApplyKV s E x ∗ srvAppliedOwn γr ai ∗ appliedLogAt γr ai x.log ∗ txn.storeWTs E.γ
  (unapplied ai ms).length`, post ours. `applyAll` (ours, not conflicted) gains `applyEntries`'
  budget in its pre, `txn.storeWTs E.γ (unapplied ai ms).length`, spent; `InvApplyAll`'s
  `srvApplyRes` (what comes back) is unchanged.
- **Proofs adapted**: `EtcdServer.apply` (the loop invariant carries both `HW` = `txn.storeWTs E.γ
  (ms.length - j)` and ours' `Hao`/`Hlog`/`Haw`; the initial instance's `simp` is origin's, the
  `Haw` goal ours), `applyEntries` and `applyEntryNormal` (both sides' hypotheses named and
  passed), `applyAll` (passes the budget to `applyEntries`). `server_kv_backend` (origin's, in the
  server's `Results.lean`) meets our unit 5a's `mvcc_NewStore_backend`, which now takes `0 ≤
  CompactionBatchLimit` and returns the compaction-capable readers (`storeReaderC`), `storeStop`
  and the compaction right `compactRight γ (-1)`: it gains the premise `hcfg` (`NewStore`'s), and
  gives up the compaction right (`compactRight_freeze`, under `wp_fupd`) to turn the readers into
  `storeReader`s (as `newWatchableStore` does), so its postcondition is origin's exactly.
- **Restated results**: `applyAll_model`, `applyEntries_model` and the linked `wp_apply*` follow
  their specs (the budget in the pre); `server_kv_backend` with the extra premise `hcfg`. Nothing
  of origin's weakened otherwise; `γ.kb = none` stays gone.
- **Trust base**: 172 axioms (ours; origin's 158 are among them), 31 sorries (ours: unit 5a's 22
  and the register's 9). Collections as merged: `server` the union of both sides' baselines
  (origin 114, ours 70: 119), which `--check` confirmed exactly; every other collection unchanged
  (adt 0/0, apply 36/0, backend 59/0, btree 0/0, cache 14/0, concurrency 13/0, leasing 8/0,
  mvcc 34/22, mvcc-compaction 22/22, raft 1/0, read 12/0, recipes 11/0, register 1/9,
  server-raft 6/0, txn 22/0, v3rpc 50/0).
- **For unit 4c** (`run`/`start`, chaining `applyAll` jobs): each `applyAll` now needs
  `txn.storeWTs E.γ (unapplied ai ms).length` (one per entry above the applied index; a conf
  change's is wasted). The supply is `server_kv_backend`'s `txn.storeWTs γ N` (the backend
  creator's `N` write-back tokens, `ownToks d.γB.wb`; free when `γ.kb = none`): the run loop's
  invariant must carry the remaining supply and split each batch's share off (a lemma
  `storeWTs γ (a + b) ⊣⊢ storeWTs γ a ∗ storeWTs γ b`, from `ownToks_add`; only the one-token
  `storeWTs_split` exists), so with a finite `N` the loop's spec bounds the entries applied (or
  takes the budget per batch as a premise of raft's hand-off).

Gates: `lake build` (no `sorry` but the generated axiomatized types', raft `Init`'s, Perennial's
and unit 5a's 22), `etc/goose.py --check` (no regeneration), every `gen-link.py` mode reproduces
(cache, concurrency, server, register, leasing, recipes, mvcc, txn, apply, adt, v3rpc, fmt,
context, read, backend), `etc/tcb-report.py --check` (172 axioms, 31 sorries), every collection's
`--check` as merged (above), `etc/verified-code.py`: etcd 794 of 3599 functions verified, 21
unfinished (etcd-raft 200 of 323, register 20 of 28).

## Build performance (2026-10-12, branch `proof-perf`)

Measured with `lake env lean` CPU time on the loaded shared machine (back to back, min of
repeats where noted), `set_option profiler true` and the CI record (`etc/build-report.py`).

- **A common tail proved once** (`wp_join`; statements unchanged). A case split followed by
  `all_goals` over the rest of the function verifies the rest once per case:
  `storeTxnCommon.rangeKeys` (`if rev <= 0`: 77s -> 38s CPU; it was the critical path's
  longest step), `Mergepgids` (`if b[0] < a[0]`: 70s -> 44s), `uberApplier.dispatch` (the
  deferred metrics after the second `switch`, once instead of once per request kind: 220s ->
  100s, 5.4 GiB -> 3.3 GiB; the longest step of the critical path after the merge of the
  apply package). Other proofs with the same shape, not changed: `Cache.Get` (`if !ready`, the
  rest twice), `watchStream.Watch` (twice two), `node.iterate` (the child recursion), where an
  early `return` in one case needs a join postcondition `(Q := ...)` that also covers it.
- **`raftOwn_access`** (`InvRaftPhys.lean`, 62 lemmas): `iframe` of the 32 field points-tos
  searched the goal's spine in an order that failed on most conjuncts (iris-lean's `Frame`
  search); framing by name in the goal's order: 135s -> 56s CPU.
- **`#print axioms`** (13 Results modules): printing the axiom names shortest-unambiguous
  (`MessageData.ofConstName`) took most of these modules (txn's 31s of which 25s); with
  `pp.fullNames` they print in full (`Perennial.fmt.pp`): txn 18s -> 5s, mvcc 10s -> 2s, apply
  10s -> 4s, ...
- **The unused-variables linter** walks a long proof's info tree: 13s of `dispatch`, 2-10s
  of `rangeKeys`; off for those two theorems only. Across the 40 costliest modules it is 3%.
- **Perennial** (`afc8f0432`, landed, not yet pinned here): the WP tactics' caches are
  per thread since `fb1ecb030` (the iframe race), but each access looked up its thread in
  interpreted code; `ThreadRef.withLocal` looks it up once per call. At the current pin plus
  that commit: `stepLeader` 107s -> 46s CPU (many WP theorems elaborated in parallel;
  before `fb1ecb030`, with the global caches, 186s), single-theorem files 4-6% faster.
  Needs a pin bump (Perennial `5857c495a..afc8f0432` has other changes: Goose evaluation
  order, `fmt`/`errors` specs).
- **Found, not changed**: each module pays ~1.1-1.5s CPU to import (2900 modules, mostly
  Lean's own `Lean.*`), which is nearly all of a Spec file's 1.6-2.6s: 874 Spec modules are
  ~1600s of CI's 9900s CPU. Lean's parallel elaboration (`Elab.async`) costs CPU: on a random
  sample of 14 files, 56s -> 50s with `-DElab.async=false` (wall about the same except for
  files of many theorems, e.g. `InvRaftPhys` 11s -> 33s wall). Native code for the tactics
  (`--load-dynlib` of iris-lean's shared library) did not change `InvRaftPhys`'s CPU: the
  profiler's "interpretation" is mostly the native callees (`isDefEq`, instance synthesis).
## Parallel elaboration and tactic state (2026-10-12, branch `flaky-iframe`)

`InvSTMRun.lean:254` (`stmMethods_ser`, the reset branch) failed in about 1 of 8 loaded full
builds and never alone. Cause: Perennial's `iframe ∗` marked its nested call of iris-lean's
`iframe ∗` with a process-global `IO.Ref Bool`. Lean elaborates a file's declarations in
parallel (`Elab.async`), so an `iframe` in one declaration that started while another
declaration's `iframe` had the flag set skipped Perennial's prepass, which frames
`stmRsetOwn pfx b ∅` against `stmRsetOwn pfx b STMSt.empty.reads` (equal by computation). The
evidence: running 16 copies of the file at once failed 5 of 32 runs (0 of 32 with
`-DElab.async=false`); a copy of the rule that records the thread holding the flag saw another
thread's flag at that `iframe` in each of the 5 failing runs of 48 and in none of the passing
ones; with the fixed tactic 0 of 80. `-Dgoose.iframe.prepass=false` reproduces the error
deterministically.

Perennial `fb1ecb030` (in the pinned `5857c495a`) makes the flag an option (`withOptions`, scoped to the call), and so
`wp_auto_angelic`'s flag; `wp_auto`'s per-call caches and hoisting candidates and
`needsGooseSimp`'s caches, which other threads' tactics reset, are per thread (`ThreadRef`).
Here, the reset branch unfolds `STMSt.empty` first, as the `*stm` branch did, and passes with the
prepass off.

About 55 other files pass only with `iframe`'s prepass (built with
`-Dgoose.iframe.prepass=false`): most of `cache/v3`'s constructors and demux proofs, the leasing
cache, the txn package, `concurrency`'s constructors, raft's `quorum`/`tracker` loops,
`raft__campaign`, `stepLeader`, the B-tree's `min`/`max`/`iterate`/`reset`. They converted loop
invariants and initial states (`sint.nat (W64 0)` against `0`, `nsat p []`, `X.init.f`) up to
computation, which the prepass now does on every run; making them syntactic is not cheap (one
`simp only [StoreState.init]` leaves `sint.nat (W64 0)` against `0`), and was not done.

## etcd's server: the raft wrapper (`server/v3/etcdserver/raft.go`): proved (2026-10-12)

Branch `server-raft`. The link between raft's `Ready` and the apply thread: every method of
`raftNode` in raft.go and `updateCommittedIndex` are specified and proved, with no `sorry`, and
linked in the server's `Link.lean` (`etc/link-lean-first-server.txt`; TCB collection
`etc/tcb-collections/server-raft.txt`). Design: `decisions.md`, "The server's raft wrapper".

- **Translation**: raft.go's `raftNode` methods, `updateCommittedIndex`, `raftReadyHandler`
  and the promoted `raft.Node` methods; v3.7's `IsEmptySnap`, `IsEmptyHardState`,
  `isHardStateEqual`, `SoftState`, `ReadState` and raftpb's `Message`, `Snapshot`,
  `SnapshotMetadata`, `HardState` with their getters (proved, `EtcdDeps/Proof/`).
  `storage.Storage` and `rafthttp.Transporter` are translated as interfaces (they were
  axiomatized types with `sorry` instances); `proto.Clone`'s axiom gets a case for a nil
  `*raftpb.Snapshot`.
- **Contracts** (`InvRaftNode.lean`, `isRaftNode`): `raft.Node` (a handshake `Ready` channel
  carrying the delivered log's half, `Advance` taking the busy token and the append receipt),
  the WAL (`Save`; `Close` succeeds), the `MemoryStorage`'s `Append` (right to receipt), the
  transport, the timeout detector, the ready handler's closures, the ticker (a bag channel or
  nil). `applyc` is an SPSC channel over a mono-list `cum` of forwarded logs
  (`InvRaftLoop.lean`: `cum_extend` for the loop's send, `rnApplyTok_recv` for the apply
  side's receive).
- **Proved**: `start` (the loop: the tick, the `Ready` case end to end, `stopped`; the deferred
  `onStop`), `processMessages` (every path: removed members, repeated `MsgAppResp`, the
  `MsgSnap` nonblocking send, heartbeats on time or late), `onStop`, `stop`, `tick`,
  `advanceTicks`, `getLatestTickTs`, `apply`, `ReadState`, `updateCommittedIndex`.
- **Gaps, by the contract**: no snapshots and no read states in a `Ready` (those branches are
  dead); the WAL's `Close` succeeds (otherwise `onStop` panics in the loop's goroutine); the
  contract's `Tick` takes a resource `T` that `start` gets from `□ |==> T` (a composition with
  node.go needs a bound on a run's ticks). The `Save` error path ends in `lg.Fatal`
  (postcondition `False`).
- **Not yet**: the apply side's use of `rnApplyTok_recv` (the apply thread still assumes its
  batch consecutive from `f0`, `InvApplier.lean`), and discharging the `raft.Node` contract by
  node.go's specs (needs raft retargeted to upstream, see "Retargeting raft to upstream").
- `etc/gen-link.py`: in a mode with several module roots (the server's `""` and `EtcdDeps`), a
  later root's spec at the same module path shadows the earlier one's (v3.7's `IsEmptySnap` has
  the verified raft's Go path).
- Gates: 68 axioms (66 on `lean`; new: zap's `Duration` and `Logger.Fatal`, names-only), 9 sorries (none the raft wrapper's), server 22/0, server-raft 6/0; `etc/goose.py --check` passes; the full `lake build` passes; etcd 587 of 3599 functions verified (577 on `lean`), 6077 of 45570 lines.

## Perennial `5857c495a`: soundness fixes (2026-10-12)

Branch `perennial-soundness` (worktree `/shared/etcd-grove-sound`). Perennial `f8f01eb44` →
`5857c495a`, which lands four soundness fixes (`8fcfd9fa4`, `3859a488b`/`4020291cc`, `cf98e5f15`,
`5857c495a`):
- **Integer semantics.** `uint32` `/` and `%` were the signed `int32` rules; integer division and
  remainder by zero returned a value (now the stuck `Panic "integer divide by zero"`); goose
  converted a shift count to the shifted operand's type, truncating it (now a `uint64`, a signed
  count through `go.shiftCount`, which panics when negative); `^x` was translated as boolean not.
  The translation changed in one place (`Code/go_etcd_io/etcd/cache/v3.lean`: the counts of the
  ring buffer's `>> 1` are `uint64` constants). The ring buffer's `moduloIndex`, `PeekLatest` and
  `Append` (`% len(r.buffer)`) discharge the new divisor check from `RingOk.cap_pos`; no proof here
  had relied on `x % 0`.
- **Timers.** `time.isTimer` has a third conjunct, `□ newTimerMade t` (opaque, given only by
  `wp_NewTimer`): a program's own `Timer` with a copied `C` no longer satisfies it (Go's `Stop`
  on it panics). `realTimer.Chan` and `demux.resyncLoop` destructure three parts.
- **`errors.As`.** `errors.wp_As` takes `errors.AsTarget T` (the target's element type is an
  interface or implements `error`; otherwise Go panics). `leasingKV.acquire`'s target is
  `*rpctypes.EtcdError`: that `EtcdError` implements `error` is a method-set fact the model lacks,
  so `clientErr` (the client's contract on its errors, `InvEtcdTxnOwn.lean`, which already assumed
  the typing fact `AsTypeTyped` of them) now has it as a conjunct. A class (as
  `context.ErrorStringIsError`) would do too, but would have to be threaded through
  `gen-link.py --leasing` and every leasing result.

Gates: `lake build` (2886 jobs), `etc/goose.py --check`, `etc/tcb-report.py --check` (69
axioms, 9 sorries: unchanged, the changed axioms are Perennial's) and every collection's
`--check` pass.

## The server's apply package (`server/v3/etcdserver/apply`)

Plan: `decisions.md`, "The server's apply: the hook through mvcc, the chain as triples, compaction
out of the model" (units 0 and A in parallel, then 1, 2, 3).

### Unit 0: translation and scaffolding (2026-10-12)

Branch `apply-u0` (worktree `/shared/etcd-grove-apply0`, off `lean` at `436f363c4`; Perennial
`e4e126e46` as a path dependency, `.lake/manifest-merge.json`).
- **Translation**: `apply.toml` translates everything but `metrics.go` (`alarms`, `init`: names
  only); the pin (`bc8b52a50`) translates as is: goose promotes the methods of the wrappers'
  embedded `applierV3` *interface* as `MethodUnfold` wrappers (`applierV3Capped.Range` is
  `MethodResolve applierV3.ty "Range"` on the field), the gap the plan expected does not exist.
  `etcdserverpb.toml` adds `InternalRaftRequest`, `RequestHeader`, `InternalRaftStringer`, the
  requests read and responses built (compaction, lease, alarm, auth), the alarm actions and
  types; `membershippb.toml` (the three cluster requests, `Member`, `RaftAttributes`,
  `Attributes`); names-only `authpb` (a goose gap: a struct listed by name whose field names a
  type of a package not imported, `AuthRoleGetResponse.Perm`, is emitted with a dangling
  reference), `semver/v3`, `etcdserver/api`, `etcdserver/version`; `lease.Lease` and
  `storage.BackendQuota` become translated structs (`lease.toml` imports `sync`,
  `storage.toml` `backend`). `etc/goose.py` lists the new packages (`github.com/Masterminds/
  semver=` root). The other names-only packages (`types`, `wait`, `pbutil`, `auth`, `v3alarm`,
  `membership`, `storage`, `traceutil`, `lease`) existed.
- **Base** (`apply/Base.lean`): `applyInit` (`alarms` holds a `*GaugeVec`; `ErrCorrupt` a fixed
  non-nil error) and the instances of the packages the apply package reaches, moved from the
  server's `BaseApply.lean` (which imports it): the apply package must not import the server's
  translation (unit 3 imports the other way). `InvRaftpb.lean` imports it instead of
  `BaseApply`; the cache's `Base` gains `membershippb`'s and `authpb`'s instances.
- **Scaffolding**: `InvRequest.lean` (`IRRModel`, `HeaderModel`, `irrDecode` (opaque; a decoder,
  not the plan's encoder: decisions), `irrId`, `dispatchKind`, `noSideEffect`,
  `needAdminPermission`, `semverValid`, `internalRaftRequestIs p rq`, persistent, the KV four
  as the txn package's `rangeRequestIs`/`putRequestIs`/`deleteRangeRequestIs`/`txnRequestIs`);
  `Contracts.lean` (`csContract P f Pre Q Post`, `isAuthStore`, `isApplyLessor` over
  `isTxnLessor` with `Grant`/`Revoke` (at the sole writer: deletions committed)/`Checkpoint`/
  `Lookup` (`leaseIs`: `ID`, `TTL()`, `Keys()`), `isAlarmStore`, `isCluster`, `isRaftStatus`,
  `isSnapshotServer`, `isConsistentIndexer`, `isQuota`, `isApplyKV` (txn's `isKV` and the
  store's `ReadView`)); `Wait.lean` (`waitOk`, moved from the server's `InvApplier.lean`, with
  `IsRegistered`; two server proofs take the new conjunct); `Chain.lean` (`Chain`, `baseChain`,
  `alarmChain`, `Outcome`, `chainStep` over the backend's relation, `applierSpec` with the
  layers' structs only: the method triples are unit 1's). `csContract` is defined here in the
  `apply` namespace; unit A's (mvcc/txn) should replace it at the merge.
- **Axioms** (12 new, each `Spec/`+`Proof/`): `semver.MustParse` (a version, or a panic, by
  `semverValid`), `semver.Version.LessThan`/`String` (non-nil versions), `types.ID.String`,
  `etcdserverpb.AlarmType.String` (through the field's address), `zap.Logger.Info`,
  `txn.WarnOfExpensiveRequest`/`WarnOfFailedRequest` (return), `prometheus.GaugeVec.
  WithLabelValues` (a gauge with mvcc's `gaugeSpec`: `Inc`/`Dec` are its contract),
  `context.WithValue` (Perennial translates `context` without its body; restricted to the auth
  store's two key types), `storage.NewBackendQuota` (an `isQuota`), `storage.BackendQuota.Cost`
  (the capped applier's, on the three request types). `pbutil.MustUnmarshalMessage` is
  generalized to a case per message type (`ConfChange` verbatim; `InternalRaftRequest`:
  `{p ↦ x ∗ d ↦* bs ∗ ⌜irrDecode bs = some rq⌝} … {internalRaftRequestIs p rq ∗ d ↦* bs}`),
  stated over raftpb's and etcdserverpb's assumptions; the server's `EtcdServer.apply` takes
  `hMU.1`. Not axioms: `time.Now`/`Since` (Perennial's), `context.Background` (Perennial's),
  the components (contracts). `errors.Is` (`dispatch`'s metrics) is the server's axiom, stated
  under the server's assumptions: unit 2 restates it or uses Perennial's `errors.wp_Is`.
- **The context** (`txnCtx`): the plan's "the proofs change little" assumed only the four entry
  points take the context; it flows to `txn`, `executeTxn`, `put`, `executeRange`,
  `deleteRange`, `traceutil.Get`. mvcc's `TxnRange.lean` gains `doneNil ctx` (`Done()` is `nil`:
  `context.TODO()`'s, `doneNil_todo`, and `WithValue`'s over it), `txnCtx ctx cd := doneNil ctx
  ∨ isContext ctx cd` (`txnCtx_todo`), `neverCd` (`neverDone_neverCd`, for `Txn` at `TODO()`)
  and `txnCtx_rangeCtx`; `rangeCtx true` takes `doneNil` in place of `TODO()`'s value. Every
  txn spec with a context (and `Results.lean`) says `mvcc.txnCtx ctx cd` for `context.isContext
  ctx cd`; `EnsureTrace`'s and `Get`'s axioms take and return a `txnCtx`. Proof changes:
  `executeRange`, `deleteRange` (the range read's `todo` from `txnCtx_rangeCtx`, 3 lines each),
  `applyCompare`, `getPrevKV` (one line). Unit A touches `deleteRange`, `put`, `txn`,
  `executeTxn`, `Put`, `DeleteRange`, `Txn` specs for the hook: their context lines are one-word
  changes.
- **`mvcc.store.Rev`** specified and proved (`store__Rev.lean`): the store's `ReadView`'s
  `Rev`, with the caller's tokens and certificate passed to `store.Read` (`log₀ <+: log`, `v =
  len log - 1`); in mvcc's link list and `Results.lean`.
- **Links**: `gen-link.py --apply` (namespace `apply`), `etc/link-lean-first-apply.txt` (the
  axioms; the txn package's `Put`/`DeleteRange`/`Range`/`Txn`/`ApplySecObserve` and mvcc's
  `store.Rev` as `@`; the package's 72 functions commented out with a first guess of their
  callees), `apply/Link.lean`, `apply/Results.lean` (skeleton), `etc/tcb-collections/apply.txt`.
  **Reuse rule**: a callee whose result a Link this one imports already defines (same full name)
  is imported, not redefined; searched: the `@` callees' Links and `REUSES` (the server's
  imports mvcc's). The server's Link drops `binary.bigEndian.wp_PutUint64`/`wp_Uint64` and
  `zap.wp_Error` and imports mvcc's Link; the trust report groups the server's Link with the
  apply package's (`61 root theorems in [server Link, apply Link, apply Results]`), which import
  mvcc's. `--leasing` did not reproduce on `lean` (txn's `compareInt64` made the bare name
  ambiguous): its list says `leasing_compareInt64` (its Link: one theorem moved).
- **A finding** (`issues/etcd-apply-alarm-gauge-reactivate.md`, reproduced): `Alarm` increments
  the alarm gauge for an alarm already active (`AlarmStore.Activate` returns the existing
  member): the gauge reads 2 for one alarm and 1 after it is disarmed. The plan's suspects:
  (1) `Apply` panics on `ID == 0` with no header: a precondition (pre-3.0 entries), `irrId`;
  (2) `dispatch`'s `Panic` default: every proposal site sets one field (`grep` of
  `InternalRaftRequest{` in `server/`), only a crafted WAL entry reaches it; (3)-(6) as the
  plan says, for units 1-2.
- **Notes on this repository**: `Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseCacheWrite`
  failed once in a full build (an `iframe` not seeing through a literal record's projection)
  and passed on the rebuild: a flaky elaboration, as `InvSTMRun` before.
- **Gates**: full `lake build` passes (2645 jobs); `ETCD_SRC=/shared/etcd etc/goose.py --check
  --perennial /shared/perennial-merge` passes; `gen-link.py` reproduces every Lean-first Link
  (`--cache/--server/--concurrency/--leasing/--recipes/--register/--mvcc/--txn/--apply`);
  `etc/tcb-report.py --check --update`: 81 axioms, 1 sorry (was 69, 1: the 12 above); every
  collection unchanged (server 26, mvcc 13, txn 20, cache 10, concurrency 12/1, recipes 11,
  leasing 8, btree 0, raft 1, register 1); apply 17 axioms, 0 sorries;
  `etc/verified-code.py --reuse --package go.etcd.io/etcd/server/v3/etcdserver/apply`: 73
  functions, 684 lines, 0 verified, 1 assumed (`Apply`, the server's axiom), 71 translated,
  1 not translated (`metrics.go`'s `init`); etcd 474 verified of 3599, 4943 of 45570 lines
  (unchanged: `store.Rev` is a promoted method, not a Go function).

### Unit A: the hook through mvcc (2026-10-12)

Branch `apply-uA` (worktree `/shared/etcd-grove-applyA`, off `lean` at `436f363c4`), in
parallel with unit 0. The backend's post-lock hook is in mvcc's contract and threaded through
the write path, in the shape of the server's `apply.Apply.spec`, so that the applier's contract
can be proved of the real write path (decisions.md, "mvcc: the batch lock runs the hook").

- **mvcc** (`InvStore.lean`): `batchTxSpec … Locked P f`/`isBatchTx … P f`/`isKeyBackend b View W
  P f`: `LockInsideApply : ∀ Pre Q, {Pre ∗ □ {P ∗ Pre} f() {Q}} … {Locked [] ∗ W ∗ Q}`, both
  `Unlock`s take `∗ P`, `LockOutsideApply` returns `Locked [] ∗ P`. `StoreNames.hook`/`hookFn`,
  `hookIs γ P f` (saved proposition and read-only ghost variable; `hookIs_agree`,
  `hookIs_agree_lc`), `isStore` holds `∃ P f, hookIs γ P f ∗ isKeyBackend … P f` (arity
  unchanged), `storeTxnWriteIs` the same `∃ Pw fw`. `csContract P f Pre Q Post`,
  `csContract_noHook`, `txnEndPre`/`txnEndPre_write`. Specs changed: `NewStore` (any `P f` in,
  `hookIs γ P f` out), `store.restore` (`isKeyBackend … P f`), `store.Write` (`hookIs ∗ Pre ∗ □
  {P ∗ Pre} f() {Q}` in, `Q` out), `storeTxnWrite.End` (`hookIs γ P f ∗ P` in),
  `metricsTxnWrite.End` (`txnEndPre γ kind` in), `writeView.Put`/`DeleteRange` (`hookIs ∗
  csContract` in, `Post` out). The read path is unchanged (its callers of `metricsTxnWrite.End`
  give `txnEndPre` of a read, `True`).
- **txn**: `Put` (`Pre` if the lease check fails, else `Post`), `DeleteRange` (`Post`), `Txn`
  (`Pre` on a failed check, `if txnReadonly t then Pre else Post` on success) take `csContract P
  f Pre Q Post ∗ hookIs γ P f`; the rest of their statements is unchanged. `put`/`deleteRange`/
  `txn`/`executeTxn` (inside an open transaction) are unchanged. The sole-writer results
  (`put_soleWriter`, `deleteRange_soleWriter`, `txn_runTxn`, `txn_readonly_no_revision`,
  `txn_check_error_no_write`) are restated at any `P f Pre Q Post`; the old statements are the
  instance `csContract_noHook`.
- **What the server bridge (unit 3) does with it**: `applierFor ua P f` becomes a definition
  whose store is `isStore s γ ∗ hookIs γ P f` (the backend's `P f` the server's `batchLockInv γ
  TM` and hook); the applier's KV calls pass the apply thread's `Pre`, hook triple
  (`hook_set_au`) and update (`writes_done`) to txn as one `csContract`, and get `Post` (a
  write) or `Pre` (no lock) back, exactly `apply.Apply.spec`'s `Post ∨ Pre`.
- Gates: full build clean (2600 jobs, no new `sorry`); `gen-link.py --mvcc/--txn/--server`
  reproduce (no Link change); `tcb-report.py --check`: baseline unchanged (69 axioms, 1 sorry;
  no new axiom), every collection unchanged (mvcc 13/0, txn 20/0, server 26/0, ...); `goose.py`
  untouched. (The base's first full build here once failed in
  `leasing/InvLeaseCacheWrite.lean:485`, an unsolved goal; the rebuild passed it unchanged:
  nondeterministic, not this unit's.)
- **Plan corrections**: `LockOutsideApply` cannot keep `{True} … {Locked []}`: `NewStore`'s first
  `Unlock` (now taking `P`) needs `P`, so it hands `P` out (the lock's invariant from the
  backend's creation). `StoreNames` gets two names (`hook`, `hookFn`), not one. The `P` agreement
  is under a later (saved propositions): `store.Write` and `End` spend a later credit.
  `writeView.Put`/`DeleteRange` open write transactions too and take `csContract`.

### Merge 0/A (2026-10-12)

`apply-u0` then `apply-uA` merged into `lean` (`--no-ff`). `lean` was at `d059a80ad`, not the
units' base `436f363c4`: the `mvcc` branch (the watchable store, units 1a to 2, and `zap.Logger.
Panic`/the key index's total specs) had been merged into it, so the merge also met mvcc's new
work. Perennial `e4e126e46` and the etcd pin `bc8b52a50` unchanged.
- **Conflicts** (all resolved by keeping both sides): `etc/tcb-baseline.txt` (the union: unit
  0's twelve and `lean`'s `trace.SpanFromContext`), `notes/STATUS.md` (one apply section, "Unit
  0" then "Unit A"), `notes/decisions.md` (both entries); txn's specs `DeleteRange`, `Txn` and
  `Results.lean`'s five sole-writer results (unit 0's `mvcc.txnCtx ctx cd` in place of
  `context.isContext ctx cd`, with unit A's `csContract P f Pre Q Post ∗ hookIs γ P f`; `Put`
  merged without conflict, both premises). No statement weakened.
- **`csContract` deduplicated**: unit 0's copy in `apply/Contracts.lean` (the same definition)
  removed; `Contracts.lean` imports mvcc's `InvStore` and uses `mvcc.csContract`;
  `csContract_pre` kept, of `mvcc.csContract`.
- **Fixes from the merge**: `store.Rev` (unit 0) calls `metricsTxnWrite.End`, which unit A gave
  the premise `txnEndPre γ kind`: of a read, `True` (as `readView.FirstRev`); `Rev` is read-only,
  no hook. The server's `Link.lean` regenerated: `lean`'s mvcc `Link` now links `zap.String`/
  `Int64` (the key index's callees), so by unit 0's reuse rule the server's imports them from
  mvcc's instead of redefining them (the build failed on the duplicates). No other proof changed.
- **Gates**: full build clean (2728 jobs); `gen-link.py` `--apply/--mvcc/--txn/--server/
  --leasing` (and `--adt/--cache/--recipes/--concurrency/--register`, `gen-btree-link.py`)
  reproduce; `etc/goose.py --check --perennial /shared/perennial-merge` (`ETCD_SRC=/shared/etcd`)
  passes; `etc/tcb-report.py --check`: 82 axioms, 1 sorry (the textual union: `lean`'s 70 and
  unit 0's 12; no `--update`); every collection matches (apply 17/0, txn 22/0, mvcc 17/0, server
  26/0, cache 10/0, concurrency 12/1, recipes 11/0, leasing 8/0, adt 0, btree 0, raft 1,
  register 1). Verified code: apply 73 functions, 0 verified, 1 assumed (`Apply`), 71
  translated, 684 lines (681 translated); etcd 494 verified of 3599 functions, 5149 of 45570
  lines (unchanged: `store.Rev` is a promoted method).

### Unit 1: the layers (2026-10-12)

Branch `apply-u1` (worktree `/shared/etcd-grove-apply1`, off `lean` at `504afa17e`). Every
function of `backend.go`, `quota.go`, `capped.go`, `corrupt.go` and `auth.go` is specified and
proved but the backend's `Compaction` (out of the model), the constructors package each layer,
`chainStep` is closed over the backend's relation (`Chain.lean`; decisions.md, the apply entry's
unit 1 bullets).
- **A translation fix** (`auth.toml`): `auth.AuthStore` was an axiomatized type (its methods'
  signatures name `context`, `etcdserverpb`, `authpb`, not imported), so its typed points-to was
  `sorry -- axiomatized type`, reached by `ApplierOptions` and the auth applier's `as` field;
  importing the three packages translates it (and `AuthBackend`, `AuthReadTx`, `AuthBatchTx`,
  `TokenProvider`) as interfaces, as `lease.toml` does for `Lessor`. Nothing else generated
  changed; `goose.py` itself untouched.
- **The triples** (`applierTriples E c ai`, `applierSpec E c a := ∃ ai, a = ok ai ∗ applierTriples
  E c ai`, persistent): one per `applierV3` method but `Compaction`, in the environment `E : AEnv`
  (the store `s`, its ghost names `γ`, the batch lock's `P` and hook `f`). Every method takes the
  apply thread's KV resources `kvOwn E log` (the store's reader slots, the sole writer of `log`,
  the state's leases known) and the chain's thread-owned resources `chainRes c a`, and returns
  them. The KV methods (`Put`, `DeleteRange`, `Range`, `Txn`) and `LeaseRevoke` (whose lessor
  deletes through the store) run the request `rq` `dispatch` passes on (`dispatchKind rq`, the
  field `some o`, the per-request premise) and return `∃ oc, ⌜chainStep backendStep c rq log oc⌝
  ∗ <answer> ∗ kvOwn E (oc.logAfter log) ∗ chainRes c a ∗ (Post ∨ Pre)` (`kvPost`; `Range` without
  the contract); the answers (`putOutcomeIs`, `deleteOutcomeIs`, `rangeOutcomeIs`,
  `txnOutcomeIs`, `revokeOutcomeIs`) carry the txn package's response predicates at their exact
  model values for an applied outcome, the error of a rejection (`rejErrIs`: `ErrCorrupt`,
  `ErrNoSpace`, the auth store's, the backend's), the quota's `ErrNoSpace` after a write
  (`noSpaceErrIs`). The other methods (`mPre`/`mPost`) take `csContract P f Pre Q Post` where
  they may write and return `Post ∨ Pre`, the log as it is; one triple per shape, over the
  method name (`respMethods`, `resp0Methods`, `clusterMethods`, the request facts the layers
  read: `reqFacts`). `Apply` is higher-order: `{irrWrapperIs r rq skip ∗ A ∗ {chainRes c a ∗ A}
  af(r, v3) {ar; chainRes c a ∗ B ar}} a.Apply(r, v3, af) {ar; B ar ∨ (⌜needAdminPermission rq⌝ ∗
  A ∗ rejectResultIs ar)}`.
- **`backendStep rq log o`**: by `dispatchKind rq`: a put is `put_soleWriter`'s three cases (the
  lease not found, the ignore flag's key missing: `.rejected .backend`; else `log ++
  [[putChangeOf …]]`); a delete the filter (`commitLog log delChanges`) or the range read's error;
  a range `.applied log false`; a transaction `checkTxn`'s error or `srvRunTxn` committed (none
  for a read-only one); a revocation the lessor's deletions (`commitLog log pend`, all
  deletions); compaction and an empty request `False`; the others the log as it is or the
  component's error.
- **`chainRes`, the auth mutex**: `chainRes (.auth c) a` owns the auth layer's `authInfo`
  (`authInfoOwn p`) beside the inner's; the other layers own nothing. `aa.mu` is a Perennial
  mutex whose resource is `authInfoOwn p` (`authIs`, made by `newAuthApplierV3` with
  `init_Mutex`): `Apply` locks it, owns `authInfo`, hands it to the `applyFunc` through the
  inner's `Apply` (whose `A`/`B` frame it), resets it, unlocks. So `Apply`'s caller owns
  nothing of the chain (its triple has no `chainRes`), and `dispatch` gets `chainRes` from the
  `applyFunc`'s precondition. Rejected: `authInfo` thread-owned with a trivial mutex resource
  (`Apply`'s statement would carry `chainRes`, and unit 2's `uberOwn` with it).
- **The constructors** package the layers: `{backendOptsOk E opts} newApplierV3Backend(opts)
  {a; applierSpec E .backend a}`, `{applierSpec E c app} newQuotaApplierV3(lg, cfg, be, app) {a;
  applierSpec E (.quota c) a}`, `newApplierV3Capped`, `newApplierV3Corrupt` (a pointer `p`,
  `applierSpec E (.corrupt c) (mkOk (*applierV3Corrupt) p)`), `newAuthApplierV3(as, base, lessor)`
  (with `isAuthStore`, `isApplyLessor`). A constructor's proof takes its layer's method specs as
  hypotheses (the link) and proves the promoted methods through the inner's triples
  (`chainRes_<layer>_out`/`_in`, `Packaging.lean`). No thread-owned part is returned: the auth
  layer's resource is in its mutex.
- **Lemmas**: `txn/SoleWriterKV.lean` (`put_soleWriter_of`, `deleteRange_soleWriter_of`,
  `range_soleWriter_of`: the txn results over their callee's spec, moved from txn's
  `Results.lean`, which restates them unchanged); `apply/KVLemmas.lean` (the leases known across
  a put, a delete, a revocation's deletions); `apply/Packaging.lean`; `WrapLemmas.lean` (an `err = nil` answer is an applied outcome: the quota layer), `AuthLemmas.lean` (`checkTxnPermission`'s Löb proof over `checkTxnReqsPermission`'s body, the auth layer's rejection/pass lemmas), `BackendLemmas2.lean` (`go.NotInterface go.uint64`, a missing Perennial instance: `types.ID.String`'s method resolution stalls without it; belongs in Perennial's `PostLifting.lean`).
- **Contracts**: unit 0's contracts used as stated, none changed (the lessor's `Checkpoint` is one critical section per call: the finding below). Not in the contracts: `cappedIs`/`corruptIs` have no `Persistent` instance (the proofs `ipersist`; harmless).
- **`Compaction`**: no triple in `applierSpec`, `backendStep` is `False` of a compaction; the
  corrupt applier's `Compaction` (`ErrCorrupt`) is proved, the backend's is not specified.
  Unit 2's `dispatch` takes `dispatchKind rq ≠ .compaction` and never calls a `Compaction`.
- **A finding** (`issues/etcd-apply-lease-checkpoint-sections.md`, reproduced): a lease checkpoint
  entry with several checkpoints writes the backend in one critical section per checkpoint
  (`lessor.Checkpoint` persists each lease in its own `LockInsideApply`), so a backend commit
  between two persists the entry's consistent index with part of its writes; the backend's
  `LeaseCheckpoint` triple takes a request with at most one checkpoint (the premise, in its
  request facts and `rqOk`; not a weaker contract). A fix exists on the fork branch
  `lease-checkpoint-one-section` (2a163496c: `Lessor.Checkpoint` takes the whole batch and
  persists it in one critical section); the issue file is the upstream draft.
- **The plan's suspects**: (3) `quotaApplierV3.Put`/`Txn`/`LeaseGrant` apply, then answer
  `ErrNoSpace` if the quota said no: by design, the apply loop raises the `NOSPACE` alarm on that
  error (`server.go:1976`); the client gets an error for a committed write; the spec says so
  (`chainStep`'s quota case, `.applied log' true`); not a bug. (5) `authApplierV3.UserGet`/
  `RoleGet` reset `authInfo` and return an empty response with the error, so `dispatch`'s result
  has both `Resp` (not nil) and `Err`, unlike the other rejections (`Resp` nil): harmless
  (`raftRequest` reads `Err` first; `Apply` resets `authInfo` again); the triples say nothing of
  the response. (6) the corrupt applier blocks the KV requests, compactions and lease grants and
  revocations only; alarms (so that the alarm can be disarmed), auth, cluster requests and lease
  checkpoints go through: by design (`corruptRejects`).
- **Results** (`apply/Results.lean`, unit 1's section): `chain_put`, `chain_deleteRange`,
  `chain_range`, `chain_txn` at `alarmChain ns cr` (`baseChain` at `false false`), the outcome in
  the txn package's terms (`putModel`, `deleteModel`, `txnModel`, `quotaAfter`; `alarmPut`, ...),
  with `#print axioms`.
- **Gates**: full `lake build` clean (2860 jobs, no `sorry`); `gen-link.py --apply` reproduces `Link.lean`
  (81 results; `gen-link.py` learned that an `@` callee's result taking the cache's assumptions is
  named in its own Link without the namespace prefix: txn's `wp_Txn`), `--txn/--mvcc/--server/
  --leasing/--cache/--recipes/--concurrency/--register/--adt` unchanged; `etc/goose.py --check
  --perennial /shared/perennial-merge` (`ETCD_SRC=/shared/etcd`) passes with the `auth.toml`
  change; `tcb-report.py --check`: 82 axioms, 1 sorry (unchanged: no new axiom); every collection
  matches but apply's, updated: 35 axioms, 0 sorries (was 17: its results now reach the txn
  package's and mvcc's trust base through `txn.Put`/...`/store.Rev`, and `context.TODO`'s proof
  is linked); `verified-code.py --reuse --package go.etcd.io/etcd/server/v3/etcdserver/apply`: 73
  functions, 63 verified (all sorry-free), 1 assumed (`Apply`, the server's axiom), 8 translated
  (the backend's `Compaction`, `uber_applier.go`'s 6, `noSideEffect`), 486 of 684 lines verified;
  backend.go 31 of 32, auth.go 16/16, quota.go 4/4, capped.go 4/4, corrupt.go 8/8; etcd 557
  verified of 3599 functions, 5635 of 45570 lines (was 494, 5149)..
### Unit 2: the uber-applier and `Apply` (2026-10-12)

Branch `apply-u2` (worktree `/shared/etcd-grove-apply2`, off `lean` at `4d2842e39`). Every
function of `uber_applier.go` and `apply.go` is specified and proved and linked: `NewUberApplier`,
`newApplierV3`, `uberApplier.restoreAlarms`, `uberApplier.Apply`, `uberApplier.dispatch`,
`uberApplier.Alarm`, `apply.Apply`, `noSideEffect` (vocabulary `apply/InvUber.lean`, lemmas
`UberLemmas.lean`, `DispatchLemmas.lean`).
- **The uber-applier**: `uberIs E p opts` (persistent: `lg`, `alarmStore`,
  `warningApplyDuration` from the options, `backendOptsOk E opts`, the base chain's applier
  `applyV3base ↦□ base ∗ applierSpec E baseChain base`); `uberOwn E p c` (the thread's:
  `applyV3 ↦ a ∗ applierSpec E c a`). `applierFor ua E := ∃ p opts, ua = mkOk(*uberApplier) p ∗
  uberIs E p opts` (persistent; takes the environment `E`, not the server's `P f`: the
  persistent part must name the same store and ghost names as the thread's part, which `P f`
  alone do not pin; the server's `P f` are `E.P E.f`). `applyKV E ua x := ∃ p, ua = mkOk p ∗
  uberOwn E p x.chain ∗ kvOwn E x.log`, `x : ApplyKV := {log, chain}`.
- **Triples**: `NewUberApplier`: `{backendOptsOk E opts} … {ua; ∃ p, ua = mkOk p ∗ uberIs E p
  opts ∗ ∃ ns cr, uberOwn E p (alarmChain ns cr)}`; `newApplierV3`: `applierSpec E baseChain`;
  `restoreAlarms`: `{uberIs ∗ applyV3 ↦ a} … {∃ ns cr, uberOwn E p (alarmChain ns cr)}` (the
  alarm store's `Get` returns any slice); `Alarm`: the current applier's `Alarm` (`mPre`/`mPost`)
  and the chain afterwards the same or `alarmChain ns cr`; `dispatch` (the `applyFunc` the
  chain's `Apply` calls, a method value): `{uberIs ∗ irrWrapperIs r rq skip ∗ chainRes c a ∗
  applyV3 ↦ a ∗ applierSpec E c a ∗ kvOwn E log ∗ cPre v3 E.P E.f Pre Q Post ∗ ⌜rqOk log rq ∧
  dispatchOk rq⌝} … {ar; chainRes c a ∗ ∃ a' c' o, applyV3 ↦ a' ∗ applierSpec E c' a' ∗ kvOwn E
  (o.logAfter log) ∗ cPost v3 Pre Post ∗ ⌜dispatchStep c rq v3 log o ∧ chainAfter rq v3 c c'⌝ ∗
  dispatchResult rq v3 log skip ar o}`; `uberApplier.Apply`: through `applierSpec`'s `Apply`
  with `dispatch`'s triple as the premise (`A` the thread's `applyV3`, KV and contract; `B`
  `dispatch`'s post), the admin rejection persisted (`rejectedResultIs`); `apply.Apply`: below.
- **`apply.Apply.spec`** (the server's shape kept, the KV added): `∀ lg e m ua w v3 E Pre Q Post x
  rq id, {isPkgInit ∗ applierFor ua E ∗ waitOk w ∗ ⌜lg ≠ null⌝ ∗ entryAt e m ∗ (if v3 then □
  {E.P ∗ Pre} E.f() {Q} ∗ (Q ={⊤}=∗ E.P ∗ Post) else True) ∗ Pre ∗ applyKV E ua x ∗
  ⌜irrDecode m.data = some rq ∧ irrId rq = some id ∧ rqOk x.log rq ∧ dispatchOk rq⌝} Apply(lg,
  e, ua, w, v3) {(ar, id'); (if v3 then Post ∨ Pre else Pre) ∗ resultErrOk ar ∗ ⌜id' = id⌝ ∗ ∃
  x' out, applyKV E ua x' ∗ ⌜applyStep rq v3 x x' out⌝ ∗ applyResultIs rq v3 x.log ar out}`.
  `applyStep`: `skipped` (`noSideEffect rq`, `x' = x`), `rejected` (`needAdminPermission rq`,
  `x' = x`), `dispatched o skip` (`skip → rq.txn.isSome`, `dispatchStep x.chain rq v3 x.log o`,
  `x'.log = o.logAfter x.log`, `chainAfter`: the chain the same or, with `v3` and an alarm
  request, `alarmChain ns cr`). `dispatchStep`: the first `switch`'s requests (cluster,
  `DowngradeVersionTest`) and everything without `v3` leave the KV (`.applied log false`); the
  KV requests and the revocation are `chainStep backendStep c`; the others leave the log.
  `dispatchResult`: a fresh read-only `Result` (`ar ↦□ v`) holding `dispatchAnswer` (unit 1's
  outcome predicates at the response pointer: `putOutcomeIs`, ..., `revokeOutcomeIs`; `Resp` and
  `Err` nil for the first `switch`), or `nil` without `v3`.
- **Without `v3` nothing is written**: unit 1's cluster triple took the critical-section
  contract whatever `shouldApplyV3`, so `apply.Apply` without `v3` (no hook triple from the
  caller) could not call it. The cluster contract (`isCluster`: `SetVersion`, `UpdateAttributes`,
  `SetDowngradeInfo`) now takes `cPre b P f Pre Q Post` (`csContract` if `b`, else `Pre`) and
  returns `cPost b Pre Post` (`Post ∨ Pre` / `Pre`), as membership's `RaftCluster` writes the
  backend only `if shouldApplyV3`; `applierTriples`' cluster triple uses `mPreV v3`/`mPostV v3`.
  A strictly stronger restatement of unit 1's (`cPre false = Pre`, which `csContract` gives;
  `Pre ⊢ cPost`); the three backend proofs and the five constructors' cluster cases changed by
  name only.
- **The server: unit 3's** (the plan's fallback). The server's three proofs cannot take the new
  precondition without the KV fold: `rqOk x.log rq` depends on the log the earlier entries
  committed (`putOk`'s room for a revision, `TxnPre`), so an existentially threaded `applyKV`
  with "no claim about `x'`" cannot discharge it; that is `applyEntries_model`. So the server
  keeps its contract as the axiom `apply.Apply_server.wp_proof : apply.Apply_server.spec`
  (`Spec/.../apply/Apply_server.lean`, the old statement verbatim, renamed; not derivable from
  the new one, which has more premises), `applierFor` stays the server's axiom
  (`InvApplier.lean`, unchanged), `applyEntryNormal` takes `hA : apply.Apply_server.spec`, the
  server's link list says `apply_Apply_server`. Unit 3 switches `applyEntryNormal` to
  `apply.Apply.spec`, makes the server's `applierFor` `∃ E, E.P = batchLockInv γ TM ∧ E.f = hook
  ∗ apply.applierFor ua E` (or uses `apply.applierFor` directly), threads `applyKV`, and drops
  both axioms. The server's results are unchanged; they rest on `apply.Apply_server.wp_proof`
  (the renamed axiom).
- **`resultOk`**: the server's (`InvApplier.lean`) is untouched (on `lean` it now also asks
  `applyErrIs err`, the error tree `errors.Is` needs); the apply package states `resultErrOk ar`
  (the `Err` field readable) in its own `InvUber.lean`. **Gap for the merge with `lean`**: the
  new `errors.wp_Is` model (Perennial `e6ec34885`) needs `applyErrIs` of every error `apply.Apply`
  returns, which this unit (built at Perennial `e4e126e46`, without `errors.TreeTyped`) does not
  state: `dispatchResult`/`rejErrIs`/the components' contracts carry no error tree, and
  `dispatch`'s `errors.Is(ar.Err, mvcc.ErrCompacted)` uses this branch's `errors.Is.spec` (any
  error, any target; restated here under `errors.Assumptions`). The merge must give the
  contracts' errors (auth store, lessor, alarm store, cluster) and the chain's own (`ErrCorrupt`,
  `ErrNoSpace`, txn's/mvcc's) `applyErrIs`, state it in `dispatchAnswer`/`rejectedResultIs`, and
  use Perennial's `errors.wp_Is` in `dispatch`.
- **`errors.Is`**: Perennial's `errors.wp_Is` needs the error's tree, which an error from a
  names-only component does not come with (at this pin); the server's axiom `errors.Is.spec`
  ("returns some bool") is restated under the `errors` package's assumptions (it was the
  server's), so the apply package's `dispatch` uses the same axiom (`errors_Is` in its link list).
  On `lean` the axiom is now a proof with error-tree premises: see the gap above.
- **The plan's suspects**: (1) `Apply` panics on `ID == 0` with a nil header: the premise
  `irrId rq = some id` (a precondition note: pre-3.0 entries; every current proposer sets an
  id). (2) `dispatch`'s `default` panic: an all-nil request has `dispatchKind = .none`; the
  premise `dispatchOk rq` (`≠ .compaction ∧ ≠ .none`); `Apply`'s callers can exclude it only
  from the proposers (unit 0: every `InternalRaftRequest{` in `server/` sets a field; only a
  crafted WAL entry has none), so it rises to the entry premise unit 3 states.
- **A finding** (`issues/etcd-apply-authstatus-metric-label.md`, minor): `dispatch` does not set
  `op` for `AuthStatus`, whose apply latency is recorded under `op="unknown"`.
- **Results** (`apply/Results.lean`, unit 2's section): `apply_kv`, `apply_readonly_no_write`,
  `apply_rejected_no_write`, `apply_no_v3_no_write` (over `applyStep`, the relation of
  `wp_Apply`'s postcondition), `chainStep_log_same`; `#print axioms` of `wp_Apply`,
  `wp_NewUberApplier`, `uberApplier.wp_dispatch` and the four.
- **Gates**: full `lake build` clean (2879 jobs, no `sorry` of ours); `gen-link.py` reproduces
  every Lean-first Link (`--apply`: unit 2's 8 functions and `errors_Is` linked; `--server`:
  `apply_Apply_server` for `apply_Apply`; `--cache/--concurrency/--leasing/--recipes/--register/
  --mvcc/--txn/--adt` unchanged); `tcb-report.py --check --update`: 82 axioms, 1 sorry (the plan
  expected 80: `applierFor`'s two axioms stay until unit 3; the only change is the rename
  `apply.Apply.wp_proof` → `apply.Apply_server.wp_proof`); collections: server 26/0 (the same
  rename), apply 37/0 (was 35: `errors.Is.wp_proof` and `txn.ApplySecObserve.wp_proof`, `dispatch`'s
  metrics), the others unchanged (txn 22, mvcc 17, cache 10, concurrency 12/1, recipes 11,
  leasing 8, adt 0, btree 0, raft 1, register 1); `verified-code.py --reuse --package
  go.etcd.io/etcd/server/v3/etcdserver/apply`: 73 functions, 71 verified (all sorry-free), 1
  translated (the backend's `Compaction`), 1 not translated (`init`), 667 of 684 lines; etcd 565
  verified of 3599 functions, 5816 of 45570 lines (was 557, 5635); `goose.py` untouched. The
  `dispatch` proof is one declaration of 30 cases (`maxHeartbeats 10000000`, about 2.5 min).
- **What unit 3 must know**: the server's `applierFor` (axiom) becomes `apply.applierFor ua E`
  with `E.P = batchLockInv γ TM`, `E.f = v.hook` (the server's `srvFieldsAt` holds it
  persistently); `applyEntryNormal` takes `apply.Apply.spec` (premises: `waitOk w` and `lg ≠ null`,
  which it has; `applyKV E ua x`; `irrDecode m.data = some rq`, `irrId rq = some id`, `rqOk x.log
  rq`, `dispatchOk rq` per entry: `entriesFrom`'s premise must say them of the state the earlier
  entries reach, i.e. be stated over the fold of `applyStep`), returns `x'` with `applyStep`;
  the server's `resultOk` (with `applyErrIs` on `lean`) from `resultErrOk` plus the error trees
  (the merge's gap above); the axiom `apply.Apply_server` and `applierFor`/`_persistent` go; the
  apply package's `hlc` is `HasLC.hasLC` (the server's proofs are generic in `hlc`: they get
  instantiated). The v3alarm `AlarmStore.Get` now proved on `lean` can feed `isAlarmStore`'s
  `Get` part (the contract's `Get` triple, `{True} … {sl; True}`, is what `restoreAlarms` uses).

### Merge 2 (2026-10-12)

Unit 2 (`apply-u2`, 4 commits `a70019085..75470a7a5` off `4d2842e39`) merged into `lean`
(`8a195c9da`: the three merges of `origin/lean` since, Perennial `f8f01eb44`, the remote's
standard-library and small etcd axioms proved, the warnings fixed), with the `applyErrIs` gap
closed. Built with `lake build --packages=.lake/manifest-f8f01eb.json` (2904 jobs).
- **Conflicts**: `Spec/errors/Is.lean` (`lean`'s statement, the proof's: an error tree and a
  pointer target; unit 2's generalization kept: under `errors.Assumptions`, so the apply package
  uses it; `Proof/errors/Is.lean` merged clean to `lean`'s proof under `errors.Assumptions`);
  `etc/tcb-baseline.txt` (`lean`'s with `apply.Apply.wp_proof` → `apply.Apply_server.wp_proof`:
  `txn.ApplySecObserve.wp_proof` was already in it, unit 2's `errors.Is` axiom is gone); the
  server's collection (the same rename); the server's `Link.lean` (regenerated, `--server`);
  `notes/STATUS.md` (this section after unit 2's). Without conflict: `applyEntryNormal` (unit 2's
  `hA : apply.Apply_server.spec` with `lean`'s `srvLgReader` threading and `HasLC.hasLC`), the
  non-nil trace facts (unit 2's proofs call nothing that needs them), the alarm-store names
  (`apply.isAlarmStore` and `EtcdGrove.isAlarmStore` never met in one proof).
- **The build after the merge** failed only in `uberApplier.dispatch`: `errors.Is(ar.Err,
  mvcc.ErrCompacted)` now needs the error's tree.
- **`applyErrIs` closed**: every error `apply.Apply` returns (and `dispatch` compares) is one
  `errors.Is` can take. `apply.resultErrOk ar := ⌜ar = null⌝ ∨ ∃ err, Err ↦□ err ∗ applyErrIs err`
  is now the server's `resultOk` body (`applyErrIs` moved from `InvApplier.lean` to
  `apply/Base.lean`, with `errLeaf` (an `errors.New` error: pointer, leaf, no `Is`; the recipes'
  `errNewLeaf`), `errVarLeaf`, `applyErrIs_nil`, `applyErrIs_leaf`, `errVar_applyErrIs`). Where
  the errors come from:
  - the auth store's and the lessor's: their contracts assert `applyErrIs err` (`permCheck2/3`,
    `IsAdminPermitted`, `AuthEnable`, `Authenticate`, `authReqContract`, `Grant`, `Revoke`,
    `Checkpoint`): an assumption of the trust boundary, as `clientErrIs` is the client's
    (documented in `Contracts.lean`; etcd's `auth` and `lease` errors are `errors.New` errors);
    the alarm store's and the cluster's methods return no error;
  - the error variables: `applyInit` gains `applyErrVars`, `ErrCorrupt`, `ErrNoSpace`,
    `ErrKeyNotFound`, `lease.ErrLeaseNotFound`, `mvcc.ErrFutureRev`, `mvcc.ErrCompacted` each an
    `errors.New` error (an assumption about those packages' initialization, stated in the apply
    package's facts as the txn package states its foreign errors);
  - the KV answers name their errors; `DispatchLemmas` derives `applyErrIs` from them
    (`putOutcomeIs_errIs`, `deleteOutcomeIs_errIs`, `rangeOutcomeIs_errIs`, `txnOutcomeIs_errIs`,
    `revokeOutcomeIs_errIs`, `keep_errIs`); the auth rejection (`rejErrIs .auth`) and the
    lessor's revocation error (`revokeOutcomeIs .applied`) now carry it;
  - the range read's context error (mvcc's `fmt.Errorf("…: %w", ctx.Err())`, which no tree
    describes) is excluded: `txn.Range`/`txn.DeleteRange` (and `range_soleWriter_of`,
    `deleteRange_soleWriter_of`, the txn Results' restatements) take `nd` (a context never done,
    as `executeRange`/`deleteRange` did), and the backend calls them at `context.TODO()`
    (`neverCd`); `rangeOutcomeIs .applied` says `err = nil ∨` a future revision, and a delete's
    backend rejection is `False`;
  - the methods that leave the log (`respMethods`, `resp0Methods`, `AuthStatus`) carry
    `applyErrIs err` in `applierTriples`; `dispatchResult` and `rejectedResultIs` carry
    `applyErrIs v.Err'`; `dispatch` calls Perennial's `errors.wp_Is` (through `errors.Is.spec`)
    with `ErrCompacted` as the pointer target.
  Proofs changed: the 22 backend/auth methods that leave the log, the auth checks
  (`checkPutAuth`, `checkLeasePuts(Keys)`, `AuthLemmas`), the auth layer's KV methods and
  `Apply`, the wrappers (their `ErrCorrupt`/`ErrNoSpace` now from `applyErrVars`), the four
  constructors' promoted methods, `uberApplier.Alarm`/`Apply`, `UberLemmas`, `dispatch`; txn's
  `Range`, `DeleteRange`, `Count`, `SoleWriterKV`, `Results`. Nothing remains assumed beyond the
  two named assumptions above (the contracts' errors, `applyErrVars`).
- **Gates**: `lake build` clean (2904 jobs); every `gen-link.py` mode reproduces (`--apply
  --server --mvcc --txn --leasing --cache --recipes --concurrency --register --adt`);
  `goose.py --check --perennial /shared/perennial-f8f01eb` passes; `tcb-report.py --check`
  matches the computed baseline (69 axioms, 9 sorries: `lean`'s, `apply.Apply.wp_proof` renamed
  `apply.Apply_server.wp_proof`; no update); collections: apply 31 → 32 (`txn.ApplySecObserve`,
  `dispatch`'s metrics; unit 2's `errors.Is` axiom is `lean`'s proof), server 18 (the rename),
  the others unchanged (txn 18, mvcc 12, cache 10, concurrency 12, recipes 11, leasing 8,
  register 1/9, raft 1, adt 0, btree 0); `verified-code.py --reuse --package …/apply`: 71 of 73
  functions verified (all sorry-free), 667 of 684 lines; etcd 577 of 3599 functions, 5876 of
  45570 lines (was 568, 5688).
- **Flaky in a full build**: `leasing/InvLeaseCacheWrite.lean` and `concurrency/InvSTMRun.lean`
  fail nondeterministically in a full `lake build` and pass alone (rebuild once).
- **For unit 3**: `apply.resultErrOk` and the server's `resultOk` have the same body (one
  `applyErrIs`), so `apply.Apply.spec`'s post gives `resultOk` by `unfold`; the rest as unit 2's
  "What unit 3 must know".

### Unit 3: the server bridge (2026-10-12)

Branch `apply-u3` (worktree `/shared/etcd-grove-apply3`, off `lean` at `3476ee914`). The apply
thread's proofs now use the proved `apply.Apply` (`apply.Apply.spec`, unit 2) and state what the
committed entries do to the KV.
- **The switch-over** (`InvApplier.lean`): the axioms `applierFor`/`applierFor_persistent` and
  `apply.Apply_server.wp_proof` (with `Spec/`/`Proof/.../apply/Apply_server.lean`) are gone. The
  server's fields hold `apply.applierFor v.ua E` with `⌜E.P = batchLockInv γ TM ∧ E.f =
  v.hook⌝`, the applier's environment `E : apply.AEnv` a parameter: `isServer s γ ci TM E`
  (`decisions.md`, apply entry, "`E` a parameter of `isServer`"). The apply thread owns
  `srvApplyKV s E x := ∃ ua, srvUberApplyAddr s ↦□ ua ∗ apply.applyKV E ua x` (the `ua` the
  field's: the two `↦□` agree), threaded through the three specs. `applyConfChange`'s contract
  (an axiom) named the old `applierFor ua P f`: restated at `apply.applierFor ua E` (`E.P`,
  `E.f`), at `HasLC.hasLC`. The server's `resultOk` went (`apply.resultErrOk`, the same body).
  The server's `Link.lean` imports `apply.wp_Apply` (`apply_Apply: @`).
- **One entry** (`entryOk`, `entryStep`): `entryOk x m := m.data = [] ∨ ∃ rq, irrDecode m.data =
  some rq ∧ (∃ id, irrId rq = some id) ∧ rqOk x.log rq ∧ dispatchOk rq`; `entryStep m v3 x x' out
  := if m.data = [] then x' = x ∧ out = .skipped else ∃ rq id, irrDecode m.data = some rq ∧
  irrId rq = some id ∧ applyStep rq v3 x x' out`. `applyEntryNormal`'s spec adds `srvApplyKV s E
  x ∗ ⌜entryOk x m⌝` in and `∃ x' out, srvApplyKV s E x' ∗ ⌜entryStep m v3 x x' out⌝` out; the
  consistent-index parts are unchanged.
- **A batch** (`batchStep`, `entriesStep`, `entriesOk`, `unapplied`): `batchStep c m x x' := if
  m.typ = W32 0 then ∃ out, entryStep m (decide (uint.Z c < uint.Z m.index)) x x' out else x' =
  x` (`c` the consistent index the batch starts at: in `apply`'s loop `index > ci` iff `index >
  c`); `entriesStep c ms` their composition (`[]`: `x' = x`); `entriesOk c (m :: ms) x := (m.typ =
  W32 0 → entryOk x m) ∧ ∀ x1, batchStep c m x x1 → entriesOk c ms x1` (every run: the relation
  is not a function); `unapplied ai ms` the entries above the applied index (a filter;
  `unapplied_eq_drop`: the code's offset). `apply`: `entriesOk (ciEff γ st.k) ms x →` and
  `srvApplyKV s E x` in, `∃ x', srvApplyKV s E x' ∗ ⌜entriesStep (ciEff γ st.k) ms x x'⌝` out;
  `applyEntries`: the same over `unapplied ai ms`. Lemmas `entriesStep_append`,
  `entriesStep_take_succ`, `entriesOk_drop`, `entriesStep_trace` (`InvApplier.lean`).
- **What the premises mean**: every normal entry of a batch, at every state the batch's earlier
  entries can reach it in, has no data or data that decode to an `InternalRaftRequest` with an
  id or a header, whose request is neither a compaction nor empty and satisfies the txn
  package's premises at that state (`rqOk`: room for the revisions (`putOk`/`delOk`/`rangeOk`),
  fewer than `2 ^ 63` keys for a delete, a valid sort target and the sort's premise for a range,
  `TxnPre` for a transaction, one checkpoint per lease checkpoint request, a valid semver). Asked of the replayed entries too (`apply.Apply.spec`'s premise
  does not depend on `v3`; stronger than the code needs: left open).
- **Results** (`Proof/.../etcdserver/Results.lean`, the server's first; found by
  `proof_roots.py` as every `Results.lean`): `applyEntries_model` (the linked `applyEntries`),
  `applyEntries_trace`, `applyEntries_kv` (in a run from an `alarmChain`, every normal KV entry
  above `ci` is skipped or rejected by the admin check, or dispatched to the chain's outcome:
  `alarmPut`/`alarmDelete`/`alarmRange`/`alarmTxn`, the txn package's `putModel`/`deleteModel`/
  the range/`txnModel`, committing `o.logAfter`: `apply.apply_kv`), `applyEntries_replay_no_write`
  and `applyEntries_replay_all` (entries at or below `ci` change nothing: the double-apply half
  of the consistent-index guarantee, on the KV), `applyEntries_rejected_no_write`; one-entry
  lemmas `batchStep_alarmChain`, `entryStep_kv`, `entryStep_no_v3`,
  `entryStep_rejected_no_write`. `#print axioms` of each: the pure ones rest on at most `propext`
  and `Quot.sound`; `applyEntries_model` on the server's 19 axioms and the axiomatized types.
- **What the server's results do not reach**: the chain's triples are inside `apply.applierFor`
  (`applierSpec`, packaged by the constructors), a premise of `isServer` that
  `NewUberApplier`'s spec establishes (`apply.wp_NewUberApplier`; the server's construction,
  `NewServer`, is not translated). So the server's trust base gains only what `apply.Apply` and
  `dispatch` call themselves; the txn package's and mvcc's axioms are in the apply collection's
  (through the constructors), not the server's.
- **Gates**: full `lake build` clean (2903 jobs: the two `Apply_server` files out, `Results` in;
  no `sorry` of ours); `gen-link.py --server` reproduces the regenerated `Link.lean`, every other
  mode unchanged (`--apply --mvcc --txn --leasing --cache --recipes --concurrency --register
  --adt`); `goose.py --check --perennial /shared/perennial-f8f01eb` passes (no translation
  change); `tcb-report.py --check --update`: 69 → 66 axioms, 9 sorries, the diff exactly
  `applierFor`, `applierFor_persistent`, `apply.Apply_server.wp_proof`; collections: server 18 →
  19 (the three gone; `storage.BackendQuota.Cost`, `txn.ApplySecObserve`,
  `txn.WarnOfExpensiveRequest`, `txn.WarnOfFailedRequest` new: `apply.Apply`'s and `dispatch`'s
  callees; its roots now `Link|Results`), the others unchanged (apply 32, txn 18, mvcc 12, cache
  10, concurrency 12, recipes 11, leasing 8, register 1/9, raft 1, adt 0, btree 0);
  `verified-code.py --reuse`: etcd 577 of 3599 functions, 5876 of 45570 lines (unchanged: no
  function changed state); `--package go.etcd.io/etcd/server/v3/etcdserver`: 969 functions, 130
  verified (all sorry-free), 8 assumed, 1436 of 13973 lines; the apply package 71 of 73, 667 of
  684 lines (unchanged); the `etcdserver` package itself 11 verified, 3 assumed
  (`applyConfChange`, `GoAttach`, `stopWithDelay`).
- **The plan, where it moved**: `entriesFrom` did not gain the entry premise (it is pure in `ms`
  and cannot see the KV state the premise depends on): `entriesOk` is a premise of its own, over
  every run; `applyConfChange`'s contract named `applierFor` too (restated); the specs carry
  `srvApplyKV s E x` (the server's `uberApply` field's applier), not `applyKV E ua x` with a free
  `ua`; `applyEntries` states the fold over `unapplied ai ms`, the entries it hands to `apply`;
  the server collection does not reach txn's or mvcc's axioms (above).

### The whole package (2026-10-12)

**Verified**: 71 of the apply package's 73 functions (667 of 684 Go lines), all sorry-free: every
function of `apply.go`, `uber_applier.go`, `backend.go` (but `Compaction`), `quota.go`,
`capped.go`, `corrupt.go`, `auth.go`; not verified: `applierV3backend.Compaction` (translated,
no spec: compaction is out of the model, mvcc's `isStore` fixes `compactMainRev = -1`) and
`init` (`metrics.go`'s gauge registration, not translated). The apply thread's `applyEntryNormal`,
`apply`, `applyEntries` use the proved `apply.Apply`; the applier is no longer a trust boundary.
**Exported results**: the apply package's (`apply/Results.lean`: `chain_put`/`_deleteRange`/
`_range`/`_txn`, the constructors, `wp_Apply`, `wp_NewUberApplier`, `uberApplier.wp_dispatch`,
`apply_kv`, `apply_readonly_no_write`, `apply_rejected_no_write`, `apply_no_v3_no_write`) and the
server's (`etcdserver/Results.lean`: `applyEntries_model`, `applyEntries_kv`,
`applyEntries_replay_no_write`/`_all`, `applyEntries_rejected_no_write`). Together: etcd's apply
loop applies the committed entries' KV requests to the store in order, each by the client model
(or rejected without a write), replays those at or below the consistent index without effect,
and keeps the consistent-index protocol.
**Premises**, in one list: the sole writer (every revision token the apply thread's; the
lessor's revocation deletes through it, same thread); the KV a bare `*store` (`isKV`; not the
`watchableStore` etcd installs); no compaction entry and no empty request (`dispatchOk`); every
normal entry's data decode (`irrDecode`) to a request with an id or a header (`irrId`; pre-3.0
entries panic); `rqOk` per entry at the state it meets (the txn package's premises: `TxnPre`,
room for the revisions, the key count, the sort target and the sort's premise; one checkpoint
per lease checkpoint request; `semverValid` of a cluster version), asked of replayed entries too;
every lease of the KV's state known to the lessor (`leasesKnown`, in the thread's `kvOwn`); the components' contracts (`isAuthStore`, `isApplyLessor`, `isAlarmStore`,
`isCluster`, `isQuota`, `semver`'s axioms, the error trees the auth store's and the lessor's
errors have, `applyErrVars`: the chain's error variables are `errors.New` errors); the backend
runs the hook under its batch lock (mvcc's `batchTxSpec`); `isServer`'s `apply.applierFor` (what
`NewUberApplier` establishes) and `applyConfChange`'s contract.
**Open ends**: the watchable store wrapper (`watchableStore.Write` around `store.Write`);
`Compaction` (out of the model); the `EnsureTrace`/`Get`/`Trace.*` axioms; `rqOk` asked of
replayed entries; the server's construction (`NewServer`: `isServer`'s fields, `NewUberApplier`'s
`applierFor`, the store's hook registration); two files flaky in a full build
(`leasing/InvLeaseCacheWrite.lean`, `concurrency/InvSTMRun.lean`: rebuild once).
**Issues found**: `issues/etcd-apply-alarm-gauge-reactivate.md` (unit 0, the alarm gauge),
`issues/etcd-apply-lease-checkpoint-sections.md` (unit 1: a lease checkpoint entry persists each
checkpoint in its own critical section; fix branch `lease-checkpoint-one-section`),
`issues/etcd-apply-authstatus-metric-label.md` (unit 2: `AuthStatus` recorded under
`op="unknown"`). Unit 3 found nothing new in the Go code.

### Merges of `origin/lean` (2026-10-12)

Three merges of `origin/lean` into `lean` after unit 1 (`6af808b84`, `2228d1eda`, `d133c1c8b`,
each built and gated): the scripts refusing a stale build and `timed-build.py`; the register's
adequacy with Perennial `008979bd0` (baseline 82 axioms, 10 sorries: nine `wp_initialize'`
stubs of Perennial's); the five standard-library axioms proved from Perennial `e6ec34885`
(`bigEndian.Uint64/PutUint64`, `sort.Sort/Reverse`, `errors.Is`; baseline 77 axioms, 10
sorries; the apply collection 35 → 32, server 26 → 23, mvcc 17 → 15, txn 22 → 19). The last
one changed the server's `resultOk` to carry `applyErrIs err` (an error tree for `errors.Is`)
and `errorsInit` to say `ErrNoSpace` is a pointer error; six of unit 1's proofs (`capped`/
`quota` `Put`/`Txn`/`LeaseGrant`) destructured `errorsInit` with the old pattern and were
fixed (`⟨%eN, #HeN, %HeNp⟩`). `apply.Apply`'s proof (unit 2) must produce `applyErrIs` of
every error the chain returns. Builds against a Perennial pin not in `/shared/perennial-merge`
use a worktree of it (`/shared/perennial-e6ec348`) and `.lake/manifest-e6ec348.json`.

A fourth (2026-10-12): `origin/lean`'s "eight small etcd axioms proved" (see "Small etcd axioms":
`traceutil.TODO`, `NewHashStorage`, `UnsafeCreateMetaBucket`, `Notifier.Notify`,
`ServerConfig.ElectionTimeout`, `AlarmStore.Get`, `EtcdServer.Logger`/`isLeader`; `Trace.Step`
requiring a non-nil trace; `MustUnmarshalMessage`'s axiom made true of the code). The `.toml`
files merged as the union of both sides' lists, and `etc/goose.py` regenerates exactly the merged
translation (0 files changed). Conflicts, each resolved keeping both sides' statements:
- `pbutil.MustUnmarshalMessage`'s spec: our two cases (one per message type) with their premise
  `isConfChangeEncoding bs` on the `ConfChange` case (the `InternalRaftRequest` case already had
  its decoding premise `irrDecode bs = some rq`): each case is true of the code (it panics unless
  the bytes decode). `EtcdServer.apply`'s proof uses `hMU.1 … hcc`.
- `store.Write`'s spec takes both `⌜trace ≠ null⌝` (theirs) and the hook (`hookIs γ P f ∗ Pre ∗
  □ {{P ∗ Pre}} f #() {{Q}}`, ours), in that order; its proof, `writeView.Put`/`DeleteRange` and
  txn's `Put`/`DeleteRange`/`Txn` thread the hook and discharge the non-nil trace (`TODO`'s or
  `EnsureTrace`'s fact). Our `store.Rev` (unit 0) now takes `TODO`'s non-nil fact into
  `store.Read`, as `readView.Rev` does.
- A name clash: `notifierLockInv` (and `_fractional`) of `pkg/notify/Defs.lean` and of the cache's
  `InvNotifier.lean` meet in `EtcdServer.apply`'s proof (the server's `InvApplier` imports the
  first; our `MustUnmarshalMessage` spec imports the apply package's `InvRequest`, which reaches
  the cache through txn's `Requests`): notify's renamed `notifyLockInv`.
- The baseline: ours less the eight proved, 77 → 69 axioms, 10 sorries (none of theirs was one
  of ours). Collections: apply 32 → 31 (`TODO`), server 23 → 18, mvcc 15 → 12, txn 19 → 18
  (the last three as `origin/lean` updated them). Every `gen-link.py` mode reproduces its
  `Link.lean`; `goose.py --check` passes; etcd 568 verified of 3599 functions, 5688 of 45570
  lines (was 557, 5635); the apply package unchanged (63 of 73, 486 of 684 lines).

## Standard-library axioms from Perennial (2026-10-12, branch `std-axioms-from-perennial`)

Perennial branch `binary-sort-errors`, landed on its `lean` as `e6ec34885` and pinned here, proves
five functions etcd-grove trusted as its own axioms; their `wp_proof`s are now theorems that
apply Perennial's results.

- `binary.bigEndian.Uint64`/`PutUint64` (`Proof/encoding/binary/`): Perennial now translates
  `BigEndian` and `bigEndian`'s methods and proves `encoding.binary.wp_BigEndian_{Uint64,PutUint64,
  Uint32,PutUint32}` (big-endian is little-endian reversed, as `u64Be`/`beToU64`). `bigEndian` has
  no fields, so loading the global reads no memory and the specs need no `isPkgInit`. Specs
  unchanged.
- `sort.Sort`, `sort.Reverse` (`Proof/sort/`): Perennial translates `Sort`, `Reverse` and the
  `sort.Interface` pdqsort of `zsortinterface.go` and proves `sort.wp_Sort`/`wp_Reverse` over its
  sorter `sort.isSorter` (the `slices` pdqsort proof adapted, its pure lemmas reused; no axiom or
  `sorry`). `sorterSpec` gives `isSorter` for the order `lt a b = true` (`sorterSpec_isSorter`,
  `isSorter_sorterSpec`, in `Spec/sort/Sort.lean`). The statements are unchanged; the two specs are
  now stated with `[sort.Assumptions]` in context (sort's code), which callers have through their
  package's `Assumptions`.
- `errors.Is` (`Proof/errors/Is.lean`): the axiom (`Is` returns some boolean, for any `err`,
  `target`) was **false**: Go's `Is` calls `err`'s `Is`/`Unwrap` methods, which may panic, and
  `err == target` panics for a target of a comparable type holding a non-comparable value
  (`errors.Is(E{[]int{}}, E{[]int{}})` for `type E struct{ x any }`, checked with `go run`).
  Perennial's own `errors.wp_Is` axiom was false for the same reason; it is now a theorem
  (Perennial translates `is`, models `Is` as Go's with `reflectlite.TypeOf(target).Comparable()`
  replaced by `reflectliteComparable`, whose spec is the one new axiom
  `errors.wp_reflectliteComparable`: `true` for a pointer type), for a `nil` or pointer target and
  an error tree whose errors of the target's type hold pointers (`errors.TreeTyped`). The spec here
  is now that (`errorIsTree S M target ∗ ⌜S err⌝`, the two premises). The callers get it from
  strengthened, true-of-Go facts: `resultOk` (the `apply.Apply` axiom's result) carries
  `applyErrIs` for `ar.Err`; `errorsInit` (a package-initialization assumption) says `ErrNoSpace`
  is a pointer error; `clientErrIs` adds `TreeTyped`; `newUniqueKV`/`newUniqueEphemeralKV` pass
  the new premises of `wp_Is`/`wp_Is_leaf`.
- Not done: `errors.As` stays Perennial's axiom `wp_As` (false as stated for a `*T` target with
  `T` neither an interface type nor implementing `error`, documented there): `As` uses reflection
  throughout, so no small faithful model exists.

Gates: `lake build` clean (2691 jobs) at the pin; `etc/goose.py --check` up to date; `etc/tcb-report.py --check`: 65 axioms and 1 sorry (were 70 and 1), the collections mvcc (-2), server (-3) and txn (-3) updated.

## Adequacy of the register's driver: the closed theorem and its trust base (2026-10-12)

`register_adequate` (`Proof/github_com/mit_pdos/etcd_grove/examples/register/Adequacy.lean`,
restated as `register_cluster_safe` in `Results.lean`) is a theorem about the operational
semantics, with no Iris in its statement. Take `registerProgram`, which is
`initialize'(); Main()` for the register package. Start it from any state with no package
initialized (`IsInit σ`) and one live thread (`g.threads = 1`). Then for every real
execution of any length `n` (`RealNsteps n`): if the main thread has finished, its value is
`#()`; every thread is a value or can step; no thread has ended in a panic. Client B's check
of its `Get` is one such panic, so it never fires.

- **Proof.** Perennial's `goose_adequacy_nopanic` is used at the disk FFI, whose
  initial-state conditions are trivial. The register's proofs are generic over the FFI.
  - Bounds: `N = n + 1`. `T = n + 2` comes from `threads_le_steps`: one step forks at most
    one thread. The WP uses neither receipts nor thread tokens, so neither bound costs
    anything.
  - Ghost state: a concrete bundle `registerGF` (`AllG` at slot 0, then invariants, credits,
    heap, prophecies, package state, the disk heap) with its `GooseGpreS` instance.
  - From `ownGoState ∅` to `ownInitializing getIsPkgInit`: `getIsPkgInit` is a lookup table
    over the 29 packages the register reaches, transitively. Its `GetIsPkgInitWf` is proved
    by `repeat' (first | exact True.intro | apply And.intro | rfl)`.
  - Then `register.wp_initialize'` (`Init.lean`), then `register.wp_Main`.
- **Initialization, proved.**
  - raft (`Proof/go_etcd_io/raft/v3/Init.lean`): the initializer establishes
    `isInitialized`, which until now was only assumed (`Base.lean`). That covers the error
    variables (`errors.New`; `IsNewError` from Perennial's new `errors.wp_New_ptr`),
    `globalRand`'s mutex (`init_Mutex`), `emptyState` and the two message tables. Nothing in
    `isInitialized` was false.
  - `quorum`, `tracker`, `confchange` and the register.
  - Perennial's `context` (`Perennial/Proof/context_proof/context_init.lean`, new).
  - Changed instances:
    - Perennial's `io`: `isPkgInit` now gives `Discard ↦□ _`, because raft's initializer
      loads it.
    - etcd-grove's `os`: `isPkgInit` gives `Stderr ↦□ _`, for the same reason.
- **Perennial**: branch `register-adequacy` (`15ef44029`, one commit on `lean`'s
  `e4e126e46`, not pushed; the pin here is that commit): `Proof/io.lean` (the `isPkgInit`
  above), `Proof/context_proof/context_init.lean` (new, with `wp_New_errorString`, `errors.New`
  at its concrete type, which `isTypedErr` needs), and `Proof/math/big.lean`,
  `Proof/crypto/rand.lean` (`wp_initialize'`, `sorry`, marked unprovable). raft's
  `IsNewError` now comes from upstream's `errors.wp_New_ptr` (`IsPointerError`,
  `isNewError_of_ptr`). Merged with `lean` (one `AllG`: `registerGF_allG` is
  `GooseGpreS.goosePreGAllG`, no `[AllG GF]` next to `HeapGS`); full build 2514 jobs, axiom
  account unchanged. **Push order**: Perennial `register-adequacy` first, then etcd-grove.
- **The theorem's hypotheses.** Perennial's Go semantics is a parameter, as in every result:
  - `GoGlobalContext`, `GoLocalContext`, `go.Semantics`;
  - `register.Assumptions`, which includes every imported package's `Assumptions`: each Go
    name stands for its Goose-translated body or for Perennial's trusted model (in
    `TrustedCode`: `sync.Mutex`, `sync/atomic`, the runtime semaphores, `fmt.Sprintf`/`Printf`
    (no formatting), `strings.Join`, `crypto/rand.Int`, `time.Sleep`, ...), plus the struct
    layouts;
  - two new classes of the same kind:
    - `log.NewModel`: the name `log.New` stands for a model returning a fresh pointer.
      Perennial translates `log` without `New`.
    - `context.ErrorStringIsError`: `*errors.errorString` is in `error`'s type set, a
      method-set fact. `methodSet` is uninterpreted, so `context`'s `isInit`, which asks for
      `isTypedErr Canceled`, cannot be established otherwise.

  No instance of `go.Semantics` has been constructed anywhere. The theorem is non-vacuous
  only if these classes are jointly satisfiable, which is believed but not proved.
- **`#print axioms register_cluster_safe`** lists 302 axioms. A Lean classifier
  (`isProp` of each axiom's type) splits them as follows:
  - **Lean's**: `propext`, `Quot.sound`, `Classical.choice`.
  - **297 data axioms, no logical content.** These are Goose's declarations of what it does
    not translate, all in `Code/`: opaque types (`reflect.Value`, `os.file`,
    `sync.Map`, ...), their `underlying` and `zero_val`, constants, and 135 package-variable
    initializers (`X.init : val`). They are 5 in `raftpb`, 53 in `math`, 25 in `os`, 17 each
    in `time` and `math/big`, 7 each in `strconv` and `reflect`, 2 in `log`, 1 each in
    `errors` and `crypto/rand`. Every type is inhabited, so they are consistent: read each
    type as `Unit`.
  - **One propositional axiom**: raft's `reflect.DeepEqual.wp_proof`, Go reflection on two
    `ConfState`s (`ConfState.Equivalent`, reached from `RestartNode`).
  - **`sorryAx`**, from 9 `sorry` declarations, all package initializers that cannot be
    proved because they run opaque initializers:
    - Perennial: `errors.wp_errorType_init` (the `reflectlite` initializer of
      `errorType`), `time.wp_initialize'`, `math.wp_initialize'`, `log.wp_initialize'`,
      `math.big.wp_initialize'`, `crypto.rand.wp_initialize'`;
    - etcd-grove (`Proof/go_etcd_io/raft/v3/Init.lean`): `os.wp_initialize'`,
      `strconv.wp_initialize'`, `raftpb.wp_initialize'` (gogoproto's registration and the
      `fmt.Errorf` error variables that `raftpb.toml` does not translate).

    `reflect.wp_initialize'` is also a `sorry` but is not reached, because `raftpb`'s
    initializer is the only caller.
- **A soundness caveat about trust-boundary axioms.** Axioms like
  `reflect.DeepEqual.wp_proof` quantify over every semantics instance. The `Assumptions`
  classes do not constrain `functions reflect.DeepEqual`, so the axiom asserts the spec for
  every function table, including ones where `DeepEqual` returns a wrong answer. Together
  with adequacy, a constructed model of `go.Semantics` with such a table would refute it.
  The axiom is consistent only as long as no such model is built. The sound form is a
  hypothesis class naming a trusted model, as `log.NewModel` does, with the spec proved from
  it. The same applies to every `*.wp_proof` axiom in `etc/tcb-baseline.txt` and to
  Perennial's spec axioms for names without `FuncUnfold` (`time.wp_Now`, `errors.wp_As`).
- **Is raft's proof complete (outside reconfiguration and read-only requests)?** Judged by
  this list, nearly, but not totally. Nothing about raft's algorithm or its Go code is
  assumed: every raft function `Main` reaches is verified, and raft's package state is now
  proved from its initializer. Two raft-repository items remain:
  - `reflect.DeepEqual.wp_proof` (Go reflection, a standard-library function, with the
    caveat above);
  - `raftpb.wp_initialize'` (generated protobuf registration, outside raft's logic).

  Everything else is the standard library (8 initializers whose variable initializers are
  opaque, `log.New`'s model, the method-set fact, Perennial's trusted models) or Perennial's
  framework: GooseLang's semantics and the Goose translator; `go.Semantics`, not shown
  satisfiable; `AngelicExit`, under which global variables land at `globalAddr` and the
  overflow `assume`s hold; a 64-bit platform. The statement is safety only: no stuck
  thread, no panic, B reads A's write. It says nothing about liveness.
- **Build.** A full `lake build` passes (2202 jobs). One unrelated proof had to be
  repaired: `lcOwn_emap_revokes_acc` (`leasing/InvLeaseCacheWrite.lean`) needed a
  `dsimp only` before its `iframe` (a projection of a literal record).
- **TCB collection.** See the dated line in `etc/tcb-collections/register.txt`.
## Merge: lean into mvcc, the hook (2026-10-12)

Local `lean` (`504afa17e`: the server's `apply` package, units 0 and A, and its change to mvcc's
backend contract, the batch lock runs the server's post-lock hook: decisions.md, "mvcc: the
batch lock runs the hook") merged into `mvcc` (base `124ab0346`; ours since: unit 3a). The
Perennial and etcd pins did not move.
- **Conflicts** (16 files; `InvStore.lean`, `etc/gen-link.py`, `etc/goose.py`, the link lists,
  the baselines, `decisions.md` merged without one), all resolved by keeping both sides:
  `storeTxnWrite.End` (spec and proof): over our `storeTxnWriteCore … chs ps sealed` and with
  their `hookIs γ P f ∗ P`, `P` agreeing with the core's through `hookIs_agree_lc` (their
  proof's step); `metricsTxnWrite.End` (spec and proof): our `isTxnEnd` and their `txnEndPre`;
  `NewStore`'s proof: their `Hhook` framed, our owned views split off (`isplitl [ReadView
  WriteView]`); `writeView.Put`/`DeleteRange`, txn's `Put`/`DeleteRange`/`Txn`/`Range`,
  `readView.Rev`/`FirstRev`/`Range`, `txnReadWrite.End`: our `isTxn_toEnd` then their
  `txnEndPre` (a read's `True`, a write's `txnEndPre_write` from the `csContract`'s update);
  `notes/STATUS.md`'s header.
- **Semantic resolution in `InvStore.lean`** (merged textually): `storeTxnWriteCore` gains their
  `∃ Pw fw`, `"#Hhook" ∷ hookIs γ Pw fw` and `batchTxSpec … Locked Pw fw` (as their
  `storeTxnWriteIs`); `_split`/`_join`/`_seal`/`_wf` carry them. `isTxnWriteCore`/`isTxnEnd`
  carry the hook through the core; `isStore` is theirs (`Ph fh`).
- **Our watchable specs follow the inner ones**: `watchableStore.Write` takes `hookIs γ.st P f ∗
  Pre ∗ □ {P ∗ Pre} f() {Q}` and returns `Q` beside `isWatchTxnWrite` (the hook recorded by the
  inner transaction); `watchableStoreTxnWrite.End` takes `hookIs γ.st P f ∗ P`, handed to both
  inner `End` calls (`txnEndPre_write`). `watchWriter_pins` destructures the two new
  existentials. decisions.md, "The watchable store's concurrency (unit 3)", "The post-lock
  hook".
- **The build needed** (beyond the conflicts): `store.Rev` (theirs, new) and our
  `watchableStore.rev` each one line for the other side's `End` premise (`isTxn_toEnd`;
  `txnEndPre` of a read). 2754 jobs.
- **Link.lean**: every mode regenerated; only the server's changed: the reuse rule imports
  `verify.wp_Verify` from mvcc's `Link` (our `watcher.send` links it) instead of defining it.
- **Checked**: `etc/goose.py --check` passes with no regeneration; `etc/tcb-report.py --check`
  matches the textual union (82 axioms, 1 sorry: ours 70, theirs 82, `verify.Verify` in both);
  every collection matches unchanged (adt 0/0, apply 17/0, btree 0/0, cache 10/0, concurrency
  12/1, leasing 8/0, mvcc 18/0, raft 1/0, recipes 11/0, register 1/0, server 26/0, txn 22/0).
  Verified code: etcd 501 of 3599 functions (5229 of 45570 lines); mvcc 85 of 155 (11
  unfinished: over the interval tree's pending specs), 909 of 2073 lines; adt 4 of 42; txn 39 of 48,
  570 of 653 lines; apply 0 of 73 (1 assumed).

## Merge: lean into mvcc, the request path (2026-10-12)

Local `lean` at `fd5d5306e` (134 commits since the base `504afa17e`: the request path `v3rpc`
units 0–3a, the raft wrapper, the apply package units 1–3, build performance, Perennial
`5857c495a`, `Results` with full names, the build-warning fixes) merged into `mvcc` (ours since the
base: the watchable store, units 1a–4c; the interval tree proved). `lean` moved on to `a95ad2bb4`
(the request path's unit 3b) during the merge: not in this one, merged next.
- **Conflicts** (8 files): the three generated `Link.lean`s regenerated (`--adt`, `--server`,
  `--v3rpc`; every mode reproduces its file, `gen-btree-link.py` too; the raft `Link.lean` takes a
  Rocq checkout and neither side touched it); `storeTxnWrite__Changes.lean` (ours, with their
  conjunct); `etc/link-lean-first-adt.txt` (ours, their `Union` kept pending, `InsertAny`
  dropped); the baselines (the union less what `lean` proved: `NewHashStorage`,
  `UnsafeCreateMetaBucket`, `binary.*`, `traceutil.TODO`); `issues/README.md`, this file (both
  sides' rows and sections).
- **The Perennial bump** (`e4e126e46` → `5857c495a`) broke nothing of ours: no proof of
  ours needed a change for it. Our `time` axioms stay:
  Perennial's `time.wp_Since` (now a theorem) returns *some* duration, ours a positive one (the
  clock assumption `syncWatchersLoop` needs, `issues/etcd-watch-sync-ticker-reset-zero.md`), and
  Perennial models no `Ticker`. The build reused `/shared/perennial-5857c49`'s `.lake/build`
  (copied into `.lake/packages/perennial/.lake/build`): 3224 jobs, no Perennial rebuild.
- **Their mvcc changes on our files**: `storeTxnWriteIs` gained `%Htrnn : trace ≠ null`; our
  `storeTxnWriteCore` carries it too (`_split`/`_join`/`_seal`/`_wf`, `Changes`, `Rev`, the
  watchable `End` rebuild it). `store.Write`/`Read` take `⌜trace ≠ null⌝`: our
  `watchableStore.Write` spec takes it as well (a spec change; no caller yet), `watchableStore.rev`
  gets it from `traceutil.TODO` (now proved, `t ≠ null`).
- **The tree's contract reconciled.** `intervalTree__InsertAny` is gone: our `Insert` (no
  distinctness premise, equal intervals after the equal ones) is it; `checkIntervals` links
  `adt_intervalTree__Insert: @`, and `NewIntervalTree`, `Intersects` are `@` too. `Union.spec`
  is restated in the contract's style: `ownIvt t L 1 ∗ ownIvt t' L' q'`, `⌜L.length + L'.length <
  2^63⌝`, `⌜b = "" ∨ affLt b e⌝` (`Stab`'s/`Visit`'s query premise; `checkIntervals` passes
  `["\x00", +∞)`), post `∃ zs, ⌜zs.Perm (stab (b, e) L')⌝ ∗ ownIvt t (zs.foldl ivtInsert L) 1 ∗
  ownIvt t' L' q'`; still pending (`?`), the tree's unit 4d proves it. `checkIntervals.spec`'s
  post owns the tree at `1`.
- **The count bound in `checkIntervals`** could not come from slice lengths: the tree holds the
  level's deletes and, through `Union`, the nested transactions' at every depth, and a request
  built in memory may share one nested transaction between branches (so its unfolded size is
  exponential in its depth; nor does `maxTxnOps` bound it, per level only). So
  `v3rpc.delCount us` (the deletes at every depth, `Defs.lean`) is bounded by a premise:
  `checkIntervals.spec` takes `⌜delCount us < 2^63⌝` (the recursive calls get it from the
  parent's, `ci_bound_at`), and `txnReqWire` (the request as decoded off the wire: a tree, each
  delete at least a byte of a message) gains `⌜delCount ts < 2^63 ∧ delCount es < 2^63⌝`, which
  `kvServer.Txn` passes on. The proof's lemmas: `ci_nest_fold_bound` (the second loop's tree is at
  most the level's deletes and the nested transactions' so far, by recursion into the nested
  branches), `ci_ivCheck_len`, `ci_ins_bound` (the first loop's `Insert`).
- **Checked**: `lake build` clean (3224 jobs; the only `sorry` warnings are Perennial's,
  `GeneratedProof/`'s and the raft `Init.lean` stubs, as on `lean`); `etc/goose.py --check`
  up to date at the new pin with no regeneration; `etc/tcb-report.py --check`: 99 axioms, 9
  sorries, exactly the union (ours 87/1, theirs 94/9; nothing in neither); every collection
  matches (adt 0/0, apply 32/0, btree 0/0, cache 10/0, concurrency 12/0, leasing 8/0, mvcc 18/0
  (ours 23 less the five `lean` proved), raft 1/0, recipes 11/0, register 1/9, server-raft 6/0,
  server 48/0, txn 18/0, v3rpc 24/0). Verified code: etcd 674 of 3599 functions (7402 of 45570
  lines); mvcc 108 of 155 (2 assumed), 1340 of 2073 lines; adt 24 of 42, 398 of 548 lines; v3rpc
  15 of 116 (`checkIntervals` and `Txn` unfinished: over the pending `Union`).
- **Pitfall**: `git diff lean` after `lean` moves compares against the new tip, not the merged
  one; compare against `MERGE_HEAD`.

## Merge: lean into mvcc, the backend meets the compaction (2026-10-13)

`lean` at `deccecdff` (the backend's units 1–5: etcd's `server/v3/storage/backend` proved over
bbolt's key-value contract, mvcc's backend contract generalized and proved of it in
`BackendBridge.lean`, mvcc's store over the real backend; and the request path's 4a/4b, already
in `mvcc`) merged into `mvcc` at `b0824a24e` (unit 5a, the compaction's specs). 31 conflicts: the
mvcc store's and backend contract's two rewrites, reconciled function by function (the design and
its rejected alternatives: `notes/decisions.md`, "The compaction over the real backend (merge,
2026-10-13)").

- **The merged contract** (`InvStore.lean`): the backend side's `isKeyBackendG` /
  `isBatchTxG` / `batchTxSpecG` / `batchTxInitSpec` / `keyReadSnap` / `keyReadLocked` with
  unit 5a's parameters added: `isKeyBackendG b View RT WT PutOk Del W Wi Dep Cmp P f`. `Del`:
  the snapshots' `snapThin` (now in `keyReadSnap`'s `RLock` postcondition) and the point read's
  "deleted" disjunct; `Dep`: returned by `batchTxInitSpec`'s `Unlock` (no longer by the no-puts
  `Unlock`), taken by the job's `LockOutsideApply`; `Size`/`SizeInUse`; under `⌜Cmp⌝`:
  `UnsafeDelete(Key)`, the limited `UnsafeRange`, `UnsafePut(Meta)`, `ReadTx`'s `metaReadTx`,
  `LockForSafeRangeDelete`/`Unlock…`. mvcc's assumed instances: `isKeyBackend b View Del W P f`
  (∃ `Dep`, no tokens, `Cmp` true), `batchTxSpec bt View Del W Dep Locked P f`, `isBatchTx`.
  `NewStore`'s premise: `storeBackend b s γ P f` (the instance's contract, ∃ `Dep`, `Cmp :=
  storeCmp γ`, i.e. `γ.kb = none`).
- **The merged store**: `StoreNames` has both sides' names (`kb`; `cmeta`, `fin`, `sch`;
  `IdxNames.crev`); `isStore` has the instance's contract, `□ Dep`, the registration
  (`storeRegd`), the configuration, scheduler, `stopc`, hash storage; `muInv`/`revMuInv` hold the
  compaction revision's halves; `writerRes` holds `compactRes`; `storeReaderC`/`storeReader` carry
  the backend's reader token (`storeRT`), `storeReader` also `crevFrozen`; the read transaction
  has the backend side's `txReader` and unit 5a's `muHeld` and `crevFrozen`; the write
  transaction both sides' fields (`storeRegd`, `storeRT`, `delKey`, `Dep`, `compactRes`,
  `crevFrozen`). Every existing mvcc proof of both sides builds (`storeTxnWrite.put` needed
  `maxHeartbeats 400000`).
- **Proved of the real backend** (`BackendBridge.lean`, `isKeyBackendG_of_backend`, `Cmp` false,
  `Dep = True`): exact snapshots (`snapThin_refl`), the point read's key found, the job's
  `LockOutsideApply` (`bt_lockOutJ`), the init `Unlock`'s `□ True`, `Size`/`SizeInUse` (`bk_size`,
  `bk_sizeInUse`, from `backend.Size`/`SizeInUse`), `ForceCommit` (unit 4's). **Not provable**,
  hence under `Cmp`: the deletion from `Key` (the backend's `UnsafeDelete` requires a bucket that
  is not safe-range, its invariant `safeSt` keeps every committed key of `Key`, and a deletion's
  commit changes what readers see, which its `Unlock` allows only with the clients' whole view,
  half of which is under `s.revMu`, which the job does not hold); the `Meta` keys (the hook's
  bucket: reads promise nothing, so not `metaRevVal`; puts need the key absent from the hook's
  leftovers, and cost an operation `bkLocked` does not count); the job's unbounded write-back
  budget; `safeRangeDeleteMu`'s reader slots (not handed out by `isBackend`). None of these is an
  axiom of bbolt's contract: they are the backend model's limits (a backend view up to deletable
  keys, and the `Meta` keys as the store's, would be the extension).
- **Adjusted unit 5a statements**: `store.Compact`, `updateCompactRev`, `compactLockfree`,
  `checkPrevCompactionCompleted` take `storeCmp γ`; `compactJobPre` holds it; `keyReadSnap` drops
  `metaReadSpec` (unused; `metaReadTx` stays); `NewStore`/`newWatchableStore`/`New` take the
  backend side's instance premises (`kb`, `kbView`, `kbRegRight`, two `kbWT`, the `kbRT`s) as
  `storeBackend`, and keep `0 ≤ CompactionBatchLimit`; `rangeEvents`/`store.restore` quantify over
  `Dep`, `Cmp`; `mvcc_NewStore_backend` takes the batch-limit premise and returns unit 5a's
  postcondition (`storeReaderC`, `storeStop`, `compactRight γ (-1)`; the client freezes it).
- **Other packages**: no statement of txn/apply/v3rpc/server/read/backend changed.
- **Gates**: `lake build` (the only `sorry` warnings are unit 5a's 21 pending proofs);
  `goose.py --check`; every `gen-link.py` mode reproduces (raft's needs the Rocq tree: untouched);
  the trust base 172 axioms, 31 sorries: exactly the union of `lean`'s 166/9 and `mvcc`'s 118/31
  (nothing turned from axiom into theorem: the bridge's new clauses use the backend's linked
  results); collections: mvcc 34/22 (the union: 5a's 30 + the 4 bbolt predicates), mvcc-compaction
  18 -> 22 axioms (the 4 bbolt predicates, which `isStore`'s `StoreNames.kb` names), every other
  unchanged (backend 59/0, server 70/0, apply 36/0, txn 22/0, v3rpc 50/0, read 12/0); verified
  code: `server/v3/storage` 188 of 490 functions verified, 18 unfinished (mvcc 108 of 155, 18
  unfinished, 6 assumed; backend 70 of 112; schema 10 of 110), etcd 794 of 3599, 21 unfinished.

## Merge: lean into mvcc, the request path's unit 4b (2026-10-13)

`lean` at `4f2c96322` (the request path's unit 4b: the apply loop `applyAll` and the applied index,
`pkg/wait`'s `wait_time.go`, `pkg/notify`'s `NewNotifier`/`Receive`, the read loop's contracts
discharged; five commits past `17575d236`) merged into `mvcc` at `1ce3878bb`. One conflict, this
file's "Last updated" line. The server's `BaseApply.lean` and `Link.lean` merged automatically
(4b's additions beside 5a's move of go-humanize's `isPkgInit` instance to mvcc's `Base.lean` and the
zap/go-humanize theorems now defined by mvcc's `Link.lean`); every `gen-link.py` mode reproduces
the merged `Link.lean`s. `etc/tcb-baseline.txt` merged automatically (4b's five axioms beside 5a's).
Gates: `lake build`, `goose.py --check`, the trust base 118 axioms and 31 sorries (the union), every
collection unchanged (server 66/0, mvcc 30/22, mvcc-compaction 18/22).

## Merge: lean into mvcc, the request path's unit 4a (2026-10-13)

`lean` at `17575d236` (the request path's unit 4a: the linearizable read loop,
`server/v3/etcdserver/read`, two commits past `164492796`) merged into `mvcc` at `3f2263f69`
(the compaction's unit 5a). Conflicts: `etc/tcb-baseline.txt` (both sides' additions kept: 5a's six
axioms and 22 sorries, 4a's three axioms `context.WithTimeoutBackground`, `strconv.FormatUint`,
`traceutil.Trace.LogAllStepsIfLong`), this file's "Last updated" line and `decisions.md` (both new
sections kept). No proof or spec changed on either side: 4a touches nothing under `storage/mvcc`,
`pkg/adt` or `pkg/schedule`; its `BaseApply.lean`/`InvApply.lean` edits merged cleanly with 5a's move
of go-humanize's `isPkgInit` instance to mvcc's `Base.lean`. Gates: `lake build` 3900 jobs (the only
`sorry` warnings the 21 pending compaction and scheduler proofs), `goose.py --check` ok, the trust base
113 axioms and 31 sorries (the union), every collection unchanged (mvcc 30/22, mvcc-compaction 18/22,
read 12/0), every `gen-link.py` mode reproduces.

## Merge: lean into mvcc, the request path's unit 3b (2026-10-12)

Local `lean` at `a95ad2bb4` (5 commits since the base `fd5d5306e`: the request path's unit 3b,
the read side and `Txn`: `EtcdServer.Range`/`Txn`, `txn.Txn` at a reader (`specRead`), the
response headers owned, `mvcc.errorfIs` for the read side's context error) merged into `mvcc`
(ours since the base: the interval tree's unit 4d, `Union` and the visitor's position).
- **Conflicts**: this file only (the "Last updated" line: both lists kept). The generated
  `Link.lean`s merged cleanly; every `etc/gen-link.py` mode but the raft one (`--adt`, `--apply`,
  `--cache`, `--concurrency`, `--leasing`, `--mvcc`, `--recipes`, `--register`, `--server`,
  `--txn`, `--v3rpc`) and `etc/gen-btree-link.py` reproduce their files.
- **Their proofs over our changes** (two, neither a change of ours):
  - `txn/Txn.lean`, their new read-transaction proof (`specRead`, the failed-check branch):
    `metricsTxnWrite.End.spec` takes `isTxnEnd` since our watchable store's unit 3a, so the
    branch converts with `mvcc.isTxn_toEnd`, as the other `End` calls in the file already do.
  - `v3rpc/Results.lean`: `txn_end_to_end` was stated over the tree's pending contract (four
    hypotheses `h_adt_NewIntervalTree`, `h_adt_intervalTree__InsertAny`, `…Intersects`,
    `…Union`, one of them, `InsertAny`, gone since the previous merge). With unit 4d the link's
    `kvServer.wp_Txn` is unconditional: the hypotheses are dropped (a stronger statement; the
    module docstring's "over the interval tree's pending contract" with them).
- **Checked**: `lake build` clean (3277 jobs; the only `sorry` warnings are Perennial's,
  `GeneratedProof/`'s and the raft `Init.lean` stubs); `etc/goose.py --check` up to date (no
  regeneration); `etc/tcb-report.py --check`: 99 axioms, 9 sorries, unchanged; every collection
  matches with no update (adt 0/0, apply 32/0, btree 0/0, cache 10/0, concurrency 12/0, leasing
  8/0, mvcc 18/0, raft 1/0, recipes 11/0, register 1/9, server-raft 6/0, server 61/0, txn 18/0,
  v3rpc 46/0). Verified code: etcd 691 of 3599 functions (7682 of 45570 lines; 34 assumed);
  mvcc 108 of 155 (2 assumed), 1340 of 2073 lines; adt 25 of 42, 405 of 548 lines; v3rpc 17 of
  116, 248 of 1722 lines (`checkIntervals` and `Txn` now verified, none unfinished).

## Merge: lean into mvcc (2026-10-12)

`origin/lean` (`436f363c4`: the server's `txn` package, units 0–4, and its changes to mvcc's
files: the read-only write transaction `NewReadOnlyTxnWrite`/`txnReadWrite.*` (`InvRoTxn.lean`),
`metricsTxnWrite.Rev`/`FirstRev`/`Range` of either transaction kind and `Changes`, `idxLogAuth`,
reads pinned by the caller's tokens, `NewStore` returning the initial log's certificate)
merged into `mvcc` (base `e3effe933`). The Perennial and etcd pins did not move.
- **Conflicts**, all resolved by keeping both sides: `etc/gen-link.py` (our `--adt` mode and
  theirs `--txn`, with its `NAMESPACED` entry), `etc/goose.py` (`pkg/v3/adt` and
  `etcdserver/txn` both translated with bodies), `etc/link-lean-first-mvcc.txt` (our adt,
  watcher-group, batch and stream lines and their read-only transaction lines; the lines both
  changed merged without conflict: our key index's `zap_*` callees, their
  `metricsTxnWrite__*` callees), `etc/tcb-baseline.txt` (the union: `trace.SpanFromContext`
  and their `traceutil`/`sort`/`txn` axioms), `notes/STATUS.md` (both sides' sections).
  `zap.Logger.Panic` (added by both): ours kept (`⌜r = PanicV #msg⌝`); no `txn` proof
  destructures its postcondition (`sortRangeResults`' panic branch is unreachable), so nothing
  needed adapting. `newTreeIndex` (spec and proof): our `⌜lg ≠ null⌝` premise and `%Hlgnn` in
  `isTreeIndex` with their `idxLogAuth γ ½ []` in the postcondition; `NewStore`: the
  call to `newTreeIndex` discharges our premise and destructures their `idxLogAuth` (`Hil`).
- **Link.lean** regenerated for mvcc (their eleven functions added); `--txn` and `--adt`
  regenerate unchanged.
- **The build** (2683 jobs) needed no further change: no semantic conflict between our
  `isTreeIndex`, total key-index specs and watch files and their `InvStore`/`InvIndex` changes.
- **Checked**: `etc/goose.py --check` passes at the unchanged pins with no regeneration;
  `etc/tcb-report.py --check` matches the textual union (70 axioms, 1 sorry; ours 58, theirs
  69); every collection matches but `txn`, which now reaches our `zap.Int64`/`zap.String`
  (through the key index's total specs under `treeIndex.Put`/`Tombstone`): updated, 20 to 22
  axioms. Verified code: etcd 494 of 3599 functions (5149 of 45570 lines); mvcc 78 of 155 (7
  conditional on the tree's contract), 829 of 2073 lines; adt 4 of 42; txn 39 of 48, 570 of
  653 lines.

## The store's compaction (2026-10-13, branch `mvcc`)

The plan: unit 5a (this one) translates the compaction and fixes its model, the contracts and
the specs; 5b proves the index's side (`keyIndex.compact`/`keep`/`doCompact`,
`treeIndex.Compact`/`Keep`) and the meta keys; 5c the store's side (`Compact`,
`updateCompactRev`, `compact`, `compactBarrier`, the job `scheduleCompaction`,
`checkPrevCompactionCompleted`, `compactLockfree`). The design, with its rejected alternatives:
`notes/decisions.md`, "mvcc: compaction — the compaction revision under revMu, the index
compacted per key, the bucket minus a kept set".

**Unit 5a (2026-10-13): done.**

- **Translation.** `mvcc.toml`: `treeIndex.Compact`/`Keep`, `keyIndex.compact`/`keep`/
  `doCompact`, `store.Compact`/`compactLockfree`/`compact`/`updateCompactRev`/
  `checkPrevCompactionCompleted`/`compactBarrier`/`scheduleCompaction`, the meta keys'
  `Unsafe{Read,Set}{Scheduled,Finished}Compact`/`Set{Scheduled,Finished}Compact`;
  `go-humanize` imported (its `isPkgInit` instance moved from the server's `BaseApply.lean` to
  mvcc's `Base.lean`). `schedule.toml`: `NewJob`, `job.Name`, `job.Do` with bodies, `context`
  imported (the FIFO scheduler stays names-only). `etc/goose.py --check` passes.
- **The model** (`Compact.lean`, pure, no `sorry`): `kiCompact` (the key index compacted at a
  revision, `key_index.go`'s `compact` with `doCompact`), `kiAvail`/`kiKeep` (the kept set,
  `keep`'s), `kiCompactO` (absent if emptied), `IdxCRep` (each key at its own level),
  `crevN`, `KeyDel` (what the job may delete), `NoDelPutAt`, `keepAt`; theorems
  `kiGet_kiCompact`, `kiGet_of_kiCompact_empty`, `kiCompact_kiCompact`/`_le`, `kiCompact_neg`,
  `kiCompact_lastEmpty`, `kiCompact_empty_lastEmpty`, `kiCompactO_step`, `IdxCRep.step`/`kiAt`/
  `rangeAt`/`get_some`/`get_none`/`mono`/`of_indexOf`, `kiGet_avail`, `named_not_del`,
  `kiAvail_prefix`, `KeyDel_prefix`, `kiAvail_kiCompact` (printed by `Results.lean`).
- **Invariants and contracts.** The index (`InvIndex.lean`): the compaction revision's counter
  (`IdxNames.crev`, `crevUB`/`crevLb`), `idxLockInv` at `IdxCRep cmax`; `Get`/`Range`/
  `Revisions`/`CountRevisions` take a part `crevUB γ q c` with `c ≤ atRev` (given back),
  `KeyIndex`/`Insert` at `-1`, `newTreeIndex` returns the whole. The store (`InvStore.lean`):
  `muInv` (`s.mu`'s resource, was `True`) and `revMuInv` each half of `compactMainRev` and a
  quarter of the counter; the compaction right `compactRight γ c`; `crevFrozen` (the right
  given up at `-1`); the backend contract with the deletable keys (`Del`), the
  deposit witness (`Dep`), the batch transaction's `UnsafeDelete`/limited `UnsafeRange`/meta
  `UnsafePut`, thinned snapshots (`snapThin`), the meta reads (`metaReadSpec`, `metaReadTx`),
  `LockOutsideApply`, `LockForSafeRangeDelete`, `Size`/`SizeInUse` (since the merge with the
  backend's units 1–5: inside the backend side's `isKeyBackendG`, the compaction-only calls under
  its condition `Cmp`, `storeCmp γ` for the store; see "Merge: lean into mvcc, the backend meets
  the compaction"); the meta record
  (`compactRes`, `compactedAt`); `isStore` with the configuration (`0 < CompactionBatchLimit`),
  the scheduler, `stopc`, the hash storage. `InvCompact.lean`: the job's predicates
  (`compactJobPre`, `compactDone`, `compactChan`, `keepSetIs`, `storeStopped`, `barrierCtx`).
  `pkg/schedule`'s `Defs.lean`: `isScheduler`, `schedRunning`, `jobIs`.
- **Specs**: the 18 compaction functions and the 3 `pkg/schedule` functions specified, their
  proofs pending (`sorry`), all linked (`etc/link-lean-first-mvcc.txt`); the store's readers
  (`storeReader`) carry `crevFrozen` (the existing statements are of a store never compacted);
  `rangeKeys` general (`rangeOutcomeC`); `NewStore` takes `0 ≤ cfg.CompactionBatchLimit` and
  returns the compaction right with `storeReaderC`; `New`/`newWatchableStore` freeze it. No
  statement of txn/apply/v3rpc/server changed.
- **New axioms** (6, trust boundary): `schedule.Scheduler.Schedule` (the shape agreed with the
  server's session), `mvcc.newKVHasher`, `mvcc.kvHasher.WriteKeyValue`, `mvcc.kvHasher.Hash`,
  `mvcc.hashStorage.Store` (crc32 unmodelled), `zap.Uint32`. **New sorries** (22): the 18
  mvcc pending proofs (`keyIndex.compact`/`keep`/`doCompact`, `treeIndex.Compact`/`Keep`,
  `store.Compact`/`compact`/`compactLockfree`/`compactBarrier`/`updateCompactRev`/
  `scheduleCompaction`/`checkPrevCompactionCompleted`, `{Unsafe,}Set{Scheduled,Finished}Compact`,
  `UnsafeRead{Scheduled,Finished}Compact`), `schedule.NewJob`/`job.Do`/`job.Name`, and
  `kvHasher.kvHasher_typed_pointsto` (the generated instance of the axiomatized type `kvHasher`,
  reached by `scheduleCompaction`'s spec).
- **Gates**: `lake build` passes (the only `sorry` warnings are the pending proofs);
  `goose.py --check` passes; the trust base 110 axioms, 31 sorries (was 104, 9); collections:
  mvcc 30/22 (was 18/0: the compaction's axioms and sorries, and the zap/humanize/context axioms
  its functions reach), new `mvcc-compaction` 18/22 (tracks units 5b/5c); every other
  collection unchanged; verified code: mvcc 108 of 155 functions verified, 18 unfinished, 6
  assumed (1340 of 2073 lines), etcd 691 of 3599 functions, 21 unfinished.
- **Findings** (`issues/`): `etcd-compaction-negative-batch-limit` (a negative
  `CompactionBatchLimit` makes the job loop forever; `NewStore`'s premise) and
  `etcd-compaction-delete-then-put` (compacting at a revision that deletes then puts a key
  deletes its live value: a later read `Fatal`s; `named_not_del`'s premise `NoDelPutAt`), both
  reproduced by Go tests (kept out of git, in `.lake/go-src/etcd`).
- **Traps for 5b/5c**: `generation.walk`'s spec has a pure closure (`doCompact`'s closure writes
  `available`: 5b needs an effectful `walk` spec); `kvHasher` is axiomatized (the job's proof
  rests on its generated instances' `sorry`); readers of a compacted store are not specified
  (`storeReaderC` exists; compaction-aware `Read`/`Write`/`Range` are the server's next need,
  with `NoDelPutAt`); `compactDone`'s "some context closed" disjunct is weak (the cancelled
  job's barrier); the bucket's logical view never shrinks (deletions are `Del`-invisible: the
  job does not take `revMu`); `LockOutsideApply` gives `W` only with the deposit witness `Dep`;
  `compactMainRev` is split between `s.mu` (`rangeKeys`) and `revMu` (`syncWatchers`);
  since the merge with the backend, the compaction is specified over mvcc's assumed backend only
  (`storeCmp γ`, `γ.kb = none`, a premise of `Compact`/`updateCompactRev`/`compactLockfree`/
  `checkPrevCompactionCompleted` and part of `compactJobPre`): the real backend does not support
  deleting from `Key` (see the merge section), so 5b/5c prove the compaction against the assumed
  contract, whose guarded clauses (`⌜Cmp⌝ -∗ …`) they open with it; the store's readers and
  writers now also carry the backend's tokens (`storeRT`, `storeWT`, `txReader`).

## The watchable store (2026-10-11, branch `mvcc`)

The next target after the KV core: etcd's watchers (`watchable_store.go`, the sync loops and
`notify`; `watchable_store_txn.go`, the write transaction's `End` notifies; `watcher.go`, the
client's stream; `watcher_group.go`, the synced and unsynced groups: key watchers in a map,
range watchers in the interval tree of `pkg/v3/adt`, a red-black tree with a `max`
augmentation). The result to reach: the watch guarantee — a watcher on `[key, end)` from
`startRev` receives every change of a key in its range at a revision at or above `startRev`,
once, in revision order, until cancelled, the events being the store's log of changes
(`Log`); compaction and `Restore` out of scope, as for the store. The plan (decisions.md,
"The watchable store: the plan, the interval tree's contract"): contract first, the tree's
proof last — unit 1a the translation (done), 1b the interval tree's contract (its model
specs, pending: `?` in the link list, hypotheses of what reaches them, as the recipes did),
unit 2 `watcher_group.go` and `watcher.go` over the contract, unit 3 the store's concurrency
and the guarantee, unit 4 the tree's proof (red-black insert/delete fixups), discharging the
hypotheses.
- **Unit 1a, the translation** (2026-10-11): `pkg/v3/adt` with bodies
  (`Code/go_etcd_io/etcd/pkg/v3/adt.toml`: everything but `MaxHeight` (floating point),
  the two `String`s (`fmt`) and `visitLevel` (debugging); 38 of its 42 functions, 495 of 548
  lines) and the four watchable-store files in the mvcc toml (all 46 of their functions;
  the promoted wrappers of `watchableStore` over `*store` and of `watchableStoreTxnWrite`
  over `TxnWrite`, which `End` needs for `Changes`/`Rev`); `go.opentelemetry.io/otel/trace`
  names-only (new; `watcher.go`'s `trace.SpanFromContext`), `client/v3` and `verify` already
  were; `Base.lean` gets the package-init instances of `adt` and `otel/trace`. Goose took
  the type assertions `.(watcherSet)`, the maps keyed by `*watcher`, five `select`s (two with
  `default`, one on a nil-able `time.After` channel, one on a ticker), `time.NewTicker`/
  `Ticker.Reset`/`time.Since`, the builtin `max`, `float64(n)` for the gauges, `verify.Verify`
  with a closure, the variadic `fcs ...FilterFunc`, and `Stab`'s closure over its named
  result (heap-allocated). `etc/goose.py --check` passes; the build, the baselines (57 axioms,
  1 sorry; mvcc 16, 0) and the verified-code figures are unchanged, with the package now
  1348 of 2073 lines translated (65%). A remark for unit 2: `watcherSetByKey`'s second
  `switch` case (`len(wranges) == 0 && len(wkeys) == 0`) is unreachable after the first
  (harmless dead code).
- **Unit 1b, the interval tree's contract** (2026-10-11): `Proof/go_etcd_io/etcd/pkg/v3/adt/`
  (`Base`: the package's init instance, moved out of mvcc's; `Model`: `IvlS`, `affCmp`
  (`StringAffineComparable.Compare`), `ivlCmp` (`Interval.Compare`: left, right, or overlap),
  `ivlLt` (the tree's order: begin, then end), `ivtInsert`, `stab`, the orders' lemmas and
  `ivtInsert_sorted`/`mem_ivtInsert`; `Defs`: `affIvl b e` (the Go `Interval` of two
  `StringAffineComparable` interface values) and the `opaque ownIvt t L`, its body naming the
  heap, semantics and package instances so that unit 4's definition changes no statement).
  **Pending** (`?` in `etc/link-lean-first-adt.txt`; hypotheses of what reaches them):
  `NewIntervalTree` (`ownIvt t []`), `intervalTree.Insert` (a new interval: `ivtInsert`),
  `Delete` (`eraseP`, returns membership), `Find` (the entry's pair, a read-only pointer for
  good, or `nil`), `Intersects` (`stab ≠ []`), `Stab` (the overlapping entries' pairs as a
  slice of pointers, read-only for good, in the tree's order), `Len`. **Proved**:
  `StringAffineComparable.Compare` (`affCmp`), `NewStringAffineInterval`,
  `NewStringAffinePoint` (`s ++ "\x00"`), `Interval.Compare` (`ivlCmp`; the type assertion
  and the dynamic `Compare` calls step under `wp_auto`, the interface call reducing to the
  value-receiver method; the struct is split into its fields for the loads, `ivl_split`/
  `ivl_combine`). `Link.lean` by `etc/gen-link.py --adt`, `Results.lean`, collection
  `etc/tcb-collections/adt.txt` (0 axioms); the baselines unchanged; verified-code: adt 4 of
  42 functions. Unit 2's design is in decisions.md, "The watcher group and the stream".
- **Unit 2, first half** (2026-10-12; design: decisions.md, "The watcher group and the stream
  (unit 2)"). **The group's sets and structure** (`InvWatchGroup.lean`): `WatchRange` (a key, or
  `[key, end)` affine) with `covers`, `watcherFixed w r fcs` (the never-written fields,
  persistent), `WatcherSt`/`watcherOwn` (the mutable fields, for the store), `ownWatcherSet`
  (a `map[*watcher]struct{}` as a `GMap Loc Unit`; `ownWatcherSetOpt` for a possibly nil map,
  which Perennial gives no ownership: lookups, `len` and `range` on it are pure),
  `ownKeyMap`, `ownWatcherGroup wg W` (the all-watchers set, the key map, the tree through
  `ownIvt` with `RangesOk`: sorted by `ivlLt`, one interval per distinct range), the lemmas
  `ownWatcherGroup_fixed`/`_member`/`_not_null`/`_intro`, `ivlCmp_point_iff` (the stab of the
  point `[k, k\x00)` is the overlap `b ≤ k < e`: `strLt_succ_le`). Proved: `watcherSet.add`/
  `delete`/`union` (disjoint, the argument possibly nil), `watcherSetByKey.add`/`delete`,
  `newWatcherGroup` (a value; a wand from the location), `watcherGroup.add` (a non-member),
  `contains` (a decidable existence over `W`), `size` (with the bound), `delete` (returns
  membership; two `watcherFixed` of a pointer agree, `watcherFixed_agree`),
  `watcherSetByKey` (the covering members, lent by a wand, by alias when the code can; its
  unreachable second `switch` case falls through). The five that reach the tree's pending
  contract are linked with its specs as hypotheses (`?` lines in the mvcc link list;
  `adt_NewStringAffine*: @`). Map notes: `make`/`delete` on a named map type need
  `go.make1_underlying`/`go.delete_underlying` first; a pointer-receiver call on a named map
  needs `wp_method_call; wp_call` then a load; `Convert watcherSet.ty go.any` is
  `interface.mkOk watcherSet.ty #m` and the assertion back steps under `wp_auto`.
  **The stream** (`InvWatchStream.lean`): the `watchable` contract `isWatchable wa P` over the
  store's choice `P : WatchParams` (`IW w` a watcher of the store, `WC w` cancelled, `C ch`
  what it needs of the channel, `F f` of a filter, all persistent; `CR ch L` the right to
  close `ch` with the watchers `L` registered on it, owned): `watch` registers (returning
  `IW`, the cancel closure's spec `cancelSpec` yielding `WC`, `CR` grown), `progress`/
  `progressAll` take `IW` only, `rev`; `isWatchStream ws wa P γ` (the fields, `C ch`, the
  store's close triple for `ch` once every registered watcher is cancelled, the `sync.Mutex`
  guarding `watchStreamInv`: the id maps with their watchers' `IW` and closures' specs, `CR`
  or, once closed, the token `watchStreamOpen γ`). Proved: `Watch` (the empty-range and
  closed cases both `ErrEmptyWatcherRange`, duplicate id, else `nil` with the id), `Chan`,
  `Cancel` (`nil` or `ErrWatcherNotExist`), `Close` (consumes `watchStreamOpen γ`: the
  double close excluded), `Rev`, `RequestProgress`, `RequestProgressAll`. `clientv3.AutoWatchID`
  /`InvalidWatchID` translated as values (`client/v3.toml`); `trace.SpanFromContext` an
  axiom (`trace.isSpan`: `End` returns), with `otel/trace/embedded`, `otel/codes`,
  `otel/attribute` types-only so that `trace.Span` is an interface, not an axiomatized type
  (`Watch` stores the span); the package facts `ErrWatcherNotExist`/`ErrEmptyWatcherRange`/
  `ErrWatcherDuplicateID`/`watchStreamGauge`. A translator remark: Goose emits the deferred
  variadic `span.End()` with no arguments as a call on `()` (elsewhere a deferred call passes
  its argument): to check in Perennial. Proof notes: `wp_apply` of a closure's spec inside the
  stored closure's proof failed with "unknown free variable" (again: `wp_bind` + `iapply`); a
  local named `end` needs `irename`. Baselines: 58 axioms, 1 sorry; mvcc 17. Verified-code:
  mvcc 71 of 155 functions (5 conditional), `watcher.go` all 7, `watcher_group.go` 6 + 5
  conditional of 16; 771 of 2073 lines.
- **Unit 2, second half** (2026-10-12): `InvWatchBatch.lean`: `EvM` (an `mvccpb.Event`: put or
  delete, the key-value, the previous one), `kvPtrFixed`/`evIs` (persistent: events are shared),
  `EventBatch`/`ebAdd` (`eventBatch.add` exactly, over `getLast?`; the cap
  `watchBatchMaxRevsV = 1000`, a package fact `globalAddr watchBatchMaxRevs ↦□`), `batchOf W ST
  evs` (per member, the fold of the covering events at or above its `minRev`; `batchOf_snoc`:
  any nodup listing of the covering members gives the same step, so the map's iteration order
  does not matter), `minRevOf`, `takeMembers` (`choose`'s prefix of the iteration),
  `ownEventBatch`, `ownWatcherBatch` (a map of pointer-and-model pairs), `ownStates ST`, the
  borrow `ownWatcherGroup_watchers` (the all-watchers set out of the group and back, for the
  loops over `wg.watchers`). Proved: `eventBatch.add`, `watcherBatch.add` (a fresh batch when
  absent), `newWatcherBatch` (`nil` for an empty group, else `batchOf`), `chooseAll` (the
  minimum `minRev`; premises: every member's state given, none below `compactRev`, none above
  `curRev`, none restoring — the store's invariant, unit 3 — excluding the compaction response
  and the panic), `choose` (the group itself below `maxWatchers`, else a fresh group of a
  nondeterministic subset of `max 0 maxWatchers` members). Notes: `BigSepM.bigSepM_lookup_acc`/
  `_insert_acc` for the states; a struct allocated by `wp_auto` is persisted by `ipersist`
  after `typedPointsto_not_null`; `&eventBatch{}` arrives as `zero_val`, rewritten to the
  literal by `rfl`; `math.MaxInt64` reduces under `wp_auto`; a map `range` with `break` under
  `wp_wand_r`. Baselines unchanged (58 axioms, 1 sorry; mvcc 17); verified-code: mvcc 74 of 155
  functions (7 conditional on the tree's contract), 823 of 2073 lines; `watcher_group.go` 9 + 7
  conditional of 16, `watcher.go` all 7. Unit 2 is complete; unit 3 follows.
- **Unit 3a, the write path** (2026-10-12; design: decisions.md, "The watchable store's
  concurrency (unit 3)" and its "Refinements for 3a"; the proof's own refinements below).
  **Contract changes first.** (1) The history carries the change: `Ev := {rev, change}` with
  `Ev.key`/`Ev.tomb` abbrevs (`Model.lean`; `Ev.enc` through `Change.enc`; `histOf_inj`,
  `histOf_prefix_log`, `histOf_cmp_log`: a history lower bound determines the log). (2)
  `storeTxnWriteIs` split: `storeTxnWriteCore tw s γ ilog pend chs ps sealed` (no key-values:
  the slice's length only) and `isTxnWriteCore`, with `_split`/`_join`; `storeTxnWrite.End`/
  `Rev` over the core; `storeTxnWrite.Changes` and `metricsTxnWrite.Changes` return the slice,
  `changesAre` and the core (the key-values are the caller's); `metricsTxnWrite.End` takes
  `isTxnEnd` (`isTxn_toEnd`); `NewStore` returns `ReadView`/`WriteView` owned; the kv-view,
  `readView` and txn callers adapted (`isTxnWrite_join` in txn's `wp_txnWrite_Changes`). (3)
  The tree contract at a fraction: `ownIvt t L q` (reads at any `q`, `Insert`/`Delete`/
  `NewIntervalTree` at `1`) with the pending `adt.ownIvt_split.spec` (split, combine *and
  agreement*; `?` in the adt list); `ownWatcherGroup`/`ownWatcherSet`/`ownKeyMap`/`rangeSet`/
  `watcherOwn`/`ownEventBatch`/`ownWatcherBatch` take `(q : Qp := 1)` (unit 2's proofs
  unchanged); `InvWatchFrac.lean`: `ownWatcherGroup_fractional`, `watchStoreInv_fractional`
  from that hypothesis. (4) `WatchParams.R` (owned; the store's `watchReader`: a
  `storeReader`) through `isWatchable`'s `rev`/`progress`/`progressAll` and `watch`, and the
  stream's `Watch`/`Rev`/`RequestProgress`/`RequestProgressAll`; `0 ≤ startRev`. The package
  facts `watcherGauge`/`slowWatcherGauge`/`pendingEventsGauge`.
  **The proof's refinements** (sound reasons found while proving): (a) **the pending revision
  is sealed before `notify`**: a lower bound of `histShape ilog pend` does not fix `pend`
  (`histShape ilog [c]` is a prefix of `histShape ilog [c, c']`), so a response could have
  stated part of a revision; `idxWriter_seal` appends the commit marker early
  (`idxWriterSealed`, `idxWriterB … sealed`, `idxWriterSealed_commit`/`idxWriterB_commit`), and
  `End` seals, notifies, then commits: every response carries the lower bound of the log that
  commits it (`evsWf`). (b) **A sole-writer token**: `notify` must know the notified log is
  the writer's `ilog`, which the inner store's own `Write` could break; `watchableStore.Write`
  takes `watchWriter γ L` (the certificate of `L`, the unspent revision tokens `wBudget L`,
  half of `γ.wlog`) and `End` returns it at `commitLog ilog pend`. (c) **A synced watcher's
  `minRev` is not advanced when it gets no events**, so "synced ⇒ above the committed
  revision" is false; the lock tracks a delivery bound per watcher (`WsOk.synced_d`,
  `syncedBelow`/`syncedAbove`). (d) **Filters are recorded per delivery**: a partial-correctness
  triple does not fix the predicate a filter implements (two witnesses may differ), so each
  delivery (`Deliv`) records the predicate its sender used (`filtersImpl`); `RespM` carries the
  watcher sent for as ghost data (watch ids are reused after a cancel). (e) `C ch := True`
  and the close right `CR` carries the channel's invariant; `WatcherNames` has `lo` (the first
  revision watched) and the channel's names; victims out with the mover are a population of
  their own (`Wo`, half their state) so `cancelWatcher`'s retry is real; the lock invariant
  holds `ghostVar γ.wst q σ` so that its fractions agree; `newWatchableStore` points the read
  view's `kv` at the watchable store (`rev()` steps through `readView.Rev`).
  **Definitions** (`InvWatchStore.lean`): `evOfKv`/`evsOfRevM`/`logEvents`/`watchEvents`/
  `filtered` with prefix and append lemmas; `RespM`, `respIs`/`respsIs`, `respOk` (the revision
  at or above the events', the id of a response with events); `WatchChanNames`,
  `WatcherNames`, `WsNames` (`st`, `wmeta`, `wlog`, `wst`); `WsState`/`WsOk` (the populations
  disjoint, a victim in one batch, the flags, the delivery bounds); `filterSpec`/
  `filtersImpl`; `watcherMeta` (a persistent ghost-map element), `cancelled` (`dghostVar
  … .discard false`), `evsWf`, `chanWatcher`, `watchChanInv` (`inv watchN`: the channel, the
  responses sent with `respOk`, the consumer's prefix `watchConsumer`, the registered list
  (half the close right's), per watcher its deliveries and its live half or `cancelled`),
  `popFacts`/`memberRes`/`outRes`/`watchStoreBody`/`watchStoreInv`, `watchReader`,
  `isStopChan` (3b), `isWatchableStore s st γ`, `storeWatchParams`, `watchWriter`/`wBudget`,
  `isWatchTxnWrite`; `WatchClose.lean`: the stream's close triple `wp_watch_close`. **Proved**:
  `watchableStore.Write`, `watchableStoreTxnWrite.End`, `notify`, `addVictim`, `watcher.send`
  (the filtering loop, `verify.Verify`'s assertion, the non-blocking send opening the channel
  invariant with a later credit — it holds filter triples, so it is not timeless), `watch`,
  `cancelWatcher`, `rev`, `progress`, `progressAll`, `progressIfSync`. Notes: `simp only [h,
  ↓reduceIte]` for an `if` under binders; stale oleans after a definition change — rebuild the
  dependent spec modules; `go.delete_underlying` on a named map. Checks: `goose --check`
  passes (no regeneration); the global baseline unchanged (70 axioms, 1 sorry: `verify.Verify`
  was the server's already), the mvcc collection 18 axioms (`verify.Verify` added), the
  others unchanged; verified-code: mvcc 85 of 155 functions (11 conditional on the tree's
  contract), 909 of 2073 lines. Next: 3b (`syncWatchers`, `moveVictims`, the loops,
  `rangeEvents`/`kvsToEvents`, `New`/`newWatchableStore`/`Close`/`NewWatchStream`), after the
  merge of `lean`'s hook change (the batch lock runs the server's post-lock hook).
- **Unit 3b, the sync machinery and the constructors** (2026-10-12). **The backend reads a
  revision range**: `keyReadSnap` gains `keyRangeReadSpec` (`UnsafeRange(Key, lo, hi, 0)` with a
  non-nil `hi` returns `rangeVals ks vs m klo khi`: read-only slices of the entries of the
  snapshot with `klo ≤ k < khi`, in key order, `BucketRange.lean`: `bucketRange` as a filter
  then a merge sort by `GoStringLe`, characterized by membership and strictly increasing keys);
  the point read unchanged. `SyncModel.lean` (pure): `u64Be_lt` (big-endian bytes order the
  values), `bucketRange_logEnts` (the range read of a well-formed log at `[revBytes lo,
  revBytes hi)` is the entries of revisions `[lo, hi)`: `KvEnt`, `logEnts`), `logEnts_events`,
  `memberBatch_logEvents` (a member's batch of the range's events is `watchEvents` from its
  `minRev` to `hi`, or to `moreRev` under the cap, `m < moreRev < hi`). `InvWatchSync.lean`:
  `entsEvents`/`wgCovers` (the `contains` interface is the chosen group), `moverRes` (what the
  victim mover holds per watcher out: the `Wo` population), the wait group (`wsWgInv`,
  `wsDone`, `wsWaiter`: the counter equals the done tokens out), the closers (`stopCloser`,
  `storeCloser` — `store.Close` closes `stopc`, a second close would panic —, `wsCloser`),
  `isStopChan` as Perennial's broadcast idiom. `InvWatchGroup.lean`: `ownWatcherGroupAt wg W
  ws` (the all-watchers map explicit: `syncWatchers` ranges over `unsynced.watchers` while
  deleting from it; `add`/`delete` keep `ws`, `.spec_group` gives the old form; `size` at any
  fraction). `InvWatchStore.lean`: `victimBatchOk` in the victim's facts (a batch's `moreRev`,
  if set, is the state's `minRev`; its events between the watcher's first revision and
  `minRev`: `moveVictims` resends without bounding the log); `σ.Lmu <+: C` suffices (no
  `Lmu = C`). Package facts: `chanBufLen = 128`, `maxWatchersPerSync = 512` (a chosen group is
  non-empty, its `minRev ≤ curRev`), `watchResyncPeriod`, `slowWatcherGauge`'s `Set`.
  **Proved**: `kvsToEvents` (unmarshal, the tombstone's `ModRevision`, `contains`), `rangeEvents`
  (the view at a fraction and the group back; the events of `[minRev, maxRev)` the group covers),
  `syncWatchers` (`choose`, the range read, the batches, the loop moving watchers synced or to
  the victims), `moveVictims` (the victims out, sent outside the lock, re-added by `minRev ≤
  curRev`, the failed ones appended), `syncWatchersLoop` (tickers; `select` on the ticker and
  `stopc`), `syncVictimsLoop` (a nil-able `time.After` channel, `victimc`, `stopc`), `ChanBufLen`,
  `newWatchableStore` (NewStore with the hook, the groups by their wands, the channels, the
  read view overwritten with the watchable store as its `kv`, the write view dropped, the
  lessor's range deleter as before; conditional on `ownIvt_split` through
  `watchStoreInv_fractional`), `New` (two readers and done tokens to the forked loops; returns
  the `WatchableKV` with `isWatchableStore`, `hookIs`, `watchWriter γ [[], []]`,
  `actualMaxReaders - 2` readers, `wsCloser`), `Close` (`close(stopc)`, `wg.Wait`, the inner
  `Close`), `NewWatchStream` (the channel, its invariant allocated, the stream's mutex, the
  open token and the consumer's empty prefix `watchConsumer γc []`). **Axioms**: `time.NewTicker`
  (a positive period; `isTicker`: `C` a bag of times), `Ticker.Stop`, `Ticker.Reset` (a positive
  duration, as Go documents: it panics otherwise), `time.Since` (returns a positive duration —
  a clock assumption, see the finding), `store.Close` (with `storeCloser`). **A finding**
  (`issues/etcd-watch-sync-ticker-reset-zero.md`): `syncWatchersLoop` calls
  `delayTicker.Reset(time.Since(st))`, which panics when the monotonic clock did not advance
  (Windows' coarse clock); the proof needs the `time.Since` assumption exactly there. Proof
  notes: a multi-line struct literal inside `ihave` fails to parse (`WsState.mk` or one line);
  `syncWatchers` needs `set_option maxRecDepth 20000`; Iris's `PartialMap.filter`/`∪` are not
  definitionally `GMap`'s (bridge with `ext`); zipping replicated reader lists inline hits
  kernel recursion (`watchReaders_of`); ghost allocation while the goal is still a WP. Checks:
  `goose --check` passes; the build 2792 jobs; the global baseline 87 axioms, 1 sorry (the five
  above), the mvcc collection 23; verified-code: mvcc 87 of 155 functions (20 conditional on
  the tree's contract), 915 of 2073 lines; `watchable_store.go` 8 verified + conditional of 21
  (`Restore` unspecified). Next: 3c, the consumer's receive lemma and the watch-guarantee
  theorem.
- **Unit 3c, the client's side and the theorem** (2026-10-12; `WatchRecv.lean`). The channel
  invariant strengthened in two places: `delivsCut` (every prefix of a watcher's deliveries
  ends at a revision: `evsWf` of the prefix's flattened events; `watcher.send` builds it from
  the old cut and the new `evsWf`, the spec unchanged) and `∀ x ∈ sent, x.w ∈ L` (every
  response sent is for a registered watcher). **`watchRecvOk γ w rs`** (persistent): the
  responses `rs` received so far for the watcher `w` are its deliveries — their events,
  concatenated, are the segments (each filtered by predicates `w`'s filters implement) of
  `watchEvents L r lo d`, `w`'s events of a log `L` the index's history has, from its first
  revision `lo` to some `d` — with `respOk` of each (the shortest prefix of the deliveries
  matching the received, `delivs_prefix_cut`). **`wp_watch_receive`**: the client's `v, ok :=
  <-ch` on the stream's channel (the facts `NewWatchStream` returns: `isChan`, the invariant,
  `watchConsumer γc received`): on `ok`, `watchConsumer (received ++ [r]) ∗ respIs v r ∗ respOk
  r ∗ watchRecvOk γ r.w (the received responses for `r.w`)`; else the consumer unchanged (the
  channel closed and drained; `watch_recv_au` is the `recvAu` form for a blocking `select`).
  **The theorems**: `watchRecvOk_cert` — with any certificate `idxCert log'` of a log long
  enough (`d ≤ log'.length`), the received events are the filtered segments of `watchEvents
  log' r lo d` (two history lower bounds are comparable: `histOf_cmp_log`, `watchEvents_cmp`);
  `watchGuarantee_unfiltered` — a watcher with no filters receives, concatenated, exactly
  `watchEvents log' r lo d`: the changes of the keys in its range at revisions from its start
  revision on, in revision order, once, up to some revision; `watchRecvOk_revs` — every
  response's revision is at or above its events' mod revisions, and a response with events
  carries the watcher's id. `Results.lean` prints their axioms: `propext`/`choice`/`Quot.sound`
  and the translation's axiomatized types only — no `sorry`, none of the package's
  trust-boundary axioms (the receive never reaches `ownIvt_split`, `verify.Verify` or the
  tickers). Note: `watchStream.Chan()` returns the channel with `P.C ch = True`, so a client
  learns it is the stream's channel from `NewWatchStream`'s postcondition, which the receive
  lemma takes. Proof notes: rebuilding the channel invariant after a state change needs
  `chanIsClosed` simplified on both the hypotheses (`irevert … simp only … iintro`) and the
  goal; `recvAu`'s later comes after the mask change, so the invariant opens with no credit.
- **The watchable store, what is proved** (2026-10-12): every function of
  `watchable_store.go`, `watchable_store_txn.go`, `watcher.go` and `watcher_group.go` but
  `Restore` (out of scope), over the KV store's contracts, the interval tree's contract
  (pending: unit 4), five time/close axioms and `verify.Verify`; the watch guarantee as the
  theorems above, safety only (nothing says a victim's batch is eventually sent). Remaining:
  unit 4 (the red-black interval tree's proof: `ownIvt` defined, the seven specs and
  `ownIvt_split` proved, discharging the 20 conditional results), `Restore`/compaction (out of
  scope), the `time.Since` assumption (a finding).
- **Unit 4a, the interval tree's representation and reads** (2026-10-12;
  `Proof/go_etcd_io/etcd/pkg/v3/adt/`). **The model** (`Tree.lean`, pure): `RbT E` (`leaf |
  node c l e r`), `inorder`, `color`/`blackHeight`/`redOk`/`rootBlack`/`RbOk`, `IvSorted`,
  `maxEnd` (the largest end of a subtree, affine) with `nodeMax` mirroring `updateMax`,
  `rotateLeft`/`rotateRight` (`inorder_rotate*`), the reads' descents as pure functions
  mirroring the code (`findE`, `intersects`, `visitL`) with `findE_eq` (the sorted tree's
  `find?`), `intersects_iff` (true iff `stab ≠ []`, no premise on the query), `visit_stab`
  (`visitL q = stab q` for a proper query), `maxEnd_ge`/`maxEnd_mem`, the overlap
  characterizations `ivlCmp_{eq_zero,neg,pos}_iff`. **The representation** (`Defs.lean`):
  `ownNode s q p n T` (the leaf is the sentinel; a node's `iv` (owned at `q`: `Delete` writes
  it), `max` = `maxW (nodeMax l e r)` — exact by construction, no separate `maxOk` —,
  `left`/`right`/`parent`/`c` at `q`, the children recursively), `ownSentinel` (its fields
  existential: `Delete` writes its `parent`), `ownIvt t L q := ∃ tv T, t ↦{q} tv ∗ ownSentinel
  ∗ ownNode (root) T ∗ ⌜T.inorder = L ∧ RbOk T ∧ IvSorted L ∧ count = L.length ∧ L.length <
  2^63⌝` (the bound: `Stab` returns `nil` on `count == 0`, so the count must not wrap; `Insert`
  will take `L.length + 1 < 2^63`, which the group proves from its map's bound). `NodeLemmas.lean`:
  split/combine with agreement (`ownNode_split`/`_combine`, `ownIvt_split'`/`_combine`:
  `ownIvt_split` proved), `ownIvt_not_null`, `ownIvt_read`, `iv_open`; `Holes.lean`:
  `ownNodeH` (a subtree whose overlapping nodes have lent their `iv`), `ownNodeH_fill`, the
  visitor protocols `nodeVisitorOk`/`ivVisitorOk`. **Two contract corrections** (decisions.md,
  "Two corrections found by the tree's proof"): `Find`/`Stab` lend the pointers at the tree's
  fraction with a wand (the nodes' pairs are written by `Delete`), and `Stab` takes `⌜b = "" ∨
  affLt b e⌝` (`visit`'s pruning is wrong for a degenerate query); the group's `add`/`delete`/
  `watcherSetByKey` adapted (the point query's premise `adt.point_ok`, `strLt_append`).
  **Proved**: `NewIntervalTree`, `Len`, `find` (a subtree and a wand back to the root; new spec),
  `Find`, `Intersects`, `intervalNode.visit` (new spec: by induction on the model, the visitor
  keeping each `iv`), `Visit` (new spec), `Stab` (`ivs` heap-allocated for the closure),
  `ownIvt_split`; `Insert`/`Delete` stay pending (`?`). `Results.lean` prints the pure lemmas'
  axioms (standard only). Notes: `intervalTree__find.lean` and `intervalTree__Find.lean` differ
  only in case (a case-insensitive filesystem would collide); `wp_if_destruct` splits a
  `decide` inside `HΦ` (rewrite the result first); `_root_.decide_true`; the sentinel is only
  ever compared against, never read. **A silent `sorry`**: `wp_apply` of an Iris-hypothesis
  triple (the visitor's protocol) on a call wrapped in `exceptionDo (return: …)` failed
  without an error, closing the branch with a synthetic `sorry` (the only sign:
  `declaration uses 'sorry'`; the TCB check caught it: `sorry adt.intervalTree.Visit.wp_proof`);
  the fix is `wp_bind (App (Val #f) (Val #x))` then `iapply` the hypothesis — and every
  per-file check must look for `sorry`, not only for errors. Checks: the build 2808 jobs;
  `goose --check` passes; the global baseline unchanged (87 axioms, 1 sorry), every collection
  matches (adt still 0 axioms with its new results); verified-code: mvcc 94 of 155 functions
  sorry-free (13 conditional on `Insert`/`Delete` only now), 1013 of 2073 lines; adt 11 of 42
  functions, 129 of 548 lines. Next: 4b (`Insert`), 4c (`Delete`).
- **Unit 4b, `Insert`** (2026-10-12). **The model** (`TreeInsert.lean`): the tree with a hole
  `RbCtx` (`top | inL c p e r | inR c l e p`, `plug`, `inorder_plug_congr`, `blacken`),
  `insertBST` mirroring the descent (left iff `ivlLt z e`, so equal intervals go right, as
  `ivtInsert` puts the new entry after the equals: `inorder_insertBST`), `nodeMaxO` and
  `nodeMax_rotate`, the fixup invariant `FixInv C t` (CLRS 13.3: `z` red with black children,
  consistent black heights, the only violation `z` under a red parent, the root black unless
  `z` is it) with `fixInv_start`, `fixInv_exit` (the root blackened: `RbOk`) and one lemma per
  loop case (`fix_red_LL/RL/LR/RR`, `fix_black_LL/RL/LR/RR`), each keeping the invariant and
  the in-order list. **The hole predicate** (`Ctx.lean`): `ownCtx t s C n p mh`, the path from
  the root to the hole `n` (each frame the parent's fields at `1` and its other subtree as
  `ownNode`; the frames' maxima `nodeMaxO` of the hole's `mh`, so a stale hole leaves the
  ancestors consistently stale until `updateMax` walks up), with up/down/push/plug lemmas and
  the distinctness facts. **Proved** (new specs, `Spec/…/adt/`): `intervalNode.color`,
  `createIntervalNode` (a red node, `max` its end, the sentinel around), `intervalNode.updateMax`
  (the walk up recomputing `nodeMaxO`, stopping when unchanged: sound, nothing above changes),
  `replaceParent`, `rotateLeft`/`rotateRight` (field level; the early return when the child is
  the sentinel is a contradiction under the premise), `insertFixup` (the loop under `FixInv`),
  `Insert` (the descent with `y` the last node, the link, `y.updateMax`, the fixup, `count++`).
  **The watcher budget** (decisions.md, "The watcher budget"): `Insert.spec`'s premise
  `⌜L.length + 1 < 2^63⌝` is supplied by the group (`watcherGroup.add` and `choose` take
  `⌜W.size + 1 < 2^63⌝`; `rangesOk_length_le : L.length ≤ W.size`), which the store's lock
  invariant gives: `watchBudget γ q M := ∃ n, ownTokAuthDfrac γ.wt (own q) n ∗ ⌜M.size + n + 3 ≤
  2^63⌝` over the named watchers `σ.M` (`WsOk.ws_size`/`wu_size`), `WatchParams.T := watchTok γ`
  (a token the stream's `Watch` and the store's `watch` take and spend, `watchBudget_spend`;
  no refund on cancel), `New`/`newWatchableStore` return `watchToks γ (2^63 - 3)`. **Duplicates**
  (decisions.md, "Duplicates in the tree"): `IvSorted` is non-strict (`¬ ivlLt b a` pairwise);
  `Insert.spec` has no distinctness premise (it is the request path's `InsertAny`); `Find.spec`
  returns some entry with the interval (the code's `find` returns the topmost duplicate) or
  `nil` with none; `Delete.spec` (pending) removes some entry with the interval (`eraseIdx`);
  `findE_eq` became `findE_some`/`findE_none`; `visit_stab`/`intersects_iff` hold as before;
  the group keeps one interval per range (`RangesOk` strict; `rangesOk_find_unique`,
  `eraseIdx_eq_eraseP_fst` recover `find?`/`eraseP` in `add`/`delete`). Notes: a pure
  conjunction in an `iintro` pattern binds whole, `obtain` after; a rebuild site listing
  hypotheses by name silently drops a new conjunct (every lock-body rebuild got `Hwt`);
  `rw [ownCtx_inL]` hits the first match (often inside `HΦ`): give the arguments; `black`/
  `red` are `val` constants (`rw [show black = #(colorW .black) from rfl]`). Checks: the build
  2825 jobs; `goose --check` passes; the global baseline unchanged (87 axioms, 1 sorry), every
  collection matches; verified-code: mvcc 98 of 155 functions sorry-free (9 conditional on
  `Delete` only), 1109 of 2073 lines; adt 20 of 42 functions, 283 of 548 lines. Next: 4c (`Delete`).
- **Unit 4c, `Delete`: the tree complete** (2026-10-12). **The model** (`TreeDelete.lean`):
  composed contexts (`RbCtx.comp`, `plug_comp`, `depth`, `AllL`: a path of left frames),
  the in-order list around a hole (`leftL`/`rightL`, `inorder_plug`), the two splices
  (`del_inorder_one`: a node with at most one child replaced by it, its entry gone at its
  index; `del_inorder_two`: the successor `y` spliced out and its entry copied into `z`,
  `rb_entry`: the red-black properties do not depend on an entry), the `max` augmentation
  through a context (`RbCtx.upMax`, `maxEnd_plug`), and CLRS 13.4's loop invariant `DelInv C t`
  (`t` red-black below its root with an extra black, the context's black heights consistent
  with `h + 1`, no red violation in the context, the root black unless `t` is it) with
  `del_start` (a black spliced node establishes it; a red one leaves a red-black tree),
  `delInv_exit` (`x` the root or red: blackening it gives `RbOk`), `delInv_sib_L/R` (the
  sibling is a node: the two `if w == nil { break }` are unreachable) and one lemma per case
  and side (`del_case1..4_L/R`), each keeping the invariant and the in-order list. **The paths
  with their locations** (`CtxAt.lean`): `Delete` and the fixup read `x.parent` and `z` back
  after helpers that walk up through them (`y.parent.updateMax` through `z`'s frame; `x.parent`
  after `rotateLeft(x.parent)`), which `ownCtx`'s existential frames lose; so `ownPathAt s q A
  ls n p mh` lists each frame's parent and other child (`ls`, innermost first; `topAt A ls n p`
  its top) and `ownCtxAt t s C ls n p mh` is such a path from the root (`ownCtx_at`:
  `ownCtx ⊣⊢ ∃ ls, ownCtxAt`; `ownCtxAt_comp`/`ownCtxAt_split` join and split at a path's
  top). The 4b specs of `updateMax`, `replaceParent` and the rotations take `ownCtxAt … ls …`
  and keep `ls`, the rotations give the rotated-down node's fields back explicitly, and `find`
  returns the node under `ownPathAt` (`topAt … = (root, s) ∧ C.plug Tz = T`) instead of the
  wand; the old forms are derived (`CtxSpecs.lean`: `updateMax_ctx`, `rotateLeft_ctx`,
  `rotateRight_ctx`), so `Insert`/`insertFixup`'s proofs and `Link.lean` are unchanged, and
  `Find`'s is adapted. **Proved** (new specs): `intervalNode.min` (the leftmost node of a
  subtree under its path of left frames), `intervalNode.successor` (for a node with a right
  child, `min` of it; the walk up the parents is unreachable under the premise),
  `intervalTree.deleteFixup` (at a hole under `DelInv`; `x` may be the sentinel, whose `parent`
  the splice wrote: `sentAt s x p`, and whose colour the exit writes through the whole-struct
  points-to; the result red-black with the hole's in-order list), `intervalTree.Delete` (`find`;
  not found: unchanged; one child: the splice; two: `successor`, the splice of `y`,
  `y.parent.updateMax` up through `z`, `z.iv = y.iv`; a black spliced node: the fixup;
  `count--`), with `Delete.spec` as written in 4b (the entry at some index with the interval
  erased). The nine mvcc results conditional on `Delete` (`watcherGroup.delete`, `notify`,
  `watchableStoreTxnWrite.End`, `cancelWatcher`, `watch`, `syncWatchers`, `syncWatchersLoop`,
  `New`, `NewWatchStream`) are now linked theorems: `adt_intervalTree__Delete: @`, no `?` left in
  either link list. Notes: `Delete`'s statements after `x.parent = y.parent` are right-nested
  (a `let:` body), so `wp_join … at next N` sees one statement: join around the `if y.parent ==
  s` instead; `wp_join (Q := …) at (if: _ then _ else #false)` joins an `&&` condition, the `at`
  clause before `with`; after `wp_join` a case may already be closed (`try`, `first | rfl |
  trivial`); `icases lemma $$ [H1 H2]` with two same-shaped premises can match them the wrong
  way round (give the arguments); `unfold adt.ownIvt at h` before `iapply` when the goal has it
  folded. Checks: the build 2835 jobs, no repo `sorry`; `goose --check` passes; the global
  baseline unchanged (87 axioms, 1 sorry), every collection matches (adt: standard axioms
  only); verified-code: mvcc 107 of 155 functions verified, all sorry-free (was 98, 9
  conditional), 1334 of 2073 lines; adt 24 of 42 functions, 398 of 548 lines (the 14 others
  translated only: `Union`, `MaxHeight`, the `String`s, `visitLevel`, the generic comparables).
- **Unit 4d, `Union`** (2026-10-12, after the merge of `lean` at `fd5d5306e`, which brought the
  request path's `Union.spec`, restated in the contract's style: see "Merge: lean into mvcc, the
  request path"). `Union(inIvt, ivl)` is `inIvt.Visit(ivl, f)` with `f` inserting each visited
  entry into the receiver: proved over `Visit` and `Insert` with the invariant `I acc := ownIvt t
  ((acc.map Prod.snd).foldl ivtInsert L) 1 ∗ [∗list] x ∈ acc, x.1 ↦{q'} …` (the lent pairs kept
  until `Visit` takes them back), the result exactly `stab (b, e) L'` (`Perm.refl`), the lent
  pair split into fields for `wp_auto` to read `Ivl`/`Val` and recombined. **A third contract
  correction** (decisions.md, "The visitor's position"): the closure calls `Insert`, whose premise
  `L.length + acc.length + 1 < 2^63` needs `acc.length < L'.length`, which `ivVisitorOk`, holding
  for any `acc`, could not give; `nodeVisitorOk`/`ivVisitorOk` now take the list `S` of the
  entries the visitor will see and each call has `⌜acc.map Prod.snd ++ [z] <+: S⌝` (the visited
  entries and this one a prefix of `S`): `Visit.spec` passes `S := stab (b, e) L`, `visit.spec`
  takes `S` and the premise `acc.map Prod.snd ++ stab (b, e) Tx.inorder <+: S` (its proof:
  `stab_node`, `List.map_snd_zip`, `ownNodeH_length` before the right recursion), `Stab`'s closure
  ignores it; `Stab.spec` and everything outside adt unchanged. `length_foldl_ivtInsert`
  (`Model.lean`). The v3rpc `checkIntervals` and `kvServer.Txn` are now unconditional
  (`adt_intervalTree__Union: @`; no `?` in any link list). Checks: build clean, no repo `sorry`;
  `goose --check`; the global baseline unchanged (99 axioms, 9 sorries); every collection
  matches (v3rpc 24/0 as before: the tree was a hypothesis, not an axiom); verified-code: adt
  25 of 42 functions, 405 of 548 lines; v3rpc 17 of 116 (`checkIntervals`, `Txn` now verified),
  248 of 1722 lines; mvcc 108 of 155, 1340 of 2073 lines; etcd 677 of 3599 functions, 7498 of
  45570 lines.
- **The whole watchable store** (2026-10-12, units 1a–4d). Every translated function of
  `watchable_store.go`, `watchable_store_txn.go`, `watcher.go` and `watcher_group.go` but
  `Restore` (and the compaction path of the store, out of the plan) is verified against the
  model, the client's watch guarantee (`wp_watch_receive`, `watchGuarantee_unfiltered`,
  `watchRecvOk_revs`) rests on no trust-boundary axiom of the package, and the interval tree
  (`pkg/v3/adt`: every function of `interval_tree.go` the group and the request path call,
  with their helpers; not `MaxHeight`, the `String`s, `visitLevel`) is proved under its own representation
  invariant: no pending contract remains (`etc/link-lean-first-adt.txt` has no `?`; the adt
  collection is its whole `Link.lean`). `watchable_store.go` is verified at 20 of 21
  functions (`Restore`), 381 of 395 lines; `watchable_store_txn.go`, `watcher.go` and
  `watcher_group.go` whole. Still assumed, of the package: the store's `restore`
  and `Close`, the scheduler, the hash storage, the backend's bucket helpers, zap, protobuf,
  the tickers and `time.Since` (positive: `issues/etcd-watch-sync-ticker-reset-zero.md`),
  `trace.SpanFromContext`, `verify.Verify`. Next: merge `lean` at `a95ad2bb4` (the request
  path's unit 3b); `Restore`.

## Small etcd axioms (2026-10-12)

Branch `etcd-small-axioms` (worktree `/shared/etcd-grove-small`, off `lean` at `436f363c4`,
`origin/lean` merged at `bcf23ae1d`). Trust-boundary axioms on small etcd functions replaced by
proofs: 70 axioms to 62 (1 sorry, unchanged); etcd 505 verified of 3599 functions, 5202 of 45570
lines (11 functions, about 51 lines, more).

- **Translated** (bodies added to the names-only packages): `mvcc.NewHashStorage`,
  `schema.UnsafeCreateMetaBucket`, `traceutil.TODO` (and the trace types: `traceutil.toml` imports
  `time`, `zap`), `notify.Notifier.Notify`, `config.ServerConfig.ElectionTimeout`,
  `v3alarm.AlarmStore.Get` (and `etcdserverpb.AlarmType_NONE`, an opaque `val` otherwise),
  `EtcdServer.Logger`/`isLeader`/`MemberID`/`Lead`/`getLead`, `pbutil.MustUnmarshalMessage`
  (still an axiom). Goose takes all of them as pinned.
- **Proved, spec unchanged**: `NewHashStorage`, `TODO` (post strengthened: not nil).
- **Proved, premise added** (each caller discharges it): `UnsafeCreateMetaBucket` takes the batch
  transaction's `UnsafeCreateBucket` triple (any `P`; `NewStore` passes `batchTxSpec`'s);
  `ElectionTimeout` the two `Cfg` fields read-only; `isLeader` `s.memberID` read-only and the
  atomic `s.lead` in an invariant (`srvLeadInv`); `AlarmStore.Get` takes `aty : w32` and
  `isAlarmStore a` (`v3alarm/Defs.lean`: `a.mu` over the owned map of owned sets);
  `Notify` takes `isNotifier n` (`notify/Defs.lean`: the `RWMutex` writer guard over the
  cache's broadcast-channel idiom, its broadcast `True`); `Logger` takes `s.lg ↦□ l` and a
  reader slot of `s.lgMu` (`srvLgReader`, not persistent: Perennial's `RWMutex` bounds readers),
  given back. The server's `isServer`/`srvFieldsAt` carry all the persistent facts (a premise of
  the roots, which nothing constructs); `srvLgReader s` is threaded through `applyEntryNormal`,
  `apply`, `applyEntries` (pre and post). `Notify` closes a channel, so `isServer` and those
  three specs moved to `HeapGS HasLC.hasLC` (the Link's `links_hasLC` section).
- **`AlarmStore`'s struct** has a field of an axiomatized type (`schema.AlarmBackend`), whose
  generated instances are `sorry`: the proof gives `TypeRepr AlarmStore` from its
  `TypeAssumptions` (as `InvServer.lean` does), so no result reaches them.
- **`Trace.Step` required a non-nil trace** (it said any `t`, `nil` included, but `Step` reads
  `t.stepDisabled`): `store.Read`/`store.Write` take `trace ≠ null`, `storeTxnReadIs`/
  `storeTxnWriteIs` record it (`%Htrnn`, last), `rangeKeys` takes it as a premise; readView/writeView
  have it from `TODO`, the txn package from `EnsureTrace`/`Get`.
- **`MustUnmarshalMessage`'s axiom was false of the code**: it returned on any bytes, the code
  panics unless `proto.Unmarshal` succeeds. It now takes `isConfChangeEncoding bs` (opaque,
  `InvRaftpb.lean`), which `entriesFrom` states of every conf-change entry. Still an axiom: the
  `proto.Unmarshal` axiom is about `mvccpb.KeyValue` only, and a second spec of the same Go function
  would not fit the one-spec-per-function layout. (Merged into `lean` with the apply package's spec, a conjunction of a case per message type: the premise is on the `ConfChange` case.)
- **Left as axioms**: `GoAttach` (its spec takes any `f` and forks it: unprovable without a spec
  of `f`, whose closure calls the untranslated `raftRequest`; also a `wgMu` reader slot and the
  `stopping` channel); `stopWithDelay` (Perennial has `time.wp_After`, but the `select`s on
  `s.done`/`s.errorc` need those channels' protocols, which nothing models); `verify.Verify`
  (Perennial has no `os.Getenv`); `membership.RaftCluster.Members` (`Member.Clone`'s deep copy and
  `sort.Sort`); `schedule.NewFIFOScheduler` (forks `f.run`, a loop over a cond and channels).
- **traceutil**: only `TODO` proved. `Step`/`StepWithFunction`/`AddField`/`StartSubTrace`/
  `StopSubTrace` append to the trace's slices, a non-atomic update that needs exclusive ownership
  of the `*Trace` (an invariant cannot cover an `append`). But the traces the txn package steps
  come from `traceutil.Get(ctx)`/`EnsureTrace`, i.e. from `ctx.Value(TraceKey{})`, and the same
  trace is also in the mvcc transaction (`kv.Read(mode, trace)`): an ownership predicate would
  have to come out of those axioms, and two calls of `Get` on one context would hand out two
  copies of an exclusive resource (unsound) unless the context's values are modelled. Perennial's
  `isContext` specifies `Value` only for `&cancelCtxKey` and has no `WithValue`, so `Get` and
  `EnsureTrace` stay axioms and so do the five methods.

## The server's txn package (`server/v3/etcdserver/txn`)

Plan: `decisions.md`, "The server's txn: the two models meet, the sole writer as tokens" (units 0
to 4; unit 0b, the index answering the state, in parallel with unit 0, in the main tree).

### Unit 0: translation and scaffolding (2026-10-11)

Branch `txn-u0` (worktree `/shared/etcd-grove-txn0`, off `lean` at `e3effe933`).
- **Translation**: `Code/go_etcd_io/etcd/server/v3/etcdserver/txn.toml`, bodies for every
  function of `txn.go`, `put.go`, `range.go` (with `kvSort`, the five `kvSortBy*` and their
  promoted `Swap`/`Len`) and `delete.go`; `util.go` (`WarnOf*`, `isNil`: reflect) and
  `metrics.go` (`ApplySecObserve`, `RangeSecObserve`, the metrics, `init`: prometheus, a float
  division) names only; listed in `etc/goose.py`. `etcdserverpb.toml` adds the requests
  (`TxnRequest`, `RequestOp` and its four oneof wrappers, `RangeRequest`, `PutRequest`,
  `DeleteRangeRequest`; until now axiomatized types), the eight sort constants and
  `RequestOp.GetRequestRange` with its body. Every other package the code names was already
  translated (`sort`, `bytes`, `math`, `fmt`, `time`, `context` Perennial's; `proto`, `zap`,
  `traceutil`, `lease`, `etcdserver/errors`, `mvcc` names-only or the mvcc core). Goose (Perennial
  `e4e126e46`) accepts the package as pinned (`bc8b52a50`): no Gooseable change. The
  translation, for the proof writers: package `go_etcd_io.etcd.server.v3.etcdserver.txn`, its
  `Assumptions` include mvcc's, `sort`'s, `context`'s, ...; `trace.StepWithFunction(func() {...},
  msg)` passes a `FuncLit`; `lg.Panic` is `MethodResolve (*zap.Logger) "Panic"`; `sort.Sort`
  is `sort.«Sort»`; `mkGteRange`'s `[]byte{}` is a slice composite literal.
- **Base** (`Proof/.../etcdserver/txn/Base.lean`): `txnInit` states the two foreign error
  variables the code returns, `lease.ErrLeaseNotFound` and `etcdserver/errors.ErrKeyNotFound`
  (their packages' facts are mvcc's `True` and the server's `ErrNoSpace`, left unchanged); no
  fact of the package's own (its metrics are read only by names-only code).
- **Requests** (`Requests.lean`, persistent predicates): `rangeRequestIs r o`,
  `putRequestIs p o`, `deleteRangeRequestIs d o` denote the client model's `OpFull`
  (`rangeOpOf`, `putOpOf`, `deleteOpOf`, with `proj_simps`; decision: reuse `OpFull`, not a record
  of the fields); `rangeEndOf` reads a range end as mvcc does (`nil`: the key; empty non-nil:
  from the key on, `[0]`); `putTxnOp` is the server's total put; `compareIs c cm` (`CmpModel`,
  the client's `compareAt` with the server's range end), `comparesIs`; `requestOpIs`/
  `requestOpsIs` (mutual, structural through nested transactions) and `txnFieldsIs`,
  `txnRequestIs rt t`; responses `kvIs`/`kvsIs` (the cache's `kvValAt` without the cache's
  assumptions), `rangeResponseIs resp rev kvs more count`, `putResponseIs resp rev prev`,
  `deleteRangeResponseIs resp rev n prevs`, `responseOpIs`/`responseOpsIs` (mirroring
  `TxnOpResult`, nested responses with header revision `0`), `txnRespFieldsIs`,
  `txnResponseIs resp rev t ok rs`. The put request's size cache is in an invariant (`proto.Size`
  stores it atomically). **`Defs.lean`**: `isKV kv s γ`, `isTxnLessor le γl` (mvcc's `isLessor`
  plus `Lookup`: `nil` or `leaseKnown`). No `soleWriter` (unit 0b's).
- **Axioms** (trust boundary, each `Spec/<pkg>/<fn>.lean` + `Proof/<pkg>/<fn>.lean`):
  `sort.Sort` (over `sorterSpec x R lt`, the `Len`/`Less`/`Swap` triples on a model list: a
  permutation sorted by a strict weak order `lt`, at most `2^62` elements; Perennial translates
  `sort` without it) and `sort.Reverse` (`Less` flipped); traceutil (names-only)
  `EnsureTrace` (a context with the input's deadline and `Done`, `{ cd with Values := vs }`, and
  a non-nil trace; decision: the derived context's descriptor, since `EnsureTrace` returns
  `context.WithValue(ctx, ...)` when `ctx` has no trace, and Perennial has no `WithValue`),
  `Get` (a non-nil trace), `Trace.StepWithFunction` (`WP f() {{Q}}` in, `Q` out: it runs the
  closure, a panic propagating), `Trace.AddField`, `StartSubTrace`, `StopSubTrace` (return; all
  on a non-nil trace); `proto.Size` of a `*pb.PutRequest` (an `int ≥ 0`); `zap.Logger.Panic`
  (a panic outcome `PanicV p`: zap writes then panics); `zap.Int32`; `txn.RangeSecObserve`,
  `txn.ApplySecObserve` (metrics: return). Existing ones reused: `traceutil.TODO`,
  `Trace.Step`, `zap.Error`, `zap.Logger.Error`, `context.TODO`; Perennial's `fmt.wp_Errorf`,
  `bytes.wp_Compare`, `time.wp_Now`/`wp_Since`. `zap.Duration` is not needed (only `util.go`).
- **mvcc's read-only write transaction** (additive, `InvRoTxn.lean`: `isRoTxnWrite trw s γ log
  rev`): `NewReadOnlyTxnWrite`, `txnReadWrite.FirstRev`/`Rev` (through the promoted methods down
  to `storeTxnCommon`'s), `Range`/`End` (to `metricsTxnWrite`'s), `Changes` (`nil`), `Put`/
  `DeleteRange` (a panic outcome): specified and proved, sorry-free, in
  `etc/link-lean-first-mvcc.txt`, mvcc's `Link.lean` regenerated (additions only).
- **Linking**: `etc/gen-link.py --txn` (namespace `txn`, the txn package's assumptions),
  `etc/link-lean-first-txn.txt` (the 18 trust-boundary functions; mvcc's wrappers as `@`; the
  package's 38 functions and `RequestOp.GetRequestRange` commented out with a first guess of
  their callees),
  `Proof/.../txn/Link.lean`, `Results.lean` (prints the mvcc wrappers' axioms),
  `etc/tcb-collections/txn.txt`. `etc/proof_roots.py` picks them up by directory.
- **A finding** (`issues/etcd-txn-empty-requestop.md`, reproduced): `Txn` panics on a
  `RequestOp` whose oneof is empty (`executeTxn` reads the `nil` response `newTxnResp` left for
  it), inside the write transaction (the batch lock stays held); the gRPC layer rejects such
  requests, so it is an unstated precondition. The request predicates give it no denotation.
- **For the next units**: (1) `mkGteRange("\x00")` returns `[]byte{}`, which Go makes
  non-nil, and mvcc's spec (`decide (endk = slice.nil)`, `rangeAnswers`' `endNil`, `inRange`'s
  `e = []` as no bound) reads a non-nil empty end as no upper bound, as the index does
  (`end == nil`, then `len(end) > 0`): consistent. But Perennial's `wp_slice_literal` quantifies
  over the literal's pointer, so a proof cannot tell `[]byte{}` from `slice.nil` through it; the
  allocation's typed points-to gives `ptr ≠ null` (`typedPointsto_not_null`), so units 1 and 2
  need a literal lemma that keeps it. (2) A range inside a transaction with `Revision ≠ 0` reads
  another revision, which the model's `TxnOp.get` does not (it reads the transaction's state):
  `txn_runTxn` needs a premise on nested ranges' revisions. (3) A range answered header-only
  (`skipRangeExecution`) is not described by `responseOpIs`. (4) Comparisons and sort targets
  outside the protobuf enumerations denote nothing (`compareIs`, the client's codes).
- **Notes on existing specs** (this repository's, not etcd's): `traceutil.Trace.Step`'s axiom
  (mvcc's, `Spec/go_etcd_io/etcd/pkg/v3/traceutil/Trace__Step.lean`) says `Step` returns on any
  trace, `nil` included, where Go dereferences it (`t.stepDisabled`): unfaithful for `nil`,
  harmless while every trace passed is non-nil (the txn package's come from `EnsureTrace`/`Get`);
  the new trace axioms require a non-nil trace. `InvSTMRun.lean` (concurrency) failed once in a
  full build under load (an `iframe` not framing `STMSt.empty.reads` against `∅`) and passed on
  the rebuild and with `lake env lean`: a flaky elaboration, not a change of this unit.
- **Gates**: full `lake build` passes (2503 jobs; the etcdserverpb change rebuilds the cache, concurrency,
  leasing and recipes proofs unchanged); `ETCD_SRC=/shared/etcd etc/goose.py --check` passes at
  the pins; `etc/tcb-report.py --check --update`: 13 new axioms (the list above), baseline 69
  axioms and 1 sorry (was 56 and 1); `--collection etc/tcb-collections/txn.txt`: 17 axioms (the
  13 and `traceutil.TODO`, `Trace.Step`, `zap.Error`, `zap.Logger.Error`), 0 sorries; every other
  collection unchanged (mvcc 13 axioms: the wrappers rest on mvcc's existing ones);
  `etc/verified-code.py --reuse`: the txn package 48 functions, 653 lines, 39 translated with
  bodies (570 lines: `txn.go` 12/296, `range.go` 18/164, `put.go` 6/77, `delete.go` 3/33), 2
  assumed (`metrics.go`), 0 verified; mvcc 62 of 155 functions verified (was 58: the four
  read-only wrapper functions; the promoted `FirstRev`/`Rev`/`Range`/`End` are not Go
  functions), 661 lines; etcd 435 verified of 3599, 4373 of 45570 lines (was 431, 4367).
- **The trust report's grouping**: `etc/tcb-report.py` runs Lean once per set of part roots the
  roots reach; the server's `Link.lean` reaches `EtcdDeps` and clashes with mvcc's
  (`binary.bigEndian.wp_PutUint64` is in both). txn's `Base` first imported the server's
  `BaseApply.lean` for `etcdserver/errors`' instance, which put txn's roots (whose `Link`
  imports mvcc's) with the server's: the instance moved, unchanged, to
  `etcdserver/errors/Base.lean` (imported by `BaseApply`). When the apply package links txn's
  results, mvcc's and the server's Links will have to coexist (rename one side's `binary` results
  or put mvcc's in a namespace).

### Unit 0b: the index answers the state; the sole writer (2026-10-11)

Branch `txn-u0b` (from `e3effe933`), two new files in
`Proof/go_etcd_io/etcd/server/v3/etcdserver/txn/`, sorry-free; built with
`--packages=.lake/manifest-merge.json` (Perennial `e4e126e46`).

- **`Lemmas.lean`** (pure; standard axioms only). Hypotheses: `LogOk log` (`LogWf`, length and
  every revision's change count below `2^63`; `LogOk.of_cert` from `idxCert`'s pure part for a
  non-empty log), a revision `r < 2^63` (any: past the log's end the state is `stateAfter`).
  The server's range is `srvInRange endNil k e key` (`endNil`: `key = k`; else mvcc's
  `inRange`: `k ≤ key` and `key < e` unless `e = []`, no upper bound), `srvSel s endNil k e` the
  state's key-values in it. Results: `rangeAnswers_stateAt` (`List.Forall₂ (AnsKv log
  (stateAt log r))` between `rangeAnswers log endNil k e (W64 r)` and `srvSel (stateAt log r)
  endNil k e`: one for one, in key order; `AnsKv`: `findKey` of the answer's key is the
  key-value, its mod revision/create revision mains and version are the answer's, `BucketHas`
  at the mod revision; the created revision's sub-revision is not characterized), via
  `forall2_filterMap_keys` (answers by sorted keys against a sorted state); `rangeAnswers_keys`,
  `rangeAnswers_findKey`, `rangeAnswers_length`, `rangeAnswers_stateAt_w` (at a word revision,
  `sint.nat`); `rangeTaken_eq` (`takeLimit (limitOf limit)` of the answers for both kinds of
  read), `rangeTaken_nonpos`, `rangeTaken_pos`, `rangeTaken_stateAt`, `rangeTotal_stateAt`
  (`totalOf (limitOf limit) withTotal` of the selection's length); `delKeys_eq` (the keys of the
  pending state in the range, needs `LogOk (ilog ++ [pend])`, `ilog ≠ []`), `delKeys_length`,
  `applyChanges_delKeys` (the pending changes then the deletes: the pending state without the
  range); `applyChange_put` (`putKv`, `rfl`), `applyChange_del`, `applyChanges_append`,
  `applyChanges_dels`, `applyChanges_dels_sel`, `stateAfter_snoc`; `lastRev_sint`,
  `lastRev_nat`, `stateAt_lastRev` (a read transaction's `rev`).
- **The end key.** `srvEnd rangeEnd`: `[]` is `(true, [])` (a `nil` end: the one key), `[0]` is
  `(false, [])` (`mkGteRange` makes it `[]byte{}`, non-nil and empty: mvcc's `end == nil` test
  fails and `unsafeVisit`'s `len(end) > 0` test makes it unbounded), anything else
  `(false, rangeEnd)`. `srvInRange_srvEnd`: exactly the client's `inRange k rangeEnd key`
  (`InvEtcd.lean`); `srvSel_srvEnd` (= `rangeIn`), `applyChanges_delKeys_client` (a range
  delete is the client's `.delete` filter). Unit 0's request predicates must give mvcc
  `endNil := (RangeEnd = nil)` after `mkGteRange`, and an empty `RangeEnd` decodes to `nil`.
- **Shapes.** The index's history records events (revision, key, delete or not) and commit
  markers, not values: `histOf_prefix_logShape`/`histOf_prefix_shape_logShape` (a history
  prefix is a `logShape` prefix), `logShape_eq_of_prefix`. Two certificates `idxCert a`,
  `idxCert b` give `logShape a`, `logShape b` comparable (`idxCert_logShape`), not `a`, `b`.
- **`SoleWriter.lean`** (Iris). `soleWriter γ log := idxCert γ.idx log ∗ ownToks γ.revs
  (soleBudget log)`, `soleBudget log = 2^63 - 3 - log.length` (timeless, not persistent);
  `soleWriterOpen` with one token fewer. `soleWriter_of_NewStore` (`[[], []]`: `2^63 - 5`
  tokens, as `NewStore` returns), `soleWriter_split` (one `revToken`, needs
  `log.length + 4 ≤ 2^63`), `soleWriter_close` (`soleWriterOpen log ∗ idxCert (commitLog log
  pend) ∗ (if pend = [] then revToken else True) ⊢ soleWriter (commitLog log pend)`),
  `soleWriter_pins_write` (`soleWriterOpen γ log ∗ storeTxnWriteIs tw s γ ilog pend ⊢
  ⌜ilog.length = log.length ∧ logShape ilog = logShape log⌝`: the auth's count covers the
  caller's tokens and the transaction's, the writer's history authority is above the caller's
  certificate), `soleWriter_pins_write'` (keeping the resources), `stateAfter_commitLog`,
  `soleWriter_read_shape` (a read transaction's log and the sole writer's: shapes comparable).
- **Not provable from unit 0b's mvcc specs** (proposed mvcc changes, one each; all resolved by
  unit 0c, below):
  1. *Values*: the pins give the log's length and shape, not `ilog = log`; make the index
     history's commit marker carry the revision's changes (`HistItem.commit cs`, so `histOf`
     is injective and `idxCert` certifies the log itself), or add a monotone list of committed
     logs whose lower bound `idxCert` includes.
  2. *The empty `End`*: `storeTxnWrite.End` (and `txnEndPost`) with `pend = []` drops the
     `revToken` (the proof keeps `ownTokAuth`'s count): return it (`… ∗ if pend = [] then
     revToken γ else True`; the token is in `storeTxnWriteIs`). Without it a `Put`/`DeleteRange`
     that changes nothing loses the exact count, and no bookkeeping recovers the pin (each lost
     token lets an unseen writer commit a revision): `soleWriter_close` takes it as a premise.
  3. *`NewStore`* does not return `idxCert γ.idx [[], []]`; `soleWriter_of_NewStore` takes it.
  4. *The read pin* (`log' = log` for `store.Read`'s `∃ log' rev`): the read transaction holds
     no token authority and its certificate is only comparable with the caller's. `store.Read`
     must take the caller's `idxCert γ.idx log₀` and `ownToks γ.revs m` (unchanged) and return
     `histOf log₀ <+: histOf log'` and `log'.length + m + 3 ≤ 2^63` — provable if `revMuInv`
     kept a fraction of `ownTokAuth γ.revs` with the budget (`End` changes the count under
     `s.revMu` held exclusively). Until then, unit 3 can use only the write pin and the
     certificates' order.

### Unit 0c: the mvcc changes for the sole writer (2026-10-11)

Branch `txn-mvcc` (from `txn-u0b`), four commits, sorry-free, no new axiom; built with
`--packages=.lake/manifest-merge.json`. Unit 0b's "not provable" list is closed: the sole writer
pins both its transactions' logs to its own. Design and rejected options: `notes/decisions.md`,
"mvcc: the certificate carries the log, the token count is exact, a read is pinned by tokens".

1. *The certificate carries the log*: `IdxNames.log`, a monotone list of the committed log,
   half its authority in `idxWriter`, half `idxLogAuth` (under `s.revMu`); `idxCert` holds its
   lower bound. `idxCert_prefix`, `idxCert_agree_len`, `idxWriter_cert_prefix`,
   `idxLogAuth_cert_prefix`, `idxCert_nil`; `idxWriter_commit` takes and returns the other half.
2. *An empty `End` keeps its token*: `storeTxnWrite.End`'s post and `txnEndPost` add
   `if pend = [] then revToken γ else True`.
3. *`NewStore`* returns `idxCert γ.idx [[], []]`.
4. *The read pin*: the budget's authority is split in halves (`ownTokAuth_halves`), one under
   `s.revMu` with `log.length + ntok + 3 ≤ 2^63`; `store.Read` takes `ownToks γ.revs m` and
   `idxCert γ.idx log₀` and returns them with `log₀ <+: log ∧ log.length + m + 3 ≤ 2^63`
   (`m = 0`, `log₀ = []` give the old spec: the `readView` proofs). The certificate is needed
   too: the tokens bound the log read from above only.

`SoleWriter.lean`: `soleWriter_pins_write` gives `ilog = log`; `soleWriter_pins_read` (pure:
from `store.Read`'s post at the sole writer, `log' = log`) and `soleWriter_Read` (`store.Read`
at `soleWriter γ log` returns `isTxnRead mw s γ log rev ∗ soleWriter γ log`, needs
`log.length + 3 ≤ 2^63`); `soleWriter_close` is fed by `End`'s post, `soleWriter_close_end` by
`txnEndPost`; `soleWriter_of_NewStore` takes `NewStore`'s post (`ownToks ∗ idxCert`).
`Lemmas.lean` untouched. Files: mvcc's `InvIndex`, `InvStore`, `newTreeIndex`, `NewStore`,
`store__Read`, `storeTxnWrite__End`, `metricsTxnWrite__End`, `readView__{Rev,Range,FirstRev}`,
`writeView__{Put,DeleteRange}`, `storeTxnCommon__Range`, `treeIndex__{Put,Tombstone,Insert}`
(proofs, a few lines each), the specs `store__Read`, `storeTxnWrite__End`, `NewStore`,
`newTreeIndex`; `txn/SoleWriter.lean`.

### Merge of units 0, 0b and 0c (2026-10-11)

`txn-mvcc` (unit 0b and unit 0c) fast-forwarded `lean` (`e3effe933`), then `txn-u0` (unit 0)
merged into it. Conflicts only in the notes: this section's heading (one kept, the units in
order 0, 0b, 0c) and `decisions.md` (both entries kept, unit 0's plan first). Everything else
merged cleanly: unit 0c changed no `Link.lean`, link list or baseline, so mvcc's `Link.lean`,
`etc/link-lean-first-mvcc.txt`, `etc/tcb-baseline.txt` and the collections are unit 0's. No
proof needed a change: unit 0's `txnReadWrite.*`/`InvRoTxn.lean` (a read transaction, whose
`txnEndPost` case unit 0c left alone) and `Requests`/`Defs` (over `isStore`, `isLessor`,
`leaseKnown`) elaborate over unit 0c's mvcc. `gen-link.py --mvcc` and `--txn` reproduce both
`Link.lean`s (`store.Read`'s new binders do not reach the generated text). Gates (Perennial
`e4e126e46`, `--packages=.lake/manifest-merge.json`): `lake build` clean (2505 jobs);
`tcb-report.py --check --update` 69 axioms, 1 sorry, the baseline unchanged from unit 0's (13
axioms more than unit 0c's: `sort.Sort`/`Reverse`, traceutil, `proto.Size`, `zap.Int32`,
`zap.Logger.Panic`, the two txn metrics); every collection matches (txn 17/0, mvcc 13/0,
server 26/0, concurrency 12/1, recipes 11/0, cache 10/0, leasing 8/0, raft 1/0, register 1/0,
btree 0/0); `goose.py --check` up to date; `verified-code.py`: etcd 435 verified of 3599
functions (4373 of 45570 lines), txn 0 of 48 (2 assumed, 39 translated; 570 of 653 lines
translated).

### Unit 1: Put and DeleteRange (2026-10-11)

Branch `txn-u1` (main tree, off `lean` at `5e3fc3803`), sorry-free, no new axiom; built with
`--packages=.lake/manifest-merge.json` (Perennial `e4e126e46`). Every function of `put.go` and
`delete.go` is specified (`Spec/go_etcd_io/etcd/server/v3/etcdserver/txn/`) and proved, each proof
importing only its callees' specs, linked (`etc/link-lean-first-txn.txt`, `Link.lean`).

- **The specs**, one line each:
  - `mkGteRange(e)`: `[0]` becomes a slice holding `[]` and not `nil`; anything else is returned
    as it is.
  - `checkLease(lessor, p)`: `nil` with `leaseOk γl o.leaseID` (no lease, or `Lookup` found it:
    `leaseKnown`), or `lease.ErrLeaseNotFound` with the lease nonzero (`errVarIs`: the package
    variable's error).
  - `getPrevKV(trace, tw, p)`, on a transaction of either kind (`isTxn mw s γ kind`; `checkPut`
    reads at `Txn`'s read transaction): if `readsPrev o` (`IgnoreValue`, `IgnoreLease` or
    `PrevKv`), `prevKvIs r (kindState kind) o.key` (the `RangeResult`'s `KVs` hold the key's
    key-value at the state read, if any), else `nil`; the error is always `nil` (`context.TODO()`).
  - `checkAndGetPrevKV`: `getPrevKV`'s answer, with `needsPrev o → findKey` some; or
    `errors.ErrKeyNotFound` when an ignore flag finds no key-value.
  - `checkPut(trace, tw, lessor, p)`: `nil` (with `leaseOk` and the previous key-value present if
    needed), `ErrLeaseNotFound` (checked first) or `ErrKeyNotFound`.
  - `put(ctx, tw, p, prevKV)` at a write transaction `isTxnWrite mw s γ ilog pend ...` with
    `getPrevKV`'s answer at `pendState ilog pend`, the previous key-value there if needed and the
    lease written `leaseOk`: the change `putChangeOf o pv` pending, and `putResponseIs resp
    (W64 ilog.length) (if o.base.prevKV then pv else none)` (the answer's own `*KeyValue` made
    read-only).
  - `deleteRange(ctx, tw, dr)` at a write transaction: `delChanges (pendState ilog pend) o`
    pending (the range's keys deleted) and `deleteRangeResponseIs resp (W64 writeRev …)
    |rangeIn …| (if PrevKv then rangeIn … else [])`; or, with `PrevKv`, the range read's context
    error (`ctx` done), nothing changed.
  - `Put(ctx, lg, lessor, kv, p)`: pre `isKV ∗ storeReader ∗ revToken ∗ ownToks γ.revs m ∗ idxCert
    γ.idx log₀ ∗ isTxnLessor le γ.leases ∗ putRequestIs p o ∗ isContext ctx cd ∗ □ (∀ ilog,
    Pinned log₀ m ilog ∧ IgnoreLease -∗ leaseOk (the previous lease at ilog))`; post `storeReader ∗
    ownToks m ∗ trace ≠ nil ∗` either `ErrLeaseNotFound` (lease nonzero, `resp = nil`, the token
    back) or `∃ ilog, Pinned log₀ m ilog ∧ ilog ≠ []` and either `ErrKeyNotFound` (ignore flag, no
    key-value at `ilog`, token and `idxCert ilog` back) or `err = nil ∗ putResponseIs resp
    (W64 ilog.length) prev ∗ idxCert (ilog ++ [[putChangeOf o pv]]) ∗ leaseOk γ.leases (putLeaseOf
    o pv)`, `pv = findKey o.key (stateAfter ilog)`.
  - `DeleteRange(ctx, lg, kv, dr)`: the same pin, fewer than `2^63` keys at the pinned `ilog`;
    post `∃ ilog` pinned, either `err = nil ∗ deleteRangeResponseIs resp (W64 (writeRev ilog dels))
    |rangeIn (stateAfter ilog) o| prevs ∗ idxCert (commitLog ilog dels) ∗ (if dels = [] then
    revToken else True)` (`dels = delChanges (stateAfter ilog) o`), or with `PrevKv` the context
    error, `resp = nil`, the token and `idxCert ilog` back.
- **The pin, as `store.Read`'s** (decision: `decisions.md`, txn entry, "Unit 1"): `Put`'s and
  `DeleteRange`'s specs take the revision token for their transaction and, beside it, any `m`
  tokens and certificate of `log₀` (`m = 0`, `log₀ = []`: the plain token spec), and return
  `Pinned log₀ m ilog` (`log₀ <+: ilog ∧ ilog.length + m + 4 ≤ 2^63`), read inside the open
  transaction (`isTxnWrite_pinned`: `soleWriter_pins_write` for any caller). After `End` nothing
  pins `ilog` any more (the token is spent), so the sole writer's statements could not be derived
  from a spec with the token alone. At the sole writer (`m = soleBudget log - 1`) `Pinned` is
  `ilog = log` (`pinned_sole`).
- **Two premises the code needs** (stated on the specs, not findings): (1) with `IgnoreLease`, the
  lease `put` writes is the previous key-value's, which mvcc's `Put` attaches (`Attach` needs
  `leaseKnown`; Go panics on an unknown lease): `Put` takes `leaseOk` of the previous lease at the
  pinned log (the sole writer: at its own log), and returns `leaseOk` of the lease it wrote, so a
  sole writer can keep "every lease in the state is known" by itself (not proved here: mvcc has
  no invariant on the leases in its state). (2) `DeleteRange` needs fewer than `2^63` keys
  (mvcc's `DeleteRange` premise).
- **`metricsTxnWrite.Range` of either kind; a range read at `context.TODO()`** (mvcc change,
  minimal, `decisions.md`): `getPrevKV` calls `Range` on the *write* transaction, through
  `mvcc.ReadView`, at `context.TODO()`. mvcc's `metricsTxnWrite.Range` spec was for a read
  transaction and an `isContext` only, and `context.TODO()`'s `todoCtx{}` is not an `isContext`
  (its `Done()` is `nil`). Now `metricsTxnWrite.Range` is over `isTxn mw s γ kind` (as `End`; a
  write transaction's range is `storeTxnWrite.Range`'s: `ilog ++ [pend]` at `writeRev`,
  `TxnKind.readLog`/`readRev`), and `rangeKeys`, `storeTxnCommon.Range`, `storeTxnWrite.Range`
  and `metricsTxnWrite.Range` take the context as `rangeCtx todo ctx cd` (`isContext ctx cd`, or
  `ctx = todoCtxV` when `todo`) and return `todo = true → r ≠ null` (at `context.TODO()` the
  `select` on `Done()` takes its default: `wp_select_nonblocking_nil`; no context error). New
  file `mvcc/TxnRange.lean` (`rangeCtx`, `rangeDone`, `rangeCtx_Done`, `wp_todoCtx_Done`,
  `wp_select1_alt_or_nil`, `readLog`/`readRev`). The old statement is the instance `kind :=
  .read log rev`, `todo := false` (`readView.Range` and `txnReadWrite.Range` use it, their specs
  unchanged). mvcc's link list: `metricsTxnWrite__Range: storeTxnCommon__Range
  storeTxnWrite__Range`. So `Put`'s spec has no context-error case; unit 3 (`applyCompare` reads
  at `context.TODO()` too) can use the same.
- **`Write.lean`** (shared, pure and Iris): `putChangeOf`/`putValOf`/`putLeaseOf`,
  `applyChange_putChangeOf`/`stateAfter_put` (the server's put is the client's `putTxnOp`),
  `delChanges`, `delKeys_client`, `stateAfter_commit_delete` (the delete is the client's filter),
  `srvEnd_mkGte` (`mkGteRange`'s slice is `srvEnd (rangeEndOf …)`), `pendState`, `kindState`,
  `KindOk`, `isTxn_kindOk`, `isTxnWrite_facts`, `Pinned`, `isTxnWrite_pinned`, `pinned_sole`,
  `rangeAnswers_one`, `prevKvIs`, `prevKvIs_of_outcome`, `rangeOutcome_sel`, `zip_kvsIs`,
  `kvPtrIs_kvIs`/`kvPtrIs_not_null` (a range result's fresh `*KeyValue` made `kvIs`),
  `errVarIs`, `leaseOk`, `todoCd`, and `wp_slice_literal_nn` (Perennial's `wp_slice_literal`
  keeping `typedPointsto_not_null`: `[]byte{}` is not `nil`, so mvcc's `decide (end = nil)` is
  `false` for `mkGteRange("\x00")`).
- **Responses**: `putResponseIs`'s `PrevKv` is the range result's own pointer; the result is
  dropped, so its `*KeyValue` is made read-only (`kvIs`) and shared, no change to unit 0's
  predicates. The responses' fields are persisted after their last store (`wp_fupd` in
  `deleteRange`, where the stores are the last steps).
- **Results** (`Results.lean`, `#print axioms` of each, no `sorryAx`): `put_putKv` and
  `deleteRange_filter` (the specs restated; the committed states `stateAfter_put`,
  `stateAfter_commit_delete`), `put_put`, `deleteRange_deleteRange`, `put_checkPut` (for unit 3),
  `put_soleWriter` and `deleteRange_soleWriter`: derived triples with `soleWriter γ log` for the
  token: the commit is at `log`, `soleWriter γ (log ++ [[c]])` (or `soleWriter γ (commitLog log
  dels)`, or `soleWriter γ log` on an error) comes back, and the committed state is the client's
  `applyTxnOp`.
- **`gen-link.py`**: an `@` callee's result takes `[go_etcd_io.etcd.cache.v3.Assumptions]` when
  its own package's `Link.lean` gives it them (mvcc's write path reaches the index's btree); so
  do the txn results that reach one. Every mode's `Link.lean` reproduces.
- **Findings**: none in the Go code. The ignore flags' `prevKV.KVs[0]` in `put` is safe in `Put`
  (`checkAndGetPrevKV` found the key in the same write transaction); `checkLease` checks `Lease`
  even with `IgnoreLease` (the client rejects that combination; a behavior, not a bug).
- **Gates**: full `lake build --packages=.lake/manifest-merge.json` clean (2525 jobs); `gen-link.py` reproduces
  every mode's `Link.lean` (`--txn`, `--mvcc` regenerated: mvcc's adds `storeTxnWrite.wp_Range` as a
  callee of `metricsTxnWrite.wp_Range`); `tcb-report.py --check`: the baseline matches (69
  axioms, 1 sorry: no axiom added or removed); `--collection txn.txt --check --update`: 20 axioms,
  0 sorries (was 17: `proto.Marshal`, `proto.Unmarshal`, `binary.bigEndian.PutUint64`, mvcc's
  existing axioms, now reached through mvcc's write path by the package's own results); every
  other collection unchanged (mvcc 13/0, server 26/0, concurrency 12/1, recipes 11/0, cache 10/0,
  leasing 8/0, raft 1/0, register 1/0, btree 0/0); `verified-code.py --reuse`: txn 9 of 48
  functions verified (18.8%; 2 assumed, 30 translated), 110 of 653 lines (16.8%); mvcc unchanged
  (62 of 155, 661 lines); etcd 444 verified of 3599 functions (was 435), 4483 of 45570 lines (was
  4373).

### Unit 2: Range (2026-10-11)

Branch `txn-u2` (worktree `/shared/etcd-grove-txn2`, off `lean` at `5e3fc3803`), sorry-free;
Perennial `e4e126e46` (`--packages=.lake/manifest-merge.json`). Every function of `range.go`
(18) and `mkGteRange` (`delete.go`) specified (`Spec/.../txn/`) and proved (`Proof/.../txn/`),
linked (`etc/link-lean-first-txn.txt`, `Link.lean`). Decisions: `decisions.md`, the txn entry's
"Unit 2" bullet.

- **The model** (`RangeModel.lean`, pure, standard axioms only): the server's range as the code
  computes it: `rangeLimitOf` (`rangeLimit`), `fastKeysOnly`/`kvRead` (mvcc's `FastKeysOnly`
  read: no value and lease `0`), `srvPre` (the state's key-values in the range, at most the limit
  read with, as read, filtered by `kvFilterOk`; none if count-only), `srvSorted` (a permutation
  of `srvPre` sorted by `kvLeBy target`, ascending or descending, when `effSortOrder` is `1`/`2`:
  `sort.Sort` is not stable, ties in any order; `srvPre` itself otherwise), `srvTrunc`/`srvMore`
  (the first `limit`, `More`), `respKv` (keys-only drops the value), `srvRangeOk o s kvs more`,
  `srvCount` (count-only: the range's size; else `totalOf` of mvcc's limit and `withTotal`).
  The comparators `kvLtBy` (`kvLtBy_swo`: strict weak orders; `kvLtBy_false_iff`: not-less is the
  client's `kvLeBy`); `sub_neg_iff` (Go's `(a - b) < 0` is `a < b` on non-negative values: no
  overflow). **The bridge** `srvRangeOk_rangeKvsOk`: `srvRangeOk` gives the client's
  `rangeKvsOk o (rangeSel s o)` up to `leaseZ (fastKeysOnly o)`, and `More` is the client's below
  `MaxInt64`, unless `cutEarly o`. The sort's premises: `validSortTarget` (else `lg.Panic`),
  `sortOk o log` (a sorting request reads a log of at most `2^62` changes, `LogSmall`;
  `stateAt_small`: then at most `2^62` keys, revisions and versions in `[0, 2^62]`).
- **The heap** (`InvRange.lean`): `kvAt` (mvcc's owned `kvPtrIs true`; `kvPtrIs_false`: a fast
  read's is `kvAt` of `kvRead true`), `kvsAt` (a list of (pointer, key-value)), `kvsOwnAt`,
  `rangeResultIs rr rev count vs` (the `*RangeResult`, its key-values owned), `rangeResult`
  (`executeRange`/`Range`'s three outcomes: `ErrFutureRev`, a context error on a full read
  (mvcc's `rangeOutcome`, kept), or the response with `srvRangeOk` of `stateAt log (rangeRev rev
  o.base.rev)` and `srvCount`), `checkRangeErr`. `RangeLemmas.lean`: mvcc's read to the model
  (`rangeKvs_kvsAt`, `taken_stateAt`, `total_stateAt`, `srvPre_small`, `isTxnRead_pure`/`_cert`),
  `rangeResultClient`, `rangeResult_client`.
- **The specs** (one line each): `kvSort.Len` (`len(s.kvs)`); `kvSort.Swap` (the slice's `i`-th
  and `j`-th pointers exchanged); `kvSortBy{Key,Version,Create,Mod,Value}.Less` (`kvLtBy t` of the
  two owned key-values; the integer targets need `kvOk`); `IsDefaultOrdering` (`order = 0 ∨
  (target = 0 ∧ order = 1)` on the `int32`s); `HasRevisionFilters` (`hasRevFilters o`);
  `rangeLimit` (`rangeLimitOf o`); `mkGteRange` (`srvEnd (rangeEndOf sl e) = (decide (sl' = nil),
  e')`: `[]byte{0}` becomes a non-`nil` empty slice); `pruneKVs` (with an `isPrunable` closure
  deciding `P` of an owned key-value: the key-values `P` rejects, in order; the pruned ones and
  the slice's tail no longer owned); `filterRangeResults` (`filter (kvFilterOk o)`);
  `sortRangeResults` (`srvSorted o vs vs'`, premises `validSortTarget` and, when sorting, at most
  `2^62` key-values with `kvOk`); `asembleRangeResponse` (`rangeResponseIs resp rev ((srvTrunc o
  vs).map (respKv o)) (srvMore o vs) count`, the result's key-values persisted into the
  response); `checkRange` (on a read transaction: `checkRangeErr rev o err`: `nil` for revision
  `0` or in `[-1, rev]`, `ErrFutureRev` above, `ErrCompacted` below `-1`); `executeRange` (on
  `isTxnRead mw s γ log rev`, premises `validSortTarget o ∧ sortOk o log`: `rangeResult`);
  `Range` (`store.Read` with the caller's `ownToks m` and `idxCert log₀`, premise `sortOk` on
  every log the read may see: `rangeResult` at the log read, `log₀ <+: log`, `log.length + m + 3
  ≤ 2^63`, the trace non-`nil`); `Count` (the count-only `countOp`: `rangeIn` length of the state
  read, or `ErrFutureRev` and `0`). mvcc: `metricsTxnWrite.Rev`/`FirstRev` of a read
  transaction (`rev`, `-1`), additive (`etc/link-lean-first-mvcc.txt`).
- **Results** (`Results.lean`, `#print axioms`: no `sorryAx`): `range_rangeSel` (`Range` with
  `rangeResultClient`: the client's `rangeKvsOk` of `rangeSel`, premise `¬ cutEarly o`);
  `range_soleWriter` (at `soleWriter γ log`, `log.length + 3 ≤ 2^63`: the read is at `log`,
  revision `log.length - 1`, `soleWriter` returned); `count_result` (`Count` at the sole writer).
- **Where the server and the client model differ** (both in `issues/`, with Go tests):
  `etcd-range-sort-none-limit.md` (a non-key target with `SortOrder: NONE` and a positive limit:
  only the first `limit + 1` keys are sorted, a wrong result reachable with `etcdctl get
  --sort-by=VERSION --limit=1`; `cutEarly`), `etcd-range-keys-only-lease.md` (keys-only ranges
  have lease `0` unless sorted by value, since 7624a8a2e; `leaseZ`). The client's `rangeKvsOk`
  already allows any order of ties, so a non-stable sort is no difference. The comparators'
  subtraction cannot overflow on a small log (`sub_neg_iff`, `kvOk`): not a finding.
- **For the merge with unit 1**: `mkGteRange`'s spec and proof (with `wp_slice_literal_nn`) are
  here; if unit 1 has its own, keep one and adapt `executeRange`'s call (one `wp_apply`). The
  `metricsTxnWrite.Range` call in `executeRange` is in one place for unit 1's `isTxn`
  generalization. `etc/gen-link.py`: an `@` callee whose result takes the cache's assumptions
  (mvcc's `metricsTxnWrite.Range`, through the btree) now passes them on (`[go_etcd_io.etcd.
  cache.v3.Assumptions]` on `wp_executeRange`, `wp_Range`, `wp_Count`); the cache's link list
  names its `Range` `v3_Range` (the txn package's `Range` made the bare name ambiguous), its
  `Link.lean` regenerated (one import moved).
- **Gates**: `lake build` clean (2550 jobs); `gen-link.py --txn`, `--mvcc` and every other mode
  reproduce their `Link.lean`; `tcb-report.py --check`: 69 axioms, 1 sorry (baseline unchanged);
  `--collection txn.txt --check --update`: 19 axioms, 0 sorries (was 17: mvcc's
  `binary.bigEndian.PutUint64` and `proto.Unmarshal`, reached through `store.Read`/`Range`; no
  axiom added); every other collection unchanged (mvcc 13/0, server 26/0, cache 10/0, ...);
  `ETCD_SRC=/shared/etcd goose.py --check --perennial /shared/perennial-merge` up to date;
  `verified-code.py --reuse`: txn 19 of 48 functions verified (range.go 18/18, 164 lines; delete.go
  1/3), 170 of 653 lines; etcd 454 of 3599 functions, 4543 of 45570 lines (was 435, 4373).

### Merge of units 1 and 2 (2026-10-12)

`txn-u1` (unit 1, with the stray `issues/recipes-pqueue-dequeue-order.md` commit `8eb95dacb`)
fast-forwarded `lean` (`b3c219f87`), then `txn-u2` (unit 2) merged into it. Conflicts and their
resolutions:

- **`mkGteRange`** (`Spec/.../txn/mkGteRange.lean`, `Proof/.../txn/mkGteRange.lean`): both units
  specified and proved it. Unit 1's spec is kept, being the stronger: the result holds `[]` and
  is not `nil` for `[0]`, and is `rangeEnd` itself otherwise; unit 2's (`srvEnd (rangeEndOf sl e)
  = (decide (sl' = nil), e')`) follows from it by unit 1's `srvEnd_mkGte` (`Write.lean`). With
  unit 2's proof went its copy of `wp_slice_literal_nn` (it was in unit 2's `mkGteRange.lean`);
  the one left is unit 1's, in `Write.lean`.
- **`executeRange`'s proof** (the one proof changed): its `mkGteRange` call now gets the slice's
  `ownSlice_len` first (a `nil` slice holds `[]`), then `srvEnd_mkGte` for unit 2's equation,
  generalizing the result's contents to `e'` (the rest of the proof unchanged); its
  `metricsTxnWrite.Range` call is unit 1's generalized spec at `kind := .read log rev`, `todo :=
  false` (`rangeCtx false ctx cd` from `isContext`, as `readView.Range`). One unused `simp`
  argument (`hcoB`) dropped.
- **`etc/gen-link.py`**: both units added the same rule (an `@` callee whose result in its own
  package's `Link.lean` takes the cache's assumptions passes them on); unit 1's version kept (the
  `theorem` anchored at a line start), one comment for both. Every mode (`--cache`,
  `--concurrency`, `--server`, `--register`, `--leasing`, `--recipes`, `--mvcc`, `--txn`)
  reproduces its `Link.lean`; the cache's `v3_Range` rename (unit 2) merged cleanly.
- **`etc/link-lean-first-txn.txt`**: one list of mvcc's `@` callees (`store.Write`/`Read`,
  `metricsTxnWrite.Range`/`Put`/`DeleteRange`/`End`/`Rev`/`FirstRev`), then unit 1's functions
  (one `mkGteRange`), then unit 2's; txn and mvcc `Link.lean` regenerated
  (`etc/link-lean-first-mvcc.txt` merged cleanly: unit 1's `storeTxnWrite__Range` callee and unit
  2's `Rev`/`FirstRev`).
- **`Results.lean`**: unit 1's section, then unit 2's (`section unit2`, the opens of both), each
  with its `#print axioms`; unit 0's mvcc prints last. **Notes**: this section's units in order;
  `decisions.md` both bullets (unit 1's first); `issues/README.md` merged cleanly.

The issues from the txn work, now all in `issues/`: `etcd-txn-empty-requestop` (`Txn` panics on
a `RequestOp` with an empty oneof; unit 0), `etcd-range-sort-none-limit` (a sort by a non-key
target with order `NONE` and a limit is cut short by the limit; unit 2),
`etcd-range-keys-only-lease` (keys-only ranges drop the lease unless sorted by value; unit 2).

Gates (Perennial `e4e126e46`, `--packages=.lake/manifest-merge.json`): `lake build` clean (2568
jobs), no `sorry`, no new axiom; `gen-link.py` reproduces every mode; `tcb-report.py --check`:
69 axioms, 1 sorry (baseline unchanged); `--collection txn.txt --check --update`: 20 axioms, 0
sorries (unit 1's list exactly, the union of both units': unit 2's 19 and `proto.Marshal`);
every other collection unchanged (mvcc 13/0, server 26/0, concurrency 12/1, recipes 11/0, cache
10/0, leasing 8/0, raft 1/0, register 1/0, btree 0/0); `ETCD_SRC=/shared/etcd goose.py --check
--perennial /shared/perennial-merge` up to date; `verified-code.py --reuse`: txn 27 of 48
functions verified (56.2%; `range.go` 18/18, `put.go` 6/6, `delete.go` 3/3; 2 assumed, 12
translated), 274 of 653 lines (42.0%); mvcc unchanged (62 of 155, 661 lines); etcd 462 of 3599
functions, 4647 of 45570 lines (was 435, 4373 before the units).

### Unit 3: Txn (2026-10-12)

Branch `txn-u3` (worktree `/shared/etcd-grove-txn3`, off `lean` at `10cc14b29`), sorry-free;
Perennial `e4e126e46` (`--packages=.lake/manifest-merge.json`). Every function of `txn.go` (12)
and `etcdserverpb.RequestOp.GetRequestRange` specified (`Spec/.../txn/`, `Spec/go_etcd_io/etcd/
api/v3/etcdserverpb/`) and proved, linked (`etc/link-lean-first-txn.txt`, `Link.lean`; the
package's `compareInt64` is `txn_compareInt64` there, leasing has one too). Decisions:
`decisions.md`, the txn entry's "Unit 3" bullet.

- **The pure model** (`TxnRun.lean`, standard axioms only): the path `txnPath s t` (`opPath`,
  `opsPath`: the verdict of `t`, then the paths of the chosen branch's nested transactions, in
  pre-order, every comparison at the read state `s`; `txnPath_length`: one plus `nestedCount`, the
  number of nested transactions, what `newTxnResp`/`checkTxn`/`executeTxn` return; the slicing
  `path[1:]`, `path[n+1:]` keeps `x :: opsPath s (rest of the branch) ++ rest`). **The server's run**
  `srvOp`/`srvOps`/`srvRunTxn`: the client's `applyTxnOp`/`runOps` but a nested transaction's
  branch is its verdict at the read state, and the run returns the mvcc changes (a put's
  `putChangeOf`, a delete's keys; `srvOp_putTxnOp`, `srvOp_delete`) with the results; the state
  is `applyChanges` of them (`srvOp_state`). `srvRunTxn_runTxn`: the server's run is the client's
  `runTxn` when every nested verdict is stable (`OpsStable`), always without nested transactions
  (`opsStable_flat`). The premises `OpsOk weak` (below), `PathsIgnOk` (what `checkTxn` checks),
  `opsOk_strong`, `opsLeases`, `TxnPre`, `txnReadonly`/`txnSerializable` (`serializable_linearizable`:
  `txnSerializable t = !t.linearizable`, the client's).
- **The heap** (`InvTxn.lean`): `txnViewIs tw s γ kind ro` (a `*metricsTxnWrite` of either kind,
  or the read-only wrapper of a read transaction), `txnWriteIs tw s γ ro ilog pend`
  (`executeTxn`'s); the transaction responses (moved from `Requests.lean`, `responseOpIs skip`:
  a range's key-values the client's `rangeKvsOk` of the selection up to `leaseZ`, its count the
  range's; `skip`: header-only, no key-values, `More` false, count `0`), `txnRespFieldsIs`,
  `respsIs`, `txnResponseIs skip`; the skeleton `opSkel`/`opsSkel`/`respsSkel`/`txnSkel`
  (`newTxnResp`'s: each wrapper's response field `nil` and owned; a nested transaction's response
  complete but for its operations'); `leasesOk`, `leasesKnown`; `checkErrIs`. `TxnLemmas.lean`:
  the run split at an index, the requests/responses element by element, `Rev`/`Changes` of
  `executeTxn`'s transaction, `txnWriteIs_kind`, `rangeResult_txn` (a range at revision `0` at a
  context never canceled: no error, the client's selection).
- **The specs** (one line each): `compareInt64` (`int64Cmp`); `compareKV(c, ckv)` (`cmpKv cm v`);
  `applyCompare(rv, c)` on a read transaction of `log` (`cmpHolds (stateAfter log) cm`; the range
  at `context.TODO()`, no error); `applyCompares` (`cms.all (cmpHolds …)`); `compareToPath(rv, rt)`
  (a fresh slice of `txnPath (stateAfter log) t`); `GetRequestRange` (the range request of a
  range op, else `nil`); `IsTxnReadonly` (`txnReadonly t`), `IsTxnSerializable`
  (`txnSerializable t`); `checkTxn(trace, rv, rt, lessor, path)` (nil, `nestedCount`,
  `PathsIgnOk` and `leasesOk` of the path's puts' leases; or `checkErrIs` and `0`; nothing
  written); `newTxnResp(rt, path)` (`txnSkel` of the branch the path chooses, `nestedCount`; any
  `s0`); `executeTxn(ctx, lg, tw, rt, path, tresp, skip)` (on `txnWriteIs tw s γ ro ilog pend`,
  path at `stateAfter ilog`, at a context never canceled: nil, `nestedCount`, `srvOps` of the
  branch at the pending state, its changes pending, `respsIs skip`, the state's leases known);
  `txn(ctx, lg, tw, rt, isWrite, path, skip)` (`srvRunTxn` at `ilog`, the header revision
  `writeRev ilog chs`, nil); `Txn` (at the sole writer: `checkErrIs` with `resp`, `trace` `nil` and
  the sole writer unchanged; or `srvRunTxn` committed, `soleWriter γ (commitLog log chs)`, the
  response at `writeRev log chs`, `chs = []` for a read-only request, the leases known).
- **The premises of `Txn`**, in one list: `soleWriter γ log` (the apply thread); `isKV`,
  `storeReader`; `isTxnLessor lessor γ.leases`; `txnRequestIs rt t` (no empty oneof, unit 0's; a
  comparison's operand wrapper not a typed `nil`, new: `compareKV`'s `tv != nil`); the context
  an `isContext` that is never canceled (`neverDone`: its Done proposition never holds; the
  apply thread passes `context.TODO()`, whose `EnsureTrace` derivative has `nil` `Done`, see
  below); `leasesKnown γ.leases (stateAfter log)` (every lease of the state granted: an
  `IgnoreLease` put attaches the previous key's lease; `Txn` returns it for the new state);
  `TxnPre log t`: `log.length + 4 ≤ 2^63`; `OpsOk true` on the chosen branch's run: every range
  at revision `0` (the transaction's state, the client's `txnOpOf`), a valid sort target, not
  `cutEarly`, a small sorted selection (`sortSmall`, `sortRangeResults`' premise at the state
  read); every `IgnoreValue`/`IgnoreLease` put finds its key at the state it runs at unless it is
  missing at `log` (`IgnOk`; `checkTxn` fails then); fewer than `2^63` changes.
- **Changes to units 0–2's and mvcc's files**: mvcc (`TxnRange.lean`): `rangeCtx true` also takes
  an `isContext` with `neverDone` (`rangeDone` likewise; `rangeKeys`' proof: the `select`'s case
  would give `□ PDone`), `TxnKind.beginRev`/`pend`; `metricsTxnWrite.Rev` of either kind (was a
  read transaction's; `checkRange` adapted); `metricsTxnWrite.Changes` (new: the length, non-
  negative); `txnReadWrite.Range` at `rangeCtx`. `executeRange` on `txnViewIs` (either kind or the
  wrapper), at `nd` a context never canceled with no context error, premise `sortSmall` at the
  state read (was `sortOk` of the log; `Range` adapted through `sortSmall_of_sortOk`);
  `deleteRange` at `nd` with no error (`DeleteRange` passes `false`); `Requests.lean`: the
  transaction responses moved to `InvTxn.lean` (they name `leaseZ`, `RangeModel.lean`), `compareIs`
  gains the typed-`nil` conjunct; `getPrevKV`'s proof one line.
- **Results** (`Results.lean`, `#print axioms`: no `sorryAx`): `txn_srvRunTxn` (the spec),
  `txn_runTxn` (under `OpsStable`: the committed state, the verdict and the results are the
  client's `runTxn` at the sole writer's log), `txn_readonly_no_revision`,
  `txn_check_error_no_write`, `compareToPath_txnPath`, `txn_serializable_iff`
  (`IsTxnSerializable` returns `!t.linearizable`), `srvRunTxn_runTxn_flat`.
- **Findings** (both in `issues/`, with Go tests): `etcd-txn-delete-then-ignore-put.md` (a
  reachable panic: a from-key delete then an `IgnoreValue`/`IgnoreLease` put of a deleted key in
  one transaction passes `checkIntervals`, whose interval for a `"\x00"` range end is empty, and
  `checkTxn`, which checks at the read state, and `put` indexes an empty `KVs` in the apply loop);
  `etcd-txn-nested-compare-snapshot.md` (nested comparisons are evaluated before the outer
  operations run: undocumented). **This repository's client model is wrong there**:
  `applyTxnOp (.txn …)` (`cache/v3/InvEtcdTxn.lean`) evaluates a nested transaction's comparisons
  on the state the operations before it left; etcd on the state before the transaction. The
  client contracts that use nested transactions (leasing's) inherit that; not changed here
  (another package's proofs), `txn_runTxn` carries the agreement as `OpsStable`.
- **The plan's suspects**: (1) the re-read of `prevKV` in the write transaction after `checkTxn`
  checked it at the read: with a concurrent writer committing in between it could panic, but under
  the sole writer the write transaction's log is the read's (`soleWriter_pins_write`): not
  reachable, a design note; the reachable case is within one transaction (finding above). (2) the
  comparisons at an earlier snapshot: under the sole writer the snapshot is the write
  transaction's committed log, so the top-level comparisons see exactly the state the branch runs
  on; only the nested ones are early (finding above). `checkTxn`'s error case returns `0`: Go's
  `txnCount += txns + 1; txnPath = txnPath[txns+1:]` runs before the error test, so a nested
  call's count must be bounded on an error too (the spec says `0`, as Go returns).
- **The context**: `EnsureTrace`'s axiom takes an `isContext`, which `context.TODO()` (the apply
  thread's) is not; `Txn`'s spec is for an `isContext` never canceled. The apply package will need
  `EnsureTrace` of `TODO()` (a derived context whose `Done` is `nil`) or a `neverDone` descriptor
  for it.
- **Gates**: full `lake build --packages=.lake/manifest-merge.json` clean (2599 jobs), no `sorry`;
  `gen-link.py --txn` and `--mvcc` reproduce their `Link.lean` (mvcc's: `metricsTxnWrite.Changes`,
  `Rev`'s new callee; txn's: unit 3's functions, `executeRange`'s new callee);
  `tcb-report.py --check`: 69 axioms, 1 sorry (the baseline unchanged: no axiom added);
  `--collection txn.txt --check --update`: 20 axioms, 0 sorries (unchanged); every other
  collection unchanged (mvcc 13/0, server 26/0, concurrency 12/1, recipes 11/0, cache 10/0,
  leasing 8/0, raft 1/0, register 1/0, btree 0/0); `ETCD_SRC=/shared/etcd goose.py --check
  --perennial /shared/perennial-merge` up to date; `verified-code.py --reuse --package
  go.etcd.io/etcd/server/v3/etcdserver/txn`: txn 39 of 48 functions verified (81.2%: every
  function Goose translates with a body: `txn.go` 12/12, `range.go` 18/18, `put.go` 6/6,
  `delete.go` 3/3; 2 assumed, `metrics.go`), 570 of 653 lines (87.3%); mvcc 62 of 155 (661
  lines; `metricsTxnWrite.Changes`/`Rev` are promoted methods, outside the totals); etcd 474 of
  3599 functions, 4943 of 45570 lines (was 462, 4647).

### Unit 4: the history laws of the log (2026-10-12)

Branch `txn-u4` (main tree, off `lean` at `10cc14b29`). `Proof/.../etcdserver/txn/HistoryLaws.lean`
(pure Lean, standard axioms only; `#print axioms` in `Results.lean`, `section unit4`). The client's
history axioms (`etcdState_*`, `InvEtcd.lean`/`InvEtcdTxn.lean`) are stated over the abstract
`etcdState`; these theorems show that each law holds of the server's log model (`stateAt log r`,
for `r < log.length`; per prefix `stateAtPfx log r pfx`, the filter by `pfx <+: key`). They
**validate** the axioms against the server model, they do not discharge them (nothing links
`etcdState` to a log yet). Each law and what it needs:

- **`revs`** (`stateAt_revs`): positive create revision, create ≤ mod ≤ `r`, positive version.
  Needs `LogOk` (revision 0 empty, `log[0]? = some []`, for a positive create revision; the word
  bound) and **`NoDupKeysPerRev log`** (each revision's changes have distinct keys) for the
  version only. *Counterexample without it:* a revision may put one key many times (`LogOk` bounds
  only each revision's change count, below `2^63`): two revisions of `2^62` puts of `k` each give
  `k` version `2^63`, whose signed value is negative. With it, a record created at `c` and
  modified last at `m` has version at most `m - c + 1` (`KvInv`). The revision parts alone need
  only `log.length < 2^63` (`stateAt_revInv`). (Unit 2 met the same unbounded version in the
  sort's comparators: its `LogSmall`.)
- **`create_persist`** (`stateAt_create_persist`): only `log.length < 2^63`. A record whose
  create revision is not the current revision's had its key, with that create revision, before
  it (`mem_applyChanges_createRev`); a delete-and-recreate in one revision gives the new record
  that revision as its create revision, so no counterexample.
- **`modrev_persist`** (`stateAt_modrev_persist`): only `log.length < 2^63` (a record whose mod
  revision is not the revision's was there before it, `mem_applyChanges_modRev`).
- **`modrev_det`** (`stateAt_modrev_det`): only `log.length < 2^63`, **not** `NoDupKeysPerRev`:
  the expected counterexample (`[.put k v1 l, .put k v2 l']` in one revision: one mod revision,
  two records) is not one, since only the later record survives the revision; by
  `modrev_persist` both records of the law are in the state at their mod revision, which holds
  one record per key (sorted). No other counterexample found (delete-and-recreate within a
  revision: the same argument).
- **`agree`** (`stateAtPfx_agree`): `stateAtPfx` is a function. `stateAtPfx_wf`: its states are
  `EtcdStateWf` (keys strictly increasing, under the prefix). The four laws per prefix
  (`stateAtPfx_revs`, `_create_persist`, `_modrev_det`, `_modrev_persist`) follow.
- **`etcdReachedAt`** has no pure law (its only axiom is `Timeless`). The log analogue of what it
  is used for: a revision's state is fixed once the log has it (`stateAt_of_prefix`,
  `stateAtPfx_of_prefix`: a longer log has the same state at every revision of the shorter one).
- **A commit keeps the hypotheses.** `LogOk.snoc`: `LogOk (log ++ [pend])` from `LogOk log`, the
  word bounds, and `DelsPresent` (the commit's deletes are of keys present when they run:
  `LogWf`'s condition for the one revision). `NoDupKeysPerRev.snoc_iff`: kept iff the commit's
  keys are distinct; `keys_nodup_iff_check`: for a revision with `DelsPresent`, its keys are
  distinct **iff its put keys are distinct and none of them is also deleted** — etcd's
  `checkIntervals` (v3rpc, "duplicate key given in txn request": distinct put keys, no put key in
  a delete's range); two deletes of one key need a put between them, which the check excludes.
  `NoDupKeysPerRev.snoc` packages it; `sel_keys_nodup`: a range delete's keys (`delKeys_eq`'s
  `(srvSel s …).map key`) are distinct. Unit 3 instantiates it with `runOps`' changes (a put
  `.put k v l`, a delete `(delKeys …).map .del`): its premise is the client's transaction passing
  that check (the check is in the gRPC layer, not in the apply path the proof covers).

**What the client axioms assume of the server**, beyond `LogOk`: `NoDupKeysPerRev` (a revision
writes a key at most once), for `etcdState_revs`'s positive version only.

Gates: `lake build --packages=.lake/manifest-merge.json` of `HistoryLaws` and `Results` clean, no
`sorry`, `#print axioms` standard only (`propext`, `Classical.choice`, `Quot.sound`). The
`tcb-report.py --collection txn.txt --check` not run (`.lake/tcb.json` not current; the merge runs
it); no new axiom.

### Merge 3/4 (2026-10-12)

`txn-u3` (unit 3, six commits) merged into `lean` (`e099df5ea`), then `txn-u4` (unit 4)
(`2175453f0`). Conflicts in the notes only (this section's "Unit 3" and "Unit 4" subsections,
`decisions.md`'s two bullets, both kept in unit order); `Results.lean` merged cleanly (unit 3's
section, then unit 4's `section unit4` and its `public import ...txn.HistoryLaws`). Unit 3's
changes (the responses moved to `InvTxn.lean`, `executeRange`/`deleteRange` generalized, mvcc's
`TxnRange.lean`) touch nothing `HistoryLaws.lean` uses (`Lemmas.lean` and mvcc's model): no
proof changed.

Gates (Perennial `e4e126e46`, `--packages=.lake/manifest-merge.json`): `lake build` clean (2600
jobs), no `sorry` of this repository's, `HistoryLaws`' results on the standard axioms only;
`gen-link.py --txn` and `--mvcc` reproduce their `Link.lean`; `ETCD_SRC=/shared/etcd goose.py
--check --perennial /shared/perennial-merge` up to date; `tcb-report.py --check`: 69 axioms, 1
sorry (baseline unchanged); every collection unchanged (txn 20/0, mvcc 13/0, server 26/0,
concurrency 12/1, recipes 11/0, cache 10/0, leasing 8/0, raft 1/0, register 1/0, btree 0/0);
`verified-code.py --reuse`: txn 39 of 48 functions verified (81.2%), 570 of 653 lines (87.3%);
etcd 474 of 3599 functions (13.2%), 4943 of 45570 lines (10.8%), as after unit 3 (unit 4 is pure).

### The whole package (2026-10-12)

**Verified**: every function of `txn.go`, `put.go`, `range.go` and `delete.go` that Goose
translates with a body (39: `txn.go` 12, `range.go` 18, `put.go` 6, `delete.go` 3), and
`etcdserverpb.RequestOp.GetRequestRange`, sorry-free; `metrics.go`'s two observers are assumed,
`util.go` names-only. mvcc gained the read-only write transaction (`txnReadWrite`,
`NewReadOnlyTxnWrite`) and `metricsTxnWrite.Rev`/`FirstRev`/`Changes`.

**Exported results** (`Results.lean`, each with `#print axioms`): unit 1 `put_putKv`,
`deleteRange_filter`, `put_put`, `deleteRange_deleteRange`, `put_checkPut`, `put_soleWriter`,
`deleteRange_soleWriter`; unit 2 `range_rangeSel`, `range_soleWriter`, `count_result`,
`srvRangeOk_rangeKvsOk`; unit 3 `txn_srvRunTxn`, `txn_runTxn`, `txn_readonly_no_revision`,
`txn_check_error_no_write`, `compareToPath_txnPath`, `txn_serializable_iff`,
`srvRunTxn_runTxn_flat`; unit 4 (pure) `stateAt_revs`, `stateAt_create_persist`,
`stateAt_modrev_persist`, `stateAt_modrev_det`, `stateAtPfx_agree` and the `stateAtPfx_*`
versions, `stateAt_of_prefix`, `LogOk.snoc`, `NoDupKeysPerRev.snoc`(`_iff`),
`keys_nodup_iff_check`, `sel_keys_nodup`; unit 0 mvcc's `txnReadWrite.wp_*`.

**The premises of the results**, in one list: the sole writer (`soleWriter γ log`: every
revision token is the apply thread's); the context `context.TODO()` or an `isContext` that is
never done (`neverDone`); no compaction (mvcc's `isStore` fixes `compactMainRev = -1`); leases as
the lessor's `Lookup` says (`isTxnLessor`), and for `Txn` every lease of the state known
(`leasesKnown`); `LogOk` (the log well formed, its length and every revision's change count below
`2^63`); for a range a valid sort target (`validSortTarget`), a small sorted selection
(`sortSmall`; `LogSmall` of the log for `Range`), well-formed key-values (`kvOk`), not
`cutEarly`; a `DeleteRange` of fewer than `2^63` keys; `NoDupKeysPerRev` (a revision writes a key
at most once), which a commit keeps exactly when the transaction passes etcd's `checkIntervals`;
`DelsPresent` (a commit's deletes name present keys, for `LogOk.snoc`); `OpsStable` for `txn_runTxn` with nested transactions
(every nested verdict the same before and after the operations preceding it); `TxnPre` (the
log's room for the commit, `OpsOk` of the chosen branch: ranges at revision `0`, ignore-flag
puts whose key exists where they run).

**Open ends**: the client model's `applyTxnOp (.txn …)` (`cache/v3/InvEtcdTxn.lean`) is wrong for
nested transactions (it evaluates a nested comparison after the operations before it; etcd
before the transaction), kept because leasing's proofs use it (`txn_runTxn` carries the
agreement as `OpsStable`); traceutil's `EnsureTrace` axiom needs an `isContext`, so `Txn` is not
stated at the literal `context.TODO()` (the apply package needs `EnsureTrace` of `TODO()` or a
`neverDone` descriptor for it); the server's `Link.lean` and mvcc's both define
`binary.bigEndian.wp_PutUint64`, a clash once the apply package links both; mvcc's
`traceutil.Trace.Step` axiom claims a return on a `nil` trace (Go dereferences it), harmless while
every trace passed is non-nil.

**Issues found** (`issues/`, all in `issues/README.md`): `etcd-txn-empty-requestop` (`Txn`
panics on a `RequestOp` with an empty oneof; unit 0), `etcd-range-sort-none-limit` (a sort by a
non-key target with order `NONE` and a limit is cut by the limit; unit 2),
`etcd-range-keys-only-lease` (keys-only ranges drop the lease unless sorted by value; unit 2),
`etcd-txn-delete-then-ignore-put` (a from-key delete then an ignore-flag put of a deleted key
panics in the apply loop; unit 3), `etcd-txn-nested-compare-snapshot` (nested comparisons see the
state before the transaction, undocumented; unit 3).

**Fix branches (2026-10-12).** Three of them are bugs with fix branches on the fork, one
signed-off commit each off upstream `main` (f061acd09), with tests, and their drafts rewritten
for etcd-io/etcd: `txn-delete-then-ignore-put` (d9ba0e03c: `checkIntervals` reads a `"\x00"`
range end as the affine infinity, as `mkGteRange` does, so the transaction is rejected as a
duplicate key; restart runs with the real binaries show the crash is permanent: the entry is in
every member's WAL beyond the stored consistent index and replays on every restart, with a fixed
binary too, so one write-permitted request takes the whole cluster down for good),
`range-sort-none-limit` (7362d4129: a `rangeSortOrder` shared by `rangeLimit` and
`sortRangeResults`, so the limit is dropped exactly when the results are re-sorted;
`IsDefaultOrdering` unchanged, since `RangeStream` relies on it) and `range-keys-only-lease`
(01e522548: the server no longer requests mvcc's index-only read, since the lessor's item map
holds a key's lease now, not at the revision read; this reverts the speedup of upstream PR
#21791, which upstream may prefer to keep by documenting the omission instead). Found while
fixing the sort cut: `etcd-rangestream-sort-none` (`RangeStream` with a non-key sort target and
order `NONE` returns duplicated and missing keys; outside the verified code, no fix branch).

## Merge: mvcc into lean (2026-10-11)

Branch `mvcc` (25 commits: the KV core's translation, model, key index, tree index, read and
write transactions, `NewStore`) merged with `origin/lean` (`672501acc`: the recipes package,
the register's cluster driver, Perennial `e4e126e46`), in the `mvcc` worktree, then fast-forwarded
onto `lean`.
- **Conflicts**: five files, all bookkeeping: the Perennial pin (`lakefile.toml`,
  `lake-manifest.json`: `lean`'s `e4e126e46` contains mvcc's `bf935cbd5`, so it wins),
  `etc/gen-link.py` (both sides' modes kept: `--mvcc`, `--recipes`, `--register`,
  `--skip-unproved`; the `[StorageModel GF]` and the cache-assumptions binders both emitted),
  the two notes (both sides' sections kept; the pin history spliced).
- **One `AllG`** (Perennial `cb6a5921e`, in `lean`'s pin; see "Perennial `cb6a5921e`: one
  `AllG`"): the `[AllG GF]` section variable next to `[hG : HeapGS …]` dropped from the 88
  files mvcc had added with it (a `sed`), and from `muInv`'s binders (`InvStore.lean`);
  `Link.lean` regenerated (its results no longer take `[AllG GF]`). No proof changed.
- **The etcd pin** moved on `lean` from `0fc6f23b1` to `bc8b52a50` (one commit, names only in
  the recipes package): the packages mvcc translates are identical, `etc/goose.py --check`
  passes at the merged pins with no regeneration.
- **Two fixes the one-`AllG` bump needed** (as on `lean`, "Perennial `cb6a5921e`: one `AllG`"):
  `leaseKnown_persistent` and `isLessor_persistent` state their predicate with `(GF := GF)` (the
  `[AllG GF]` local instance used to fix `GF`; `HeapGS ?hlc ?GF` is not tried), and
  `mkOk_loc_inj` (`InvStore.lean`), whose statement mentions no `GF`, gets its own binders
  (`[FfiSyntax] [GoLocalContext] [GoGlobalContext] [go.Semantics]`) outside the section: as a
  section theorem its `HeapGS`/`Assumptions` binders were undetermined at every use.
- **Checked** (after a full build, 2450 jobs): `etc/goose.py --check` at the merged pins;
  `etc/tcb-report.py --check` matches (56 axioms, 1 sorry: the two sides' lists merged
  textually, disjoint); every collection matches (btree 0, cache 10, concurrency 12 and the
  sorry, leasing 8, mvcc 13, raft 1, recipes 11, register 1, server 26 axioms);
  `etc/verified-code.py`: etcd 431 of 3599 functions verified, 4367 of 45570 lines (mvcc 58 of
  155, 655 of 2073).

## mvcc: the KV core, phase one (2026-10-10)

Started the verification of etcd's `server/v3/storage/mvcc` KV core (`notes/decisions.md`,
"mvcc: the log of changes as the model"), on branch `mvcc` (worktree `/shared/etcd-grove-mvcc`;
another session was committing `client/v3/leasing` to the main checkout at the time).

- **Translation**: the KV core with bodies (`Code/go_etcd_io/etcd/server/v3/storage/mvcc.toml`:
  `revision.go`, `key_index.go`, `index.go`, `kv.go`, `kv_view.go`, `kvstore_txn.go`,
  `metrics_txn.go`, the promoted methods of embedded fields), `pkg/v3/schedule` and prometheus's
  `client_golang/prometheus` names-only (`etc/goose.py`). It needs Goose's range over an
  integer and `float64(n)` of an integer as an uninterpreted function, written in
  `/shared/perennial-mvcc` on Perennial `7c93f27aa`, rebased on upstream's `7cea8cc26` (the
  panic branch) when it landed, pushed as `114b847ff` and `bf935cbd5` (2026-10-10 evening) and
  pinned here as `bf935cbd5`; `lean` (panics and `recover`, `client/v3/leasing`) merged at the
  same time, so `etc/goose.py --check` passes with the pinned translator (the etcd pin
  `0fc6f23b1` is upstream's `goose-lean`).
- **Model** (`Proof/go_etcd_io/etcd/server/v3/storage/mvcc/Model.lean`): the log of changes,
  `stateAt` through the client model's `putKv`, the key index `indexOf (evsOf log)` with
  `kiPut`/`kiTombstone`/`kiGet`/`kiFindGen`/`genWalk` mirroring the code, the key bucket
  `bucketOf log` with the opaque `kvEncode`, `revBytes`, `LogWf`; the pure lemmas the proofs use.
- **Proved** (specs in `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/`, proofs beside the shared
  `Base`/`Model`/`Defs`; `Link.lean` by `etc/gen-link.py --mvcc` from
  `etc/link-lean-first-mvcc.txt`; `Results.lean` prints the axioms; collection
  `etc/tcb-collections/mvcc.txt`): `Revision.GreaterThan`, `generation.isEmpty`,
  `generation.walk`, `keyIndex.Less`, `keyIndex.isEmpty`, `keyIndex.findGeneration`,
  `keyIndex.get`, `keyIndex.put`, `keyIndex.tombstone`: 9 of the core's 72 functions, all
  sorry-free, resting on no axiom of this repository (the error and metrics variables are
  package facts, `Base.lean`).
- **The model's main theorem** (`LogLemmas.lean`, `kiGet_indexOf`, sorry-free, standard axioms
  only): for a well-formed log (`LogWf`, length and every revision's change count below 2^63),
  what the index built from the log's events answers of a key at a revision (`idxGet` then
  `kiGet`) matches the key-value of the state at that revision (`KvMatch`): both absent, or the
  key-value's mod revision, create revision and version are the answer's, and the bucket holds
  the key-value at the answer's revision (`BucketHas`: `changeKv` of that change). Proved
  key by key (`kiOfKey`, the key's events folded; `indexOf_rep` links it to the btree-model
  index), by induction over the log's revisions and, within one, over its changes
  (`rev_step`), with `Lemmas.lean` (what `kiGet` answers after `kiPut`/`kiTombstone`, below
  and at or above the new revision, under `KiWf`/`KiAbove`; `kiGet_top`).
- **`index.go`, the point operations** (2026-10-10, branch `mvcc`): the btree's
  `ownBTree_combine` (`btree/Combine.lean`, keys determined by items) and the cache wrapper's, so
  a tree can be a `RWMutex` resource; `Hist.lean` (the index's history with commit markers,
  `kiGet_reader`, the writer's facts, finding/inserting entries by key, `kiLastEmpty_false_of_del`);
  `InvIndex.lean` (`ownTree`, fractional; `idxLockInv`, `isTreeIndex`, `idxReader`, `idxWriter`,
  `idxCert`, `idxWriter_commit`, `reader_answer`). **Proved and linked** (sorry-free):
  `newTreeIndex`, `treeIndex.keyIndex`, `unsafeGet`, `Get` (a reader with the certificate of a
  committed log reads what it determines), `Put` and `Tombstone` (the writer, for the pending
  revision's next change). The specs of `Get`/`Put`/`Tombstone` are stated at
  `HeapGS HasLC.hasLC` (later credits) with the cache's btree interface assumptions
  (`etc/gen-link.py` adds `[go_etcd_io.etcd.cache.v3.Assumptions]` when a spec has it).
  **`KeyIndex` and `Insert`** (2026-10-11, the last of `index.go`; `restore` and the tests are
  their only callers, on a private index): under the live index's invariant, the history fixes
  the tree's keys and their indexes, so `KeyIndex` (a reader with `idxKnows`) returns the key's
  pointer (`kiKey`, persistent) or `nil`, present whenever the reader's log gives the key an
  index (`kiOfKey … ≠ kiEmpty`), and exactly then for the writer's knowledge; `Insert` (the
  writer, an owned key index holding the key's `kiOfKey`, not empty) always *replaces* the key's
  entry and returns the old one, owned: inserting a new key is not a step of the live index
  (decisions.md, "`KeyIndex` and `Insert` under the history"). Lemmas:
  `idxGet_indexOf_eq_none_iff` (a key has an entry iff its `kiOfKey` is not `kiEmpty`),
  `ownTree_entry` (an entry's pointer is not `nil` and carries its key), `idxKnows_writer_events`.
- **`index.go`, the range reads** (2026-10-10, branch `mvcc`): `unsafeVisit` (the entries in
  `[key, end)` in key order, `rangeEntries`, through the btree's `AscendGreaterOrEqual` model
  spec and a visitor triple `visitSpec`, the visited entries lent to the caller's closure by
  index), `Revisions`, `CountRevisions`, `Range`: a reader with the certificate of a committed
  `log` and `atRev` below its length gets the keys of the range with a revision at `atRev` in
  `log`, in key order (`rangeAnswers`; the one key if `end == nil`), at most `limit` of them if
  positive (`rangeTaken`), and the count (`rangeTotal`: all of them if `withTotalCount`, else at
  most `limit`); `Range`'s `keys` are the key indexes' own key slices, read-only (`ownKeys`).
  The model: `rangeAt` (the index's answers in a range), `reader_range` (a reader's range
  answer is its certified log's: the certified keys stay, `kiOfKey_ne_mono`, sorted subsets
  are sublists, the later keys answer nothing below the certified length), the visiting
  (`fromKey`, `belowEnd`, `filter` as `takeWhile` on sorted entries) and the visitors'
  accumulation (`entryAnswers` of a prefix, `takeLimit`/`totalOf`/`reached` and the limit's
  arithmetic), in `Hist.lean`; the proofs share `ReadLemmas.lean` (`kiGetVal_pairs`,
  `entries_not_empty`, and the two Boolean conditions of the visitors as triples on the Goose
  expressions, `wp_reachedLimit`, `wp_stopCond`, so each visitor has one continuation per
  outcome). All four sorry-free and linked; `Results.lean` prints 20 results and the two model
  theorems; the collection's baseline is still empty (no axiom, no sorry).
- **`revision.go`, the encoding** (2026-10-10 evening, branch `mvcc`): the eight functions
  proved (`RevBytes.lean`, shared: the model's `revBytes r tomb` split as the encoder leaves it,
  `bucketKeyBytes`, `isTomb`, the list lemmas of each step). `newBucketKey`, `NewRevBytes` (17
  zero bytes, capacity 18), `isTombstone`/`IsTombstone` (`isTomb`: 18 bytes, the last `'t'`),
  `BucketKeyToBytes` (into a buffer of 17 or 18 bytes with its capacity: the 17 bytes of the
  revision, then for a tombstone the mark appended or written over the 18th; a non-tombstone
  keeps the 18th), `RevToBytes` (the same, no mark), `BytesToBucketKey`/`BytesToRev` (the 17
  bytes of a nonnegative revision and at most one byte after them, as the model's `revBytes`
  values are; a tombstone iff that byte is the mark; any other input panics, outside the spec).
  The callees are encoding/binary's `BigEndian.PutUint64`/`Uint64`, the server's trust-boundary
  axioms (`Spec/encoding/binary/`, `u64Be` of `InvCindex.lean`), now also in the mvcc list:
  the encoders and decoders rest on those two axioms, the rest of mvcc on none. Proof notes:
  a slice expression `b[i:j]` evaluates to `slice.slice b V i j` behind a bounds `if`
  (`simp only [Hb, _root_.and_self, ite_true]`), the parts come from `ownSlice_slice ... .1`
  and go back by `ownSlice_combine` and `ownSlice_trivial_slice` (as the register's
  `encode`); `wp_if_destruct` wants a `decide` or a Boolean variable, a field such as
  `bk.tombstone'` needs `cases h : bk.tombstone'`; a closed `decide` of a word equality
  reduces by `simp (config := { decide := true }) only [hl]` after `hl : s.len = W64 17`.
- **The read transactions, opened and closed** (2026-10-11, branch `mvcc`): `InvStore.lean`
  (design: decisions.md, "The transactions: the store's locks and the backend contract"): the
  backend's contract for the `Key` bucket (`keyReadSnap rt m`: a `ReadTx` over a snapshot `m`,
  `UnsafeRange(Key, k, nil, 0)` reads `m`'s entry; `isKeyBackend b View`:
  `ConcurrentReadTx()`/`ReadTx()` return a snapshot of the caller's `View q m`), the locks
  (`s.mu` holds nothing, `muInv`; `s.revMu` holds `currentRev = log.length - 1`,
  `compactMainRev = -1`, `idxCert γ.idx log` and the bucket's ghost-map authority
  `bucketView γ q (bucketMap log)`, `revMuInv`), `isStore` (persistent: backend, index as the
  `index` interface over `isTreeIndex`, logger, the two guards), `storeReader` (a reader slot
  of each lock and the index's), `storeTxnReadIs` (the `storeTxnRead`'s fields, read-only) and
  `isTxnRead mw s γ log rev` (the `metricsTxnWrite` wrapper, owned, around `txnReadWrite`
  around the `storeTxnRead`, with `s.mu` held shared). Proved: `store.Read` (under `s.revMu`
  shared: the snapshot of the committed log's bucket, `rev` its last revision; both modes),
  `storeTxnRead.End` (the tokens back), `storeTxnCommon.FirstRev`/`Rev` (the fields; the
  promoted calls load through `txCommon tr`), `newMetricsTxnRead`. Trust-boundary axioms (not
  yet linked): `traceutil.Trace.Step` returns; `proto.Unmarshal` of `kvEncode kv` into a
  `*mvccpb.KeyValue` sets its fields to `kv`'s and returns `nil`. Proof notes: a nested
  struct's points-to cannot be made persistent as a whole (`ipersist` wants a `DFractional`
  points-to: split it with `iStructNamedPrefix` and persist the fields), and only while the
  goal is a `WP` (a basic update needs a modality to eliminate into); an Iris hypothesis with
  `∀`s is instantiated by `ihave H' := H $$ %x %y` before `wp_apply H'`; a persistent
  predicate about to be destructed is kept with `ihave #H0 : P $$ []` then `· iexact H`; an
  abbreviation of an address (`structFieldRef`) must live in a section with
  `[GoSemanticsFunctions]` (as `idxMuAddr`), else its uses leave the lock lemmas' instances
  undetermined; a lock resource with no content takes the semantics' instances explicitly.
- **The read transaction's range** (2026-10-11, branch `mvcc`): `storeTxnCommon.rangeKeys` and
  `Range` proved and linked. The spec (`rangeOutcome`, `InvStore.lean`): with the store, the
  transaction's read-only fields (`storeTxnReadIs`: the snapshot `m ⊇ bucketMap log`, the
  certificate, `rev = log.length - 1`), a reader slot of the index, a context and the two key
  slices, a range at `ro.Rev` (`rangeRev`: `rev` if at most 0) returns either the future-revision
  error (`rev < ro.Rev`: `ErrFutureRev`, a result with `Count = -1`), or, for a full read, `nil`
  and an error once the context is done (the `select` on `ctx.Done()` in the loop), or `nil`
  error and the result: `CountOnly` the count of `rangeAnswers`, else `Rev = rev`,
  `Count = rangeTotal` and `KVs` the `rangeTaken` answers in key order (`rangeKvs`: each
  `*mvccpb.KeyValue` is the key-value `findKey` gives in `stateAt log` at that revision, with
  `kvPtrIs`: a fast-keys-only read fills the key, create/mod revision and version, a full read
  also the value and lease, read from the bucket). The model lemma `rangeAnswers_kv`
  (`BucketLemmas.lean`): every answer of `rangeAnswers` at a revision of a well-formed log has
  its key-value in `stateAt`, with the answer's revisions and version, and the bucket maps the
  answer's revision's bytes to its encoding (from `kiGet_indexOf`'s `KvMatch` and `BucketHas`;
  the bucket's functionality from `revBytes_inj`). Callees: `treeIndex.CountRevisions`/`Range`/
  `Revisions`, `sliceCapWithLimit` (proved, `capWithLimit`), `NewRevBytes`, `RevToBytes`, the
  backend's `UnsafeRange` by the contract `keyRangeSpec` in `storeTxnReadIs`, and the two
  trust-boundary axioms now linked: `traceutil.Trace.Step` and `proto.Unmarshal` (the mvcc
  collection's baseline has them with the two BigEndian axioms). Proof notes: the Go `range`
  over an integer and over the slice are `wp_for` loops whose invariant names every conjunct
  (an unnamed invariant lets `wp_if_destruct` pick a `decide` inside the postcondition); the
  non-blocking `select` is `chan.wp_select_nonblocking_alt` with
  `context.isContextDone_nonblocking_receive` (as `Election.Campaign`), the loop's resources
  passed through its `P`; the fixed hypotheses are framed by name after `wp_for_post` (a bare
  `iframe` instantiates the invariant's existential wrongly); `hif` from `wp_if_destruct` is
  sometimes `#(decide c) = #true`, sometimes `c` (`first | exact Hif | …`); the long proof needs
  `set_option maxHeartbeats 4000000 in`.
- **The wrappers** (2026-10-11, branch `mvcc`): `metricsTxnWrite.Range` (counts, forwards:
  `isTxnRead` kept, `rangeOutcome`) and `End` (the counters and the gauge of `metrics.go` by
  the package facts `counterSpec`/`gaugeSpec`, then the deferred `storeTxnRead.End`: the
  reader's tokens back, `storeReader`); `readView.FirstRev`/`Rev`/`Range` (`isReadView rv s γ`:
  the view's `kv` is the store; a transaction opened by `store.Read` around the read and
  closed by the deferred `metricsTxnWrite.End`; `Rev` and `Range` return with the certificate
  `idxCert γ.idx log` of the log they read, `rev = log.length - 1`). `traceutil.TODO` is a new
  trust-boundary axiom (returns a trace). The promoted methods (`txnReadWrite`'s from its
  `TxnRead`, `storeTxnRead`'s from `storeTxnCommon`, `metricsTxnWrite`'s from its `TxnWrite`)
  are `MethodUnfold` lambdas in the translation, not functions: the proofs unfold them in
  place, `rw [method_unfold (t := go.GoType.PointerType T.ty) (m := go!"M")]; wp_call`, naming
  the type and method because a bare `wp_method_call` rewrites the first `methods` term it
  finds, which may be the one stored in the `defer` cell or a counter's in a hypothesis.
- **The write transactions** (2026-10-11, branch `mvcc`; the design: decisions.md, "The write
  transactions: the batch lock's resources, the backend's write path, the lessor"). Specified
  at the checkpoint `628f69632` (`InvStore.lean`: `batchTxSpec`/`isBatchTx` and `BatchTx()` in
  `isKeyBackend`, `isLessor`/`leaseKnown`, `writerRes` under the batch lock, `revToken` and the
  budget `ownTokAuth γ.revs`, `revMuInv` with halves of `currentRev` and `γ.clog`,
  `storeTxnWriteIs`/`isTxnWrite`, `changesAre`, `TxnKind`/`isTxn`/`txnEndPost`, `commitLog`,
  `isWriteView`; `InvIndex.lean`: `IdxKnow`/`idxKnows` for the index readers, `idxKnows_facts`,
  `idxWriter_wf`; `BucketLemmas.lean`: `writeRev`, `delKeys`, `pendPuts`, `bucketMap_append`,
  `changeKv_put`, `LogWf'.append_change`, ...), then proved and linked: `store.Write` (a token
  for the batch lock's resources), `storeTxnWrite.put` (the index read by the writer, the
  bucket's `UnsafeSeqPut`, the index's `Put`, the `changes` append, the lease detached and
  attached), `Put`, `delete`, `deleteRange` (the keys at `writeRev`, each deleted in a loop),
  `DeleteRange`, `End` (the commit under `s.revMu`: both halves of `currentRev`, the ghost
  log, the index writer's commit, the token back, the batch `Unlock`'s write-back), `Rev`,
  `Changes`; `metricsTxnWrite.Put`/`DeleteRange`/`End` (over `TxnKind`), `writeView.Put`/
  `DeleteRange`; `readView.*` and `treeIndex.Get`/`Range` reproved for the changed specs. Three
  new trust-boundary axioms: `proto.Marshal` (the converse of `Unmarshal`), `zap.Error`,
  `zap.Logger.Error`; the mvcc collection's baseline updated. `changesAre_snoc` (`InvStore.lean`)
  is the shared lemma of `put` and `delete`. Proof notes: a spec held as an Iris hypothesis with
  `∀`s is applied as `wp_apply H $$ %x %y [$H1 $H2]` (the `%_` left to unification by the framed
  hypotheses; an argument nothing determines, `GetLease`'s item, given explicitly); an `if
  err != nil` after a call whose spec returns `nil` is resolved by `wp_auto` (no
  `wp_if_destruct`), an unknown error is `cases err with | nil => … | ok e => …`; a `&T{...}`
  literal is allocated by `wp_auto` (`«$r0_ptr»`, no `wp_alloc`), and the key-value a spec
  takes for it is a literal record with the Goose literal's fields (`createRev := 0`, not
  `W64 0`, not `zeroKv k`: the frame does not unfold a definition or convert the literals); a
  record literal continued on a second line must not contain a type ascription `(x : Int)` (it
  does not parse: `W64 ilog.length`); a predicate packaged before the code's last reads of the
  struct (`tw.s` for the lessor) is built as a wand over the struct's points-to and applied at
  each return (`iapply HΦ; iapply Hpack; iexact Htw`); `rw … at H` on an Iris hypothesis is
  `rw` on the goal (the context is part of it); two halves of a points-to join by
  `((typedPointsto_dfractional _ _).dfractional _ _).2` and split by `.1` after `own_half_half`
  rewrites `DFrac.own 1` (an `icombine … as` leaves a plain conjunction); `icombine … gives`
  of the token authority and a token needs `revToken` unfolded; `isStore`'s `ti` shadows the
  transaction's after `iNamedSuffix` (`icombine Hidx HidxS gives %h; mkOk_loc_inj; subst`); a
  range loop's index is `i_ptr`/`i`, its loop variable's cell is in the invariant (the body
  stores it), and after `wp_for_post` the goal is the fixed resources then the invariant:
  `iframe` the fixed ones by name, then `iexists`; `word` failed with "unknown free variable"
  on `0 ≤ sint.Z (W64 n) ∧ sint.Z (W64 n) < (l ++ [x]).length` (an `sint.Z (W64 n) = n` step
  by `BitVec.toInt_ofInt_eq_self`, then `omega`); `trace_state`'s output in a `lake env lean`
  log has no header (it reads as a second goal of the preceding error).
- **The writer's range read** (2026-10-11, branch `mvcc`; design: decisions.md, "The writer's
  range read"): `storeTxnWrite.Range` proved and linked (an Opus subagent's work). The bucket view
  is split (`revMuInv` half, `writerRes`/`storeTxnWriteIs` half, `bucketView_halves`; `End`
  joins them), `batchTxSpec` reads under the lock (`UnsafeRange` sees the pending puts) and its
  `Unlock` with puts takes a wand building `W` from the written-back view; `rangeKeys`'s spec
  is over the `storeTxnCommon` fields at a fraction, `keyReader rt m R` (`keyReadSnap_reader`,
  `batchTx_reader`), `idxKnows` and `0 ≤ rev < log.length`; `treeIndex.Revisions`/
  `CountRevisions` take `idxKnows` as `Get`/`Range` do; `txCommonW`, `idxKnows_wf`,
  `writeRev_commitLog`. The result: `rangeOutcome` at `ilog ++ [pend]` and `writeRev ilog pend`.
  No new axiom (the mvcc collection: 8 axioms, 0 sorries). Proof notes: the whole-struct
  points-to of `storeTxnWriteIs` is split with `iStructNamedPrefix` for the promoted
  `rangeKeys` and joined back with `typedPointsto_combine`.
- **The store's constructor** (2026-10-11, branch `mvcc`): `NewStore` translated (`kvstore.go`;
  `restore` and everything else it calls untranslated) and proved and linked, on a fresh backend.
  The spec: the caller gives the empty bucket view `ghostMapAuth γb 1 ∅` (the fresh-backend
  assumption), the backend's contract for every store location and names with that bucket name
  (`writerRes s γ` is the store's choice), and the lessor at its own ghost name `γl`; it returns
  `isStore s γ` at the initial log `[[], []]` (`currentRev = 1`), the two views, every reader slot
  (`storeReader`) and `2 ^ 63 - 5` revision tokens. A `nil` logger is replaced by `zap.NewNop()`'s;
  `cfg` is not modelled. Contract changes (`InvStore.lean`): `batchTxSpec` gains
  `LockOutsideApply()` (`Locked []`, **no** resource: the batch lock holds `writerRes` from
  `NewStore`'s first `Unlock`, the no-puts triple, on) and `UnsafeCreateBucket(b)` (keeps the
  puts); `isKeyBackend` gains `ForceCommit()`; `isLessor le γl` is over the lessor's own `GName`
  (`leaseKnown γl id`, the specs of `put`/`Put` take `leaseKnown γ.leases`) and gains
  `SetRangeDeleter(f)` (the closure over `store.Write` is opaque; the lessor's later calls of it
  are outside the model); `revMuInv` is `Fractional` (for `sync.init_RWMutex`);
  `idxWriter_commit` no longer needs `ilog ≠ []` (the first two commits). `mvccInit` gains the two
  configuration defaults `NewStore` reads (package variables, any values). Five new axioms:
  `zap.NewNop` (non-nil), `schedule.NewFIFOScheduler`, `NewHashStorage`,
  `schema.UnsafeCreateMetaBucket` and `store.restore` on a fresh backend (the identity on the
  verified state; its store of `1` into `currentRev` is modelled as no write, since `NewStore`
  holds only half of `currentRev` then: the other half is the batch lock's; in the code that
  write is protected by `s.mu` held exclusively, which `muInv = True` does not express). Proof
  notes: `wp_join` for the `lg == nil` and `cfg` defaults (the cases join at the logger's and the
  config's points-to); `wp_apply` of the batch transaction's triples (its token `Locked` a
  variable from an existential) failed with "unknown free variable" here (not in `store.Write`):
  `wp_bind (App (Val #(methods bt.ty _ bt.v)) (Val #()))` then `iapply` (cause not found); the
  store's names are an `obtain`ed variable with equations, rewritten into the context
  (`rw [← hγi, …]`), not a `let`.
- **`key_index.go`'s panics** (2026-10-11): `zap.Logger.Panic` is an axiom panicking with its
  message (`RET r; ⌜r = PanicV #msg⌝`, Perennial's panic outcome; a nop logger panics too:
  `Panic`/`Fatal` entries are always written) and `zap.Logger.Fatal` an axiom that never
  returns (`os.Exit(1)`; as Perennial's `AngelicExit`, divergence: postcondition `False`); no
  verified function reaches `Fatal` (the protobuf axioms never fail), so it is not linked and
  in no baseline. `keyIndex.put`, `tombstone` and `get` are now specified over all inputs
  (decisions.md, "`key_index.go`'s panics as outcomes"): the former precondition is the normal
  case, and otherwise the result is the panic with zap's message and the key index unchanged
  (`tombstone`, in the code's order: empty → its panic; last generation empty →
  `ErrRevisionNotFound`; revision not above `modified` → `put`'s panic; `ki.gens ≠ []` stays a
  premise, an index out of range being stuck). They take `⌜lg ≠ null⌝` (so does
  `treeIndex.unsafeGet`; `isTreeIndex` records it, `newTreeIndex` requires it, `NewStore` has
  it) and `kiKey p k` where the panic reads the key. The callers (`treeIndex.Put`/`Tombstone`/
  `unsafeGet`, the range reads' visitors) discharge the case (`simp only [h, ↓reduceIte]` on
  the `if` under the result's binder, then `subst`); the panic unwinds through `wp_auto` with
  nothing special. Baselines: 57 axioms (`zap.Logger.Panic`), the mvcc collection 16
  (`zap.Int64`, `zap.String`, `zap.Logger.Panic`); verified-code figures unchanged.
- **Not yet**: the restore and the compaction (out of scope).
  `etc/verified-code.py` (2026-10-11, after `treeIndex.KeyIndex`/`Insert`): 58 of the package's
  155 functions verified, 655 of 2073 lines; of the KV core translated with bodies (661 lines),
  99% of the lines; `NewHashStorage` and `restore` count as assumed (`kvstore_txn.go` all 17
  functions, `index.go` 12 of 15 (the rest is the compaction), `key_index.go` 8 of 18,
  `revision.go` all 9, `kvstore.go` `NewStore`).
- **Perennial `bf935cbd5` pinned, `lean` merged** (2026-10-10 evening): the two Goose/semantics
  commits were rebased on upstream's `7cea8cc26` (panics and `recover`; no conflict; goose's
  tests, Perennial's build and the examples' regeneration checked) and pushed; the pin moved
  from `7c93f27aa` (via `lean`'s `7cea8cc26`) and `lean` (`client/v3/leasing`, the panic
  adoption, 15 commits) was merged (`fb427fb05`: both sides' `gen-link.py` modes and notes
  kept). `etc/goose.py --check` passes; the only translation that differed was `lean`'s
  regenerated `client/v3/concurrency` (`with_defer_recover:`). Two fixes for the new Perennial:
  `treeIndex.Get`'s proof stalled at the function's `return` (every pure `let` step now needs
  its value not to be a panic, `v.isPanic = false`, proved automatically for `#x` and
  constructors but not for an opaque `val`), so `ReadLemmas.kiGetVal_pairs` gives the
  4-tuple's components typed (`#m`, `#c`, `#v`, `#i`); and `etcdserver/BaseApply.lean`'s
  `storage/mvcc` instance, `True` from the names-only translation, failed once the
  translation had bodies (`define_is_pkg_init` wants prometheus's instance; the whole-repo
  build had not been run on this branch), so `BaseApply` now imports mvcc's `Base.lean`
  (which has `mvccInit` and the instances of traceutil, lease, schedule, prometheus) and its
  three duplicates (mvcc, traceutil, lease) are gone.
- **Incident**: a `lake env` call in the worktree, whose `.lake/packages` was then a symlink to
  the main checkout's, found the main checkout's manifest pointing at a Perennial revision
  (`1eabc2c47`, the other session's unpushed commit, with a non-GitHub remote) and re-cloned
  `.lake/packages/perennial`, deleting that clone and its build cache. Restored at the pinned
  `7c93f27aa` with the cache copied earlier; `1eabc2c47` exists in no local repository. The
  worktree now has its own `.lake/packages` (copies; `perennial` a clone of
  `/shared/perennial-mvcc` with the GitHub remote URL).
- **Environment**: this machine had no Lean or Go; elan (`~/.elan`, toolchain `v4.34.1`) and Go
  1.27.1 (`~/.local/go`) were installed user-locally, not on `PATH`.
## Recipes (`client/v3/experimental/recipes`)

Plan: `decisions.md`, "Recipes: the client contracts reused, the queue's claim, two prefixes as
one". Units 0 to 4; unit 0 (translation, scaffolding, the reproductions), unit 1 (the bundle,
`key.go`, `client.go`, `watch.go`), unit 1b (the three key helpers unit 1 left), unit 2 (the barrier,
the queue, the priority queue, the revision token) and unit 3 (the RWMutex, the double barrier)
are done and merged; the package is verified ("The whole package").

### Unit 0: translation and scaffolding (2026-10-11)

- **The Gooseable commit** `bc8b52a50` on the fork's `goose` branch (pinned in `etc/goose.py`),
  as concurrency's `207c8f747` and leasing's `0fc6f23b1`: Goose as pinned (Perennial
  `7cea8cc26`) rejects the package with 3 errors, all the known alias issue (`[impossible(go)]:
  expected (pointer to) struct type for base of selector, got *go.etcd.io/etcd/client/v3.Event`
  at `watch.go:49` (`ev.Type`), `queue.go:76` and `priority_queue.go:79` (`ev.Kv`)), and the
  calls of methods promoted from `*clientv3.Client`'s embedded interfaces (`c.Watch`,
  `client.Get/Put/Delete`) translate to `MethodResolve (*Client) "Get"`, which has no
  unfolding; a `*Client` passed as a `clientv3.KV` (`newKey(b.client, ...)`,
  `claimFirstKey(q.client, ...)`) dispatches to the same. The commit (7 files, +31/-22) binds
  `*clientv3.Event`s to `*mvccpb.Event`, calls through the fields (`c.Watcher.Watch`,
  `client.KV.Get/Put/Delete`) and passes `client.KV` where a `KV` is expected. One behavior
  difference, for a `Client` whose `KV` field is nil (no real client): `RemoteKV.Delete` returns
  `nil` where the original panics.
- **Configuration**: `Code/go_etcd_io/etcd/client/v3/experimental/recipes.toml` translates
  the package in full (`translate = ["*"]`, `imports = ["*"]`), listed in `etc/goose.py`;
  `client/v3.toml`: bodies for `WithFirstRev`, `WithFirstKey`, `WithLastKey`, `WithMaxModRev`,
  `WithMinModRev` (the recipes' get options; `WithMinModRev` is not called by the recipes but
  came with the batch); `Code/go_etcd_io/etcd/client/v3.lean` regenerated (+79 lines, bodies
  and unfoldings only). Everything else the plan suspected translates: `fmt.Sscanf(..., "%d",
  &newSeqNum)` (a call of Perennial's names-only `fmt.Sscanf` with `[]any{&newSeqNum}`), `for
  wresp := range wc` (`chan.forRange WatchResponse.ty`), `EphemeralKV{RemoteKV}` (below),
  `append(WithLastRev(), WithMaxModRev(...))` (`go.append` of a slice literal), the `...`
  spreads, `errors.Is` (`FuncResolve errors.Is`), `strings.Split`.
- **The translation, for the proof writers**: package namespace
  `go_etcd_io.etcd.client.v3.experimental.recipes`, assumptions class `...recipes.Assumptions`
  (imports context, mvccpb, clientv3, errors, concurrency, fmt, strings, time). `EphemeralKV`
  is a struct with one field `RemoteKV` (a `RemoteKV` value, not a pointer); `&EphemeralKV{*k}`
  is a `GoAlloc` of a composite literal of the loaded `*k`; its promoted methods
  `(*EphemeralKV).Delete/Key/Put/Revision/Value` have `MethodUnfold` instances
  (`EphemeralKV.TypeAssumptions.ptr_Revision_unfold`, ...) to `(*RemoteKV).M` applied to
  `StructFieldRef EphemeralKV.ty "RemoteKV" r`; `ek.rev` is `StructFieldRef RemoteKV.ty "rev"`
  of `StructFieldRef EphemeralKV.ty "RemoteKV"`. `waitEvents`'s loop is `chan.forRange
  WatchResponse.ty` over the `WatchChan`, the inner one `slice.forRange`; its `return ev` is
  `doReturn` out of both. `WaitEvents`/`WaitPrefixEvents` `defer cancel()`. The functions
  are `newKey`, `newKV`, `newUniqueKV`, `putNewKV`, `newSequentialKV`, `newEphemeralKV`,
  `newUniqueEphemeralKey`, `newUniqueEphemeralKV`, `deleteRevKey`, `claimFirstKey`,
  `WaitEvents`, `WaitPrefixEvents`, `waitEvents`, `NewBarrier`, `NewQueue`,
  `NewPriorityQueue`, `NewRWMutex`, `NewDoubleBarrier` and the methods `RemoteKV.{Key,
  Revision, Value, Delete, Put}`, `Barrier.{Hold, Release, Wait}`, `Queue.{Enqueue, Dequeue}`,
  `PriorityQueue.{Enqueue, Dequeue}`, `RWMutex.{RLock, Lock, waitOnLastRev, RUnlock, Unlock}`,
  `DoubleBarrier.{Enter, enteredClients, Leave}`; the errors are global variables
  (`ErrKeyExists`, ...: `GlobalVarAddr`).
- **Scaffolding**: `etc/gen-link.py --recipes` (namespace `recipes`; a clientv3 function's
  result `recipes.v3.wp_F`, concurrency's `recipes.concurrency.Session.wp_Client`, from their
  specs' own namespace, no change to the script needed) reading
  `etc/link-lean-first-recipes.txt` (every function of the package, 38, with its callees in Go
  order as a first guess, and the clientv3, concurrency and `fmt_Sscanf` lines they reach;
  self-calls, interface calls and Perennial-specified standard-library calls not listed). It
  fails now only on the missing specs (the 38, the four new clientv3 options, `fmt_Sscanf`).
  `etc/tcb-collections/recipes.txt`: the `roots` line, no baseline yet. `etc/proof_roots.py`
  and `etc/verified-code.py` need nothing (they find a package's `Link.lean`/`Results.lean` by
  directory).
- **Two findings, reproduced before any Lean** (`issues/recipes-dequeue-closed-watch.md`,
  `recipes-barrier-wait-closed-watch.md`; fix branch `recipes-closed-watch-channel`
  `0aa6c6af8`, one commit off upstream `main`, worktree `/shared/etcd-recipes-repro`; tests
  `tests/integration/clientv3/experimental/recipes/v3_closed_watch_test.go`): `waitEvents`
  returns `nil` when the watch channel closes (the client closed, or etcd cancels the watch
  for a compaction past the start revision), so `WaitEvents`/`WaitPrefixEvents` return `(nil,
  nil)`; `Queue.Dequeue`/`PriorityQueue.Dequeue` then dereference `ev.Kv` and panic (closing
  the client, or a compaction racing the watch's registration, 5 of 5 attempts), and
  `Barrier.Wait` returns `nil` while the barrier is held, `DoubleBarrier.Enter` `nil` with fewer
  than `count` entrants (`RWMutex.waitOnLastRev` and `Leave` only retry). The fix: `waitEvents`
  returns the canceled response's `Err()` or a new `ErrWatchClosed`, which the callers already
  propagate. For the proofs as shipped, `WaitEvents`'s spec takes the premise that the channel
  delivers the events before it closes (a nil dereference is stuck in GooseLang), stated on the
  watch channel.
- **Numbers** (`etc/verified-code.py --reuse`): the recipes 38 functions, 401 Go lines (at `bc8b52a50`), all
  translated, 0 verified (`double_barrier.go` 4/101 lines, `key.go` 13/98, `rwmutex.go` 6/46,
  `priority_queue.go` 3/37, `queue.go` 3/36, `watch.go` 3/32, `barrier.go` 4/26, `client.go`
  2/22); etcd 330 verified of 3599.
- **Gates**: `lake build` passes with the translation (the recipes' `Code` and
  `GeneratedProof` modules included); `etc/tcb-report.py --check` matches the baseline (42
  axioms, 1 sorry); `ETCD_SRC=/shared/etcd etc/goose.py --check` passes at the new pin.

### Unit 1: the base, the client bundle, `key.go`, `client.go`, `watch.go` (2026-10-11)

Files: `Proof/go_etcd_io/etcd/client/v3/experimental/recipes/` (`Base`, `InvRecipesClient`,
`InvRecipesLemmas`, `InvRecipesClaim`, one proof per function, `Link`) and
`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/`; deviations from the plan:
`decisions.md`, "Recipes", "Unit 1".

- **The bundle** `isEtcdRecipesClient client pfx` (persistent): the `KV` field with the
  contracts at `context.TODO()` (`isRecipesKV`: `isEtcdKVTodo`, `isEtcdTxnKVTodo`,
  `isEtcdDeleteKVTodo`, `isEtcdPutKVTodo`, `InvEtcdTxn.lean`; the recipes pass `TODO()` to every
  `KV` call, and `TODO()`'s context, never done, is not an `isContext`), and the `Watcher` field
  with `isEtcdRangeWatcherOpen` (`InvEtcdTxn.lean`): `isEtcdRangeWatcher` with the SPSC close
  predicate `False`. **The premise**: a watch channel is never closed (no compaction past a
  watched revision, the client not closed while a recipe waits); every recipes result rests on
  it, which the fixed code would not need (the two findings). No `ctx` field (unused).
- **Puts** (`InvEtcdTxn.lean`, the recipes' addition): `putTxn op` (the one-operation transaction
  `Then(OpPut(...))`), `putResult` (as `deleteResult`, through `runTxn`: no new etcd semantics),
  `isEtcdPutKV` (any `isContext`) and `isEtcdPutKVTodo`. `context.TODO()` specified and proved
  (`Spec/context/TODO.lean`: `todoCtxVal`).
- **Options** (`InvOp.lean`): `withMaxModRevM`, `withMinModRevM`; `WithFirstRev`, `WithLastKey`,
  `WithMaxModRev`, `WithMinModRev` specified and proved as the existing ones; **`WithFirstKey`**
  (`withTop(SortByKey, SortAscend)`, whose `WithSort` closure rewrites its captured `order`,
  which `WithSort.spec`/`withTop.spec` exclude) returns options needing a resource
  (`optsAtRes sl gs R`, `optSpecRes`, `optsAt_res`: the closures are called one at a time),
  proved by stepping into `withTop` and `WithSort`; `isEtcdKVTodo` takes such options.
- **Keys** (`key.go`): `RemoteKVSt` (`kv`, `key`, `rev`, `val`) behind `ownRemoteKV` (exclusive),
  `ownEphemeralKV` (the embedded field); `RemoteKV.Key/Revision/Value`, `Delete` (nil `kv`: `nil`;
  otherwise `deleteResult`; `kv` becomes nil), `Put` (needs a `kv`: `putResult` of
  `.put key val 0`). `putNewKV`: `(r, nil)` with `keyCreatedAt pfx key val lease r` (absent at
  `r - 1`, at `r` created with create/mod revision `r`, version 1, the value, the lease),
  `(0, ErrKeyExists)` with the key present at some `r ≥ lo`, or another error; `newKV`,
  `newKey`, `newEphemeralKV` (the session's client's `KV`, its lease `id`).
- **The claim** (`client.go`): `deleteRevKey kv key rev` (`rev > 0`): `(true, nil)` with
  `revKeyDeleted pfx key rev r` (mod revision `rev` at `r - 1`, absent at `r`), `(false, nil)`
  with `revKeyGone` (no `key` with mod revision `rev` at `r`), or an error; `claimFirstKey`: the
  first claimed `*KeyValue` with its `revKeyDeleted`, each before it gone (`claimedBefore`), or
  `nil` with all gone. **At most once** (`InvRecipesClaim.lean`, `revKeyDeleted_same_rev`): two
  claims of `(key, rev)` are at the same revision (history laws only).
- **Events** (`watch.go`): `waitEvents` (loop invariant: the consumer's received list and
  `0 ≤ i < len(evs)`; the close branch is `False`) returns an `*Event` with `waitedEvent pfx o
  rev typ ev` (`eventAt`, of the last awaited type, `rangeWatchEvOk`); `WaitEvents` /
  `WaitPrefixEvents` (`WithCancel(Background())`, deferred `cancel()`, `c.Watcher.Watch`):
  always `err = nil` (never `ErrNoWatcher`: the channel is not nil, `isChan_not_null`);
  `waitedEvent_key_delete`, `waitedEvent_put`, `waitedEvent_key` for the callers.
- **Deferred to unit 1b** (specs written, proofs `sorry`): `newUniqueKV`, `newSequentialKV`,
  `newUniqueEphemeralKV` (Perennial's `strings.Split`, `errors.Is`, `Sprintf` integer models;
  `fmt.Sscanf` an axiom then). `newUniqueEphemeralKey` is proved (a call of
  `newUniqueEphemeralKV`). The specs state the key's prefix `kp ++ "/"` and its creation; the
  decimal shape and `newSequentialKV`'s order are unit 1b's (the order needs a premise on the
  keys under the prefix, see `decisions.md`).
- **Link**: `etc/gen-link.py --recipes --skip-unproved` (new flag: leaves out the listed
  functions with no proof file and those reaching one, named in the header);
  `etc/link-lean-first-recipes.txt`: unit 1's lines in hypothesis order, `context_TODO`,
  `WithMinModRev`; `fmt_Sscanf` off `newSequentialKV`'s line until 1b.
- **Numbers** (`etc/verified-code.py --reuse`): the recipes 15 of 38 functions verified (14
  sorry-free: `newUniqueEphemeralKey` reaches a unit-1b `sorry`), 3 unfinished, 102 of 401 Go
  lines (`key.go` 47/98, `client.go` 22/22, `watch.go` 33/33); etcd 350 verified of 3599.
- **Gates**: `lake build` passes; `etc/tcb-report.py --collection etc/tcb-collections/recipes.txt`:
  the first baseline, the axioms `etcdReachedAt`, `etcdState`, `etcdState_revs`,
  `proto.Clone.wp_proof` and the three unit-1b `sorry`s; `etc/tcb-report.py --check`: the three
  `sorry`s are new, the repository baseline updated (`--check --update`: 42 axioms, 4 sorries).

### Unit 1b: `newUniqueKV`, `newUniqueEphemeralKV`, `newSequentialKV` (2026-10-11)

The three `sorry`s of unit 1 proved; decisions: `decisions.md`, "Recipes", "Units 1b, 2 and 3"
(the `Sscanf` axiom, `clientErrIs`, `newSequentialKV` not creating its key, `SeqKeysWf`).

- **`newUniqueKV`, `newUniqueEphemeralKV`**: the loop (`wp_for`, the variables as invariant)
  over `time.Now().UnixNano()`, `Sprintf("%s/%v")` (`str_slash_v_int64`: the key is
  `kp/<decimal of an int64>`, now in both specs) and `putNewKV`/`newEphemeralKV`; `errors.Is` on
  `ErrKeyExists` (`wp_Is_leaf`, from `errNewLeaf` in the package facts, `Base.lean`) retries; on
  the client's error (`wp_Is` with `clientErrIs`) either answer is fine (retry, or return the
  error). `newUniqueEphemeralKey`'s spec unchanged (its proof drops the decimal).
- **`clientErrIs`** (`InvEtcdTxn.lean`): `isEtcdTxnKVTodo`'s builder also gives
  `txnCommitErrTodo` (its `Commit` with `clientErrIs` on an error); threaded through the third
  case of `putNewKV`, `newKV`, `newEphemeralKV` (`newKey`'s spec unchanged). `deleteRevKey`'s
  proof adapted (one pattern).
- **`newSequentialKV`** (Löb induction for the retry; `wp_join` with a general postcondition
  for the `if len(resp.Kvs) != 0` block, which may return `Sscanf`'s error): the spec
  takes `pfx <+: __kp` and returns `seqKeyPutAt pfx kp key val g r` (the key made from the
  get's state at `g ≥ lo`, `SeqNext`; the state at `r ≥ g` the puts of `__kp` and the key on
  the state at `r - 1`, `__kp` unmodified since `g`), not `keyCreatedAt`: the transaction does
  not check the key's absence. `InvRecipesSeq.lean`: `lastKeyOp` (`WithLastKey()`'s get) and
  `lastKeyOp_kvs` (its one key-value is the greatest of the range), `lastField`
  (`strings.split`'s last field, `lastField_slash`), `scanInt_fixedDigits`, `seqTxn` and its
  lemmas, `sprintf_slash_016d` (any sign), the order: `seqNext_order` / `seqKeyPutAt_order`
  (under `SeqKeysBelow kp (10^16 - 1)` at `g`: the key is `seqKey kp m`, `m` one past the
  greatest, `m < 10^16`, above every key with prefix `kp` then), `seqNext_absent`,
  `seqKeyPutAt_created` (fresh, given also no new key under `kp` between `g` and `r - 1`).
- **`fmt.Sscanf`**: an etcd-grove axiom (`Spec/fmt/Sscanf.lean`, `fmt.scanInt`), linked
  (`fmt_Sscanf` on `newSequentialKV`'s line).
- **Spec changes the units 2 and 3 meet**: `newSequentialKV`'s (new premise, new success
  case; `PriorityQueue.Enqueue`), `newUniqueKV`'s and `newUniqueEphemeralKV`'s pure success
  facts have a fourth conjunct (the decimal), `putNewKV`/`newKV`/`newEphemeralKV`'s third case
  is `⌜..⌝ ∗ clientErrIs err`, `recipesInit`'s first conjunct has `⌜errNewLeaf e⌝`,
  `isEtcdTxnKVTodo`'s builder a third conjunct (`txnCommitErrTodo`).
- **Numbers** (`etc/verified-code.py --reuse`): the recipes 18 of 38 functions verified, none
  unfinished, 153 of 401 Go lines (`key.go` 98/98, `client.go` 22/22, `watch.go` 33/33); etcd
  353 verified of 3599.
- **Gates**: `lake build` passes (the full build); `etc/tcb-report.py --collection
  etc/tcb-collections/recipes.txt --check --update`: the three `sorry`s gone, the axiom
  `fmt.Sscanf.wp_proof` added (Perennial's `errors.wp_Is` and `time.wp_Now` are not listed:
  the report lists this repository's); `etc/tcb-report.py --check --update`: the same change to
  the repository baseline (43 axioms, 1 sorry).
### Unit 2: the barrier, the queue, the priority queue (2026-10-11)

Files: `Proof/go_etcd_io/etcd/client/v3/experimental/recipes/` (`InvRecipesBarrier`,
`InvRecipesQueue`, one proof per function, `Results`, `Link`) and their specs; the token and the
`More` flag in `Proof/go_etcd_io/etcd/cache/v3/InvEtcdTxn.lean`; deviations from the plan:
`decisions.md`, "Recipes", "Units 1b, 2 and 3".

- **The revision token** (`InvEtcdTxn.lean`): `etcdRevToken r` (an axiom beside `etcdState`,
  exclusive: `etcdRevToken_excl : etcdRevToken r ∗ etcdRevToken r ⊢ False`). The builder's
  `Commit` (`txnBuilderSpec`, under the prefix; so `isEtcdTxnKV` and `isEtcdTxnKVTodo`) returns
  `txnCommitResultTok`: `txnCommitResult`'s facts and, if the transaction wrote (`txnWrote`), the
  token of its revision; `txnCommitResultTok_result` drops it (the six concurrency call sites:
  `Mutex.tryAcquire`, `Election.Campaign/Proclaim/Resign`, the two STM commits, one line each).
  A read-only transaction makes no revision (etcd's `storeTxnWrite.End` advances the revision
  only if the transaction changed something) and gets no token. `putResult` carries the token (a
  put always writes). Not given: `deleteResult` (no caller needs it), leasing's
  `txnCommitResultO`. `deleteRevKey`'s `true`, `putNewKV`'s `nil` and `claimFirstKey`'s claimed
  item return it; `revKeyDeleted_once` (`InvRecipesClaim.lean`): two successful claims of one
  `(key, rev)` are impossible.
- **The get's `More` flag** (`getRespMore`, `InvEtcdTxn.lean`): `isEtcdKVTodo` also returns the
  response's `More`, etcd's (`asembleRangeResponse`: a positive limit cut the selection). The
  queues read it; without it the wait path could not say that the get listed every item.
- **Barrier** (`isBarrier b client key`: read-only fields, the bundle at the prefix `key`):
  `NewBarrier`, `Hold` (`newKey`: `keyCreatedAt`, or `ErrKeyExists` with the key present, or an
  error), `Release` (`nil`: the key absent at some `r ≥ lo`), `Wait` (`nil`: the key absent at
  some `r ≥ lo`: at the get's revision, the early return, or at the delete event's, from
  `R + 1`). `Wait` takes `0 ≤ lo` (the watch's revision `R + 1` must be non-negative).
- **Queue** (`isQueue q client kp`, `kp ≠ []`, the bundle at `kp`): `NewQueue`, `Enqueue`
  (`newUniqueKV`'s key under `kp ++ "/"` created with the value), `Dequeue` (Löb induction,
  `iloeb`, for the two retries: `More`, and a lost claim on the wait path; the recursive call is
  `rw [method_unfold ...]` then the induction hypothesis). `(v, nil)`: an item `it` with
  `v = it.value`, `dequeuedAt kp kp it r` (in etcd's state at `r - 1`, `revKeyDeleted` at `r`,
  the token of `r`) and `dequeueOrder kp kp modRevLe it r` (below).
  A get's `*KeyValue` may be a nil pointer as far as the contract says (nothing makes it
  non-nil), so the code's `kv != nil` is a real branch: a claimed item at a nil pointer counts as
  gone (`revKeyDeleted` gives `revKeyGone` at the same revision), and the proof goes on as if
  nothing were claimed.
- **Priority queue** (`isPriorityQueue q client key`: the prefix field `key ++ "/"`, the bundle at
  `""`): `NewPriorityQueue`, `Enqueue` (`Sprintf("%s%05d", ...)` by `SprintfOut.str_05d_uint16`:
  the key is under `key ++ "/" ++ padZeros 5 (decimal pr) ++ "/"`), `Dequeue` (the queue's
  proof, with `WithFirstKey()`'s resource-threaded options and `keyLe`).
- **Results** (`Results.lean`, `#print axioms` of each): the specs restated (`barrier_hold`,
  `barrier_release`, `barrier_wait_release`, `queue_*`, `pqueue_*`); `queue_dequeued_once`,
  `pqueue_dequeued_once` (two dequeues of the same `(key, mod revision)`: `False`, by the
  tokens); `queue_dequeued_was_enqueued`, `pqueue_dequeued_was_enqueued` (the item, with its
  value, under the prefix at `r - 1`; for the queue also absent at `r`); `queue_fifo`,
  `pqueue_min_key` (at the get's revision `r0 < r`: the item was there with the least mod
  revision / key under the prefix — **the get path** — or every item under the prefix at `r0`
  was gone at some revision in `[r0, r]` and the item was put at or after `r0` — **the wait
  path**); `queue_fifo_before_claim` (by `etcdState_modrev_persist`, below).
- **Weaker than planned, and why.** (1) *FIFO just before the claim* (`r - 1`) is not provable from
  the model's history laws: they do not exclude a key whose mod revision goes back within one
  lifetime (`etcdState_create_persist` keeps the key, not its record; `etcdState_modrev_det` says
  one record per mod revision), so an item older than the claimed one could be at `r - 1`
  without being at the get's revision. With the law that a key-value lives unchanged from its mod
  revision while present (`etcdState_modrev_persist`, the model's seventh history axiom since
  2026-10-11; a hypothesis `EtcdModRevPersist` of the result before), the get path's FIFO holds at
  `r - 1` (`queue_fifo_before_claim`). (2) *The wait path*:
  the watch contract (`rangeWatchRespOk`) says events are real, not that none is skipped, so
  nothing is said of items put between the get and the event; the wait path states that the
  get's items were all claimed by others by `r` and that the item was put at or after the get's
  revision (`WaitPrefixEvents` from `r0`, not `r0 + 1`: an event at `r0` itself is possible).
  (3) *The priority queue's least key* is at the get's revision only, and **is false at the
  claim** in etcd, not only unprovable: an `Enqueue` of a higher priority (a smaller key) between
  the get and the claim is not seen, and `Dequeue` returns a lower-priority item while a
  higher-priority one is present (no premise rules it out; the recipe is not a linearizable
  priority queue; its comment "returns Enqueue()'d items in FIFO order" is copied from the
  queue). Reproduction sketch: client A calls `Dequeue` on a queue holding priority 5 only;
  after A's `Get` returns the priority-5 item and before A's `deleteRevKey` commits (a
  breakpoint, or a delay injected in `claimFirstKey`), client B calls `Enqueue(v, 1)`; A returns
  the priority-5 item while the priority-1 item is present. FIFO for the plain queue has no such
  race: an item put after the get has a larger mod revision.
- **`pqueue_order`** (least key = highest priority, then FIFO) is not stated: it needs unit 1b's
  `SeqKeysWf` order theorem; the statement for the merge is in `decisions.md` (stated at the
  merge: "Merge of unit 2").
- **Numbers** (`etc/verified-code.py --reuse`): the recipes 25 of 38 functions verified (22
  sorry-free; 3 unfinished: unit 1b's), 203 of 401 Go lines (`barrier.go` 26/26, `queue.go` 37/37,
  `priority_queue.go` 38/38); etcd 360 verified of 3599. The enqueues reach unit 1b's `sorry`s
  (`newUniqueKV`, `newSequentialKV`).
- **Gates**: `lake build` passes (the cache, concurrency and leasing rebuilt on the contract
  change); `etc/tcb-report.py --collection etc/tcb-collections/recipes.txt --check --update`: new
  `etcdRevToken`, `etcdRevToken_excl` (the token), `etcdState_agree`, `etcdState_create_persist`,
  `etcdState_modrev_det` (already in the repository's base, now reached by the recipes);
  `etc/tcb-report.py --check --update`: the two token laws only (48 entries).

### Unit 3: the RWMutex and the double barrier (2026-10-11)

Files: `Proof/go_etcd_io/etcd/client/v3/experimental/recipes/` (`InvRWMutex`, `InvDoubleBarrier`,
one proof per function, `Results` (unit 3's section)) and their specs; decisions:
`decisions.md`, "Recipes", "Units 1b, 2 and 3" (the unit 3 bullets).

- **RWMutex** (`isRWMutex m s γ client id pfx`: session, `context.TODO()`, prefix `pfx` with
  `NewRWMutex`'s `/`, the bundle at `pfx`, `context.isClosedchanInit`; `rwMyKey m pfx o`: `myKey`).
  `waitOnLastRev(bp)`: the get `lastRevOp bp (myRev - 1)` (`WithLastRev()` appended with
  `WithMaxModRev`, `lastRevOp_kvs`); `(true, nil)` with `RWBlockFree bp myRev` at the get's
  revision, else `WaitEvents` for the last key's deletion and `false`. `RLock`/`Lock`: a fresh key
  under `pfx/read/` / `pfx/write/`, then `waitOnLastRev(pfx + "write")` / `(pfx)` until done:
  `nil` means `rwHeldAt pfx role key c R`. `RUnlock`/`Unlock`: `myKey.Delete()`
  (`rwUnlockResult`). **Exclusion** (`rwmutex_write_exclusion`, `rwmutex_read_write_exclusion`):
  as `Mutex`'s, plus the premise that the holders' keys are never modified (`keyUnmodified`): the
  recipe filters by mod revision, so a key rewritten by another client stops blocking.
- **DoubleBarrier** (`isDoubleBarrier b s γ client id key count`: with `0 < count`, a
  precondition of `NewDoubleBarrier`; `dbMyKey`). `enteredClients`: the waiters (prefix
  `key/waiters`) sorted by create revision (`waitersResp`). `Enter` (`enterResult`): `nil` with
  `enterReady` (the direct path's `count` waiters seen, `waitersSeen`; the waiting path's write of
  `key/ready` at or after its key's creation, `readyPut`); `ErrTooManyClients` with the key
  possibly left (its `Delete`'s error is ignored); results `double_barrier_enter_ready` (no
  premise) and `double_barrier_enter_count` (under `readyPutsCounted`: `count` waiters seen at a
  revision etcd has reached). `Leave` (Löb induction): `nil` means the key absent at some `r ≥ lo`
  (`double_barrier_leave`, for the record `Enter` leaves), or its record already deleted.
- **No finding.** Misuse is a precondition: `RUnlock`/`Unlock`/`Leave` with a nil `myKey` (a nil
  dereference; `Leave` only if waiters are left), `count ≤ 0`. The mod-revision filter of
  `waitOnLastRev` is the premise above, not an issue (only another client's `Put` into the
  prefix triggers it).
- **Link**: `NewRWMutex`, `NewDoubleBarrier` take `context_TODO`; the other unit 3 lines were in
  hypothesis order already. `Link.lean` regenerated (`--skip-unproved`).
- **Numbers** (`etc/verified-code.py --reuse`): the recipes 25 of 38 functions verified (21
  sorry-free: `RLock`, `Lock`, `Enter` and `newUniqueEphemeralKey` reach unit 1b's
  `newUniqueEphemeralKV` `sorry`), 249 of 401 Go lines (`rwmutex.go` 46/46,
  `double_barrier.go` 101/101); etcd 360 verified of 3599.
- **Gates**: `lake build` passes; `etc/tcb-report.py --collection etc/tcb-collections/recipes.txt`:
  the exclusion results add the existing history law `etcdState_create_persist` to the
  collection's baseline (updated); `etc/tcb-report.py --check` matches the repository baseline
  (42 axioms, 4 sorries).

### Merge of units 1b and 3 (2026-10-11)

Unit 3 (branch `recipes-u3`) merged onto unit 1b. Unit 3's proofs needed no change for 1b's spec
changes (they use `newUniqueEphemeralKey`, whose spec is unchanged, and discard `recipesInit`'s
first conjunct). Conflicts: `Link.lean` (regenerated from the merged `link-lean-first-recipes.txt`,
which merged cleanly), the notes (both units' subsections kept).

- **Numbers** (`etc/verified-code.py --reuse`): the recipes 28 of 38 functions verified, all
  sorry-free, 300 of 401 Go lines; etcd 363 verified of 3599 (unit 3's "21 sorry-free" above
  predates 1b's proofs).
- **Gates**: the full `lake build` passes; `gen-link.py --recipes --skip-unproved` reproduces
  `Link.lean`; the recipes collection: `etcdReachedAt`, `etcdState`, `etcdState_create_persist`,
  `etcdState_revs`, `fmt.Sscanf.wp_proof`, `proto.Clone.wp_proof`, no `sorry`;
  `etc/tcb-report.py --check` matches the repository baseline (43 axioms, 1 sorry), every other
  collection unchanged.

### Merge of unit 2 (2026-10-11)

Unit 2 (branch `recipes-u2`) merged onto units 1, 1b and 3.

- **Conflicts**: `InvEtcdTxn.lean` merged textually; resolved by hand so that 1b's
  `txnCommitErrTodo` (the `TODO()` builder's `Commit` with `clientErrIs`) returns unit 2's
  `txnCommitResultTok` (the token and the error premise both: `putNewKV`'s `nil` has the token,
  its third case `clientErrIs`). `putNewKV.lean`, `newKV.lean` (both sides' patterns combined),
  `Results.lean` (unit 2's section, then unit 3's, then the order below; every `#print axioms`),
  `Link.lean` (regenerated), `etc/tcb-collections/recipes.txt`, the notes (subsections in unit order).
- **Adaptations to unit 2's contract** (one line each): the `TODO()` `Get`'s third conjunct
  (`getRespMore`) in `newSequentialKV`, `RWMutex.waitOnLastRev`, `DoubleBarrier.enteredClients`,
  `Leave`; `newSequentialKV`'s `Commit` (`txnCommitResultTok_result`); `newUniqueKV` drops
  `putNewKV`'s token; `DoubleBarrier.Enter`'s `Put` result bound non-persistent.
  `newUniqueEphemeralKV`, `newKV`'s callers, `RLock`/`Lock`, `Barrier.Hold` needed nothing.
- **Adaptations to 1b's**: `PriorityQueue.Enqueue`'s spec returns `seqKeyPutAt [] (key/%05d(pr))
  k val g r` with `lo ≤ g ≤ r` (unit 2 had `keyCreatedAt`, which `newSequentialKV` no longer
  gives: it does not check the key's absence); `Queue.Enqueue` needed nothing.
- **`pqueue_order`** (`Results.lean`, section "The priority queue's order"): `pqKey key p n =
  key/%05d(p)/%016d(n)`; `PQKeysWf key s` (every key under `key/` is a `pqKey` with `p < 10^5`,
  `n < 10^16`); `pqKey_lt`/`pqKey_le` (key order is lexicographic (priority, sequence number):
  `padZeros_decimalNat_lt` and equal-width prefixes); `pqueue_order`: from `dequeuedAt` and
  `dequeueOrder … keyLe`, at the get's revision `r0 < r`, `it ∈ s0` and, under `PQKeysWf key s0`,
  `it.key = pqKey key p n` with `(p, n)` lexicographically least among the items under `key/`
  (or the wait path's facts); `pqueue_enqueue_order`: on `Enqueue`'s result, under
  `SeqKeysBelow (key/%05d(pr)) (10^16 - 1)` at the get, the key is `pqKey key pr n`, above every
  key of that priority then, `n` one past the greatest; `pqKeysWf_seqKeysWf`: `PQKeysWf` gives
  each priority's `SeqKeysWf`. No axiom (`EtcdModRevPersist` stayed a hypothesis until the
  owner promoted it, below).
- **Gates**: the full `lake build` passes; `gen-link.py --recipes` (plain: `--skip-unproved` now
  skips nothing, and the usage line for it is gone) reproduces `Link.lean`; the recipes collection
  (`--check --update`): `etcdReachedAt`, `etcdRevToken`, `etcdRevToken_excl`, `etcdState`,
  `etcdState_agree`, `etcdState_create_persist`, `etcdState_modrev_det`, `etcdState_revs`,
  `fmt.Sscanf.wp_proof`, `proto.Clone.wp_proof`, no `sorry`; `etc/tcb-report.py --check --update`:
  `etcdRevToken`, `etcdRevToken_excl` added (45 axioms, 1 sorry); the cache and concurrency
  collections gain `etcdRevToken` (their builder's `Commit` names it since unit 2; unit 2 left them
  stale; updated), the others match.

### The whole package (2026-10-11)

All 38 functions of `client/v3/experimental/recipes` (401 Go lines, at `bc8b52a50`) are specified
and proved, sorry-free (`etc/verified-code.py --reuse`: 38 of 38, 401 of 401 lines; etcd 373
verified of 3599, 3712 lines). `Results.lean` restates 33 results with `#print axioms`.

- **Results**: `barrier_hold` (`nil`: the key created), `barrier_release` (absent after the
  call), `barrier_wait_release` (`Wait`'s `nil` only once released); `queue_Enqueue`,
  `queue_Dequeue`, `pqueue_Enqueue`, `pqueue_Dequeue` (the specs); `queue_dequeued_once`,
  `pqueue_dequeued_once` (no item dequeued twice, by the revision tokens);
  `queue_dequeued_was_enqueued`, `pqueue_dequeued_was_enqueued` (the item was under the prefix
  just before the claim); `queue_fifo` (least mod revision at the get, or the wait path),
  `queue_fifo_before_claim` (least just before the claim, by `etcdState_modrev_persist`),
  `pqueue_min_key` (least key at the get), `pqueue_enqueue_order` (an enqueue's key above its
  priority's), `pqueue_order` (least priority, then earliest, at the get);
  `rwmutex_RLock`/`Lock`/`RUnlock`/`Unlock`, `rwmutex_unlock_released`,
  `rwmutex_write_exclusion`, `rwmutex_read_write_exclusion` (writer/writer and reader/writer
  exclusion); `double_barrier_Enter`/`Leave`, `double_barrier_enter_ready` (what each path saw),
  `double_barrier_enter_count` (`count` waiters seen), `double_barrier_leave` (the key gone); the
  constructors.
- **Premises**: the watch channel is never closed (the bundle, `isEtcdRangeWatcherOpen`: no
  compaction past a watched revision, the client not closed while a recipe waits; the fixed code
  would not need it); the session's lease (as `Mutex`'s exclusion); `keyUnmodified` (RWMutex: no
  other client rewrites a lock key); `SeqKeysWf`/`SeqKeysBelow`/`PQKeysWf` (the priority queue's
  order: the keys under its prefix are the recipe's, fewer than `10^16` per priority);
  `readyPutsCounted` (the double barrier's count: only `Enter`s write `key/ready`).
- **Trust base** (the recipes collection): the model's `etcdState` laws, now with
  `etcdState_modrev_persist` (a key-value lives unchanged from its mod revision while present;
  the owner promoted `queue_fifo_before_claim`'s hypothesis `EtcdModRevPersist` to this axiom on
  2026-10-11, so the result is unconditional), the token (`etcdRevToken`, `etcdRevToken_excl`),
  `fmt.Sscanf.wp_proof`, `proto.Clone.wp_proof`.
- **Findings** (unit 0; `issues/recipes-dequeue-closed-watch.md`,
  `recipes-barrier-wait-closed-watch.md`, fix branch `recipes-closed-watch-channel`): on a closed
  watch channel `Queue.Dequeue`/`PriorityQueue.Dequeue` panic on a nil `ev.Kv`, and
  `Barrier.Wait` (and `DoubleBarrier.Enter`) report release while held.
- **Design note, and a documentation issue**: the priority queue is not linearizable: an `Enqueue` of a
  higher priority between a `Dequeue`'s get and its claim is not seen, so `Dequeue` can return a
  lower-priority item while a higher-priority one is present (unit 2, "Weaker than planned");
  its order holds at the get's revision. Its comment ("returns Enqueue()'d items in FIFO order",
  copied from the queue) is recorded as a documentation issue,
  `issues/recipes-pqueue-dequeue-order.md`.

## Perennial `cb6a5921e`: one `AllG` (2026-10-11)

Perennial `cb6a5921e` (`lean`) makes `AllG GF` a singleton: `GooseGlobalGS` has the field
`gooseAllG : AllG GF` (a reducible instance, so `HeapGS` provides it), the ghost state of
the thread tokens and time receipts (`ThreadGS` and `ReceiptGS` no longer carry their own
`AllG`, and `ThreadGpreS`/`ReceiptGpreS` are gone: `GooseGpreS.goosePreGAllG`). A section
with `[hG : HeapGS hlc GF]` must not add `[AllG GF]`: that is a second instance, and its
resources do not match Perennial's (`iexact: cannot unify threadTok and threadTok` in
`Cache__Watch`, `dghostVar` in `Handoff`). Done here:

- `[AllG GF]` dropped from every `variable` line, theorem binder and `omit` next to `HeapGS`
  (654 files, mechanical; `etc`-free: a script over the `variable`/`theorem`/`omit` lines).
  The seven generic ghost-theory files without `HeapGS` (`raft/v3/Protocol/*`, `Results.lean`)
  keep it. `notes/porting-guide.md`, "Section variables", updated.
- `GF` is not an out-parameter of `HeapGS`, so a term whose `GF` nothing else fixes now
  needs `(GF := GF)`: `InvApply.skip_done`'s statement (`consInv`), and the register's
  `regStorIface_inj _ _ Hst` (a theorem whose binders include the section's `HeapGS`, so
  its `GF` is never inferable from its statement; three call sites). Everything else builds
  unchanged. Also in the pin: `114b847ff` (Goose: `range` over an integer) and `bf935cbd5`
  (`float64(n)` of an integer).
## The register's cluster driver: a closed program, safe from package initialization (2026-10-11)

`examples/register/cluster.go` holds `Main()`. It builds three replicas (ids 1, 2, 3): a
`NewStorage`, a `raft.RestartNode` with a `quietLogger{}` and PreVote off, then `New`. They are
connected in process by `deliver`, the `send` callback. A goroutine per node calls `Tick` 2^20 times,
sleeping 5 ms between calls. Two clients run on top: A does `Put("hello")` on replica 1 and then
signals B over a channel. B, on Main's own thread, does `Get()` on replica 2 and panics if the
result is not `"hello"`. `go test -race` runs it (`TestCluster`). The translation is regenerated.

Proved and linked (`Link.lean` by `etc/gen-link.py --register`; `#print axioms` in
`Results.lean`): `Main`, `deliver`, `deliverable`, `tick`, and `quietLogger`'s formatting methods.
The top-level statement (`register_Main`, `Spec/.../register/Main.lean`) is
`{{ isPkgInit register }} Main() {{ RET #(); True }}`, at `HeapGS HasLC.hasLC GF` with `[AllG GF]`
and no storage registry. It rests on raft's `reflect.DeepEqual.wp_proof` axiom only, with no
`sorryAx`: `RestartNode` reaches that axiom. The register's TCB collection was updated by
hand (see below).

- **Everything allocated in the proof.** The proof allocates the storage registry and
  instantiates the register's specs at it: `Main.wp_proof` takes its callees' specs at any
  `RegStor GF`. It also allocates `ownRaftGhost_alloc` for {1,2,3} with
  `γ.reCfg = listToSet voters`, `budget_alloc (3 * 2^20)` with the tick credits,
  `propDataInv_alloc`, `regInv_alloc` (the sequence tokens at 0), and the clients' invariant
  (`clientInv`, `Cluster.lean`: the client's half of the value and half of a flag "A's `Put`
  is done", whose other half A holds). Every premise of `RestartNode`, `NewStorage`, `New`,
  `node.Step` (in `deliver`), `node.Tick`, `Put` and `Get` is discharged there. None of them
  is vacuous.
- **A vacuity bug found by composing.** `isLogger` (raft's `Logger` contract, `InvLogger.lean`)
  held of no `Logger`. `logMethods` listed `Info`/`Debug`/`Warning`/`Error`, and `isLogger`
  states every method as a call on a format and then an argument slice. Those four take a single
  variadic parameter, so that call gets stuck. As a result `RestartNode`/`NewRawNode`, which
  take `isLogger`, were vacuous. `logMethods` is now `Infof`/`Debugf`/`Warningf`/`Errorf`.
  raft calls `Error` only on uncovered paths (`stepFollower`'s `MsgForgetLeader`,
  `releasePendingReadIndexMessages`). Every existing use was an f-variant, so no raft proof
  changed. This was found only because `Main` had to construct a `Logger`.
- **The transport.** `Ready` says of its messages only `isRaftMsg` and `termLB`. `node.Step`
  takes `stepP`, which needs more: `NetMsgOk` (the type, `To` the receiver, a nonzero term and
  sender, not self-sent), a context, and owned entries. `deliverable` checks in Go what
  `Ready` does not promise: the type, `From ≠ 0`, `From ≠ To`, a nonzero term but for a
  `MsgProp`, and a nil `Context`. A nil slice points to `[]` for free; an empty non-nil one
  does not. Routing by `peers[m.To]` makes `To` the receiver, and `deliver` copies the
  entries. raft drops nothing in practice: a temporary panic on a non-deliverable message
  never fired in 20 test runs. The proof pieces are `raftMsg_deliverable` and
  `stepP_deliverable` (`Cluster.lean`). No raft spec changed for the transport.
- **What an adequacy theorem needs from it.** Perennial's `goose_adequacy`
  (`GooseLang/Adequacy.lean`) takes
  `ffiGlobalStart -∗ ffiLocalStart -∗ ownGoState σ.packageState -∗ threadTok ={⊤}=∗ WP e {{ ⌜φ⌝ }}`.
  For `e = initialize' register #(); Main #()` from an `IsInit` state (empty package state),
  three things are missing. First, `ownGoState ∅` has to become `ownInitializing` (unfolding
  `ownInitializingDef` at the empty map). Second, a proved `register.wp_initialize'`: it needs
  raft's, and every standard-library package's, `wp_initialize'`, and Perennial's
  `time.wp_initialize'` is a `sorry`. Third, `register_Main` is then applied to the
  `isPkgInit` that initialization returns. Neither `Main` nor the register uses thread tokens
  (`wp_fork` without one), so any thread bound `T` works.

Not checked: `etc/tcb-report.py --collection etc/tcb-collections/register.txt --check --update`
needs a full build, and the disk (≈400 MB free) does not allow one. The collection's
`axiom reflect.DeepEqual.wp_proof` line was written from `#print axioms register_Main`.
Checked since (2026-10-11, the merge with Perennial `e4e126e46`): `--collection
etc/tcb-collections/register.txt --check` matches (1 axiom, 0 sorries) after a full build.

## Panic and recover: Perennial's panics adopted, the STM's axioms gone (2026-10-10)

Perennial branch `panic` (`b4f46e1dd`..`c46da895a`: a panic outcome `PanicV` in GooseLang,
`Catch`, `with_defer_recover:`; and `d958136aa`, `c01745d27`, `7cea8cc26`: standard-library
models) is adopted; **the pin is not moved in this tree**: the branch builds with
`lake build --packages=<a manifest whose perennial is a path to that checkout>` and needs
Perennial `7cea8cc26` pinned once pushed. Design and the implementation's deviations:
`decisions.md`, "Panic and recover" and "The standard library's models".

- **Adoption**: Goose translates only `runSTM`'s goroutine differently (its deferred literal calls
  `recover()`: `with_defer_recover:`); the 68 other `with_defer` sites are unchanged. Two proofs
  changed: `runSTM` (`wp_with_defer_recover`, `wp_recoverPanic`) and, indirectly,
  `EtcdServer.applyEntryNormal` (it binds `etcdserverpb.AlarmType_NOSPACE`, an axiomatized
  constant `val` a `let` can no longer bind without knowing it is not a panic: now translated,
  `etcdserverpb.toml`). Every other proof builds unchanged.
- **STM**: `fetch` and both commits state their abort (`stmRet`: a return, or the panic of
  `stmError{err}`, `err ≠ nil`; `wp_panic`); `Get`, `Rev`, the interface's triples and the closure
  (`applySpec`) propagate it; `runSTM` recovers it (`Catch`, the deferred literal's `recover()`,
  the assertion to `stmError`, `(nil, err)` sent). `NewSTM`'s spec is unchanged. The axioms
  `stmPanic.spec`, `stmRecover.spec` are gone.
- **Mutex**: `lockerMutex.Lock`/`Unlock` (`NewLocker`'s `sync.Locker`) specified and proved, a
  return or `panic(err)` (`locker_Lock`, `locker_Unlock` in `Results.lean`).
- **Leasing**: `strings.Compare`, `strings.TrimPrefix`, `errors.As`, `(*time.Time).Add` are
  Perennial's (`strings.wp_Compare`/`wp_TrimPrefix` from trusted models, `errors.wp_As` an axiom
  in Perennial with an error-tree precondition, `time.Time.wp_ptr_Add` from `ptr_Add_unfold`);
  their four axiom pairs here are gone. Contract change: `txnCommitResultO`'s error case carries
  `clientErr` (a leaf error without `As`/`Unwrap` methods, an `EtcdError` if of that type), which
  `acquire` gives `errors.wp_As`. `status.FromError` stays an axiom.
- **Merged** `lean` at `1bf5733bf` (leasing unit 5) on top: no conflict but the leasing link list
  (regenerated); builds unchanged.
- **Trust base** (after `--check --update`): 42 axioms, 1 `sorry` (`etc/tcb-baseline.txt`; −6:
  `stmPanic`, `stmRecover`, `strings.Compare`, `strings.TrimPrefix`, `errors.As`,
  `time.Time.Add`); collections: concurrency 11 axioms (the etcd model's), 1 `sorry`
  (Perennial's `context.wp_WithDeadlineCause`); leasing 8 axioms; btree 0, cache 9, raft 1,
  register 0, server 26, unchanged.
- **Gates** (with `--packages`): `lake build` passes (2176 jobs); `etc/tcb-report.py --check` and
  every collection pass; `etc/goose.py --check --perennial /shared/perennial-panic` passes;
  `etc/gen-link.py --cache/--concurrency/--leasing/--server` reproduce the Links;
  `etc/verified-code.py --reuse --package go.etcd.io/etcd/client/v3/concurrency`: 62 functions,
  61 verified, 1 unfinished (`Session.Close`, through Perennial's `sorry`), none translated-only
  (the two locker wrappers were).
- **Push order**: Perennial `panic` (`7cea8cc26`) first, re-pin, then etcd-grove.

## client/v3/leasing: the protocol premise and the lease cache (2026-10-10)

Units 1 and 2 of 5 of `client/v3/leasing` (the caching `KV`): its translation, the protocol as a
premise on etcd's history with its key lemma, and the lease cache (`cache.go`, `util.go`)
specified and proved: every function of `cache.go`, and of `util.go` but
`gatherOps`/`gatherResponseOps` (nested transactions, unit 5). Design: `decisions.md`, "Leasing: the protocol as a premise on the
history". Files: `Proof/go_etcd_io/etcd/client/v3/leasing/` (`Base`, `InvLeasingModel`,
`InvLeaseCache`, `InvLeaseEval`, lemma modules `InvLeaseCacheLemmas`, `InvLeaseCacheWrite`,
`InvLeaseEvalLemmas`, `Link`, `Results`), `Spec`/`Proof`
pairs for every function of `cache.go` and of `util.go` but `gatherOps`/`gatherResponseOps`.

- **Translation**: `client/v3/leasing` with bodies (`leasing.toml`), on the etcd fork's
  `0fc6f23b1` = `goose-lean` (`ab1deb078`) + one **Gooseable** commit (not pushed: push it to
  `upamanyus/etcd`'s `goose-lean` first): kv.go calls `lkv.cl.Watcher.Watch(...)` (the promoted
  `Watch` of `*Client` has no unfolding) and binds `resp.Events` to a `[]*mvccpb.Event` (the alias
  issue), as `207c8f747` did for concurrency. `client/v3.toml`: the `Op` getters
  (`KeyBytes`, `ValueBytes`, `IsGet`, `IsPut`, `IsDelete`, `IsTxn`, `Txn`, `IsKeysOnly`), `OpTxn`,
  `WithIgnoreLease`, `WithKeysOnly`, `WithLastRev`, `Cmp.KeyBytes`/`GetCompare`, the responses'
  `OpResponse`, `OpResponse.Get`; `etcdserverpb.toml`: the header's, `Compare`'s and `ResponseOp`'s
  getters. **Goose issue**: an untranslated type alias (`grpc/status.Status`, of
  `internal/status.Status`) is emitted as an axiomatized type (`axiom Status : go.GoType`) while its
  users name `Status.ty`: `status.toml` now translates the alias, and `grpc/internal/status` is a
  names-only package. Package init (`Base.lean`): `closedCh` holds a fixed channel (that it is
  closed is ghost, `closedChInit`, in `isLeaseCache`).
- **The protocol premise** (`InvLeasingModel.lean`; a hypothesis, not an axiom), in words: *there
  is a history `h` of etcd's whole keyspace — its state at every revision `r ≥ 0` is `h.st r`
  (`etcdState r "" (h.st r)`, keys unique) — and for each revision `z` the session lease of the
  leasing client that committed it (`h.writer z`), such that at every revision `0 < z < 2^63`, for
  every data key `k` (outside `pfx`): (1) if `k`'s record changes at `z`, then `pfx ++ k` is absent
  at `z - 1`, or present with a lease `L ≠ 0` and `h.writer z = L` (the holder wrote it); (2) a lease
  key present at `z - 1` and at `z` with the same create revision keeps its lease.* **Changed from
  the plan**: "`k` changes only while `pfx ++ k` is absent" is false, since the holder writes `k`
  while holding its lease (its guard is its own entry's revision); the model does not record
  writers, so the premise names them (`h.writer`).
- **`leased_value_stable`** (verbatim): `(hk : LeasingDataKey pfx k) (hab : sint.Z a ≤ sint.Z b)
  (hlv : kvOf sa (pfx ++ k) = some lv) (hlb : kvOf sb (pfx ++ k) = some lb)
  (hc : lb.createRev = lv.createRev) (hw : ∀ z, sint.Z a < z → z ≤ sint.Z b → h.writer z ≠ lv.lease) :
  LeasingProtocol pfx h ∗ etcdState a [] sa ∗ etcdState b [] sb ⊢ ⌜kvOf sb k = kvOf sa k⌝`: the
  lease key present at `a` and `b` with one create revision, and no transaction of its holder in
  `(a, b]`, give `k` the same record. Proved by induction from `a` (`leased_incarnation`, pure): the
  incarnation stays present (`etcdState_create_persist` from `b`) with its lease (premise (2)), so
  no revision changes `k` (premise (1)). **`revoked_protects`**: after the lease key has the record
  `lv` at `a` (e.g. `"REVOKE"`, a put keeping create revision and lease), a transaction at `z > a`
  of anyone but the holder that changes `k` runs once that incarnation is gone at `z - 1`.
- **Contract extensions** (`InvEtcdTxn.lean`): `TxnOp.putKeep`, a put with `WithIgnoreLease`
  keeping the key's lease (`txnOpOf` maps an `ignoreLease` put with no lease to it). The range
  comparison `Compare(CreateRevision(lkey).WithRange(lend), "<", n)` needed nothing (`cmpHolds` is
  over the range's keys). Not yet: nested transactions (`OpTxn`, `serverTxn`: unit 5) and an owned
  range response (the cache mutates the acquisition's response, which the contract gives
  read-only: unit 4).
- **The lease cache** (`InvLeaseCache.lean`): `isLeaseCache lc γ pfx X` (persistent: the
  `RWMutex` guard with the lock invariant `leaseCacheInv`, and `closedChInit`),
  `leaseCacheReader` (a reader slot), the state `LeaseCacheSt` (the entries map — nil until the
  session monitor makes it — its entries `LeaseEntry` with their `*leaseKey`, revision, waiter,
  response, cached `CachedKv`s, ghost lease and acquisition record, the revocation times, the latest
  header, the frozen entries, the installed `*leaseKey`s), `LeaseCacheWf`, and `entryFacts` (each
  entry's and frozen entry's acquisition: etcd's whole keyspace at `rev` has the key's record `acq`
  and the lease key with the holder's lease, created at most at `rev`). The lock invariant is
  fractional (a reader holds `rfrac`), with the client's part `X st q` (kv.go's fields under the
  same lock, its invariant over the state). **Specs, as exact transitions** (writers take the
  client's step `X st 1 ={⊤}=∗ X (f st) 1 ∗ Q st`; readers return what the client learns of the
  state read, `lcPeek`):
  - `Add(key, resp, op)` (verbatim, abridged): with `respOwn e0 (DFrac.own 1) ∗ entryFacts pfx key
    e0 ∗ ⌜e0.rev = e0.hm.revision ∧ e0.acq = e0.kv⌝ ∗ opFullAt opv o ∗ leaseCacheReady γ` and the
    step `∀ st li ch, X st 1 ={⊤}=∗ X (st.add key {e0 with li := li, waitc := ch}) 1 ∗ Q st`, returns
    `ret` with `∃ st, □ Qr st ∗ Q st ∗ freshGetResp ret e0.hm e0.more e0.count (getResult o e0)`
    (`LeaseCacheSt.add`: the old entry frozen, a fresh `*leaseKey`, the closed channel as waiter,
    the header replaced if newer).
  - `Get(ctx, op)` (verbatim, abridged): `(nil, false)` if `isBadOpM o`; otherwise `ok = true` and
    `nil`, or `∃ st e, □ Qr st ∗ ⌜st.entries !! o.key = some e ∨ (o.key, e) ∈ st.frozen⌝ ∗
    entryFacts pfx o.key e ∗ freshGetResp ret e.hm e.more e.count (getResult o e)` (the entry as it
    is at the second read: still the key's, or evicted since).
  - `Rev`, `notify`, `MayAcquire` (read lock); `Lock`, `LockRange`, `LockWriteOps` (fresh waiter
    channels the caller closes; `WaitcOnly`), `NotifyOps`; `Evict`, `EvictRange` (`LeaseCacheSt.evict`,
    `evictRange`: frozen entries, revocation times); `Update`, `delete` (on the owned state: the
    holder's put and delete applied to the entry, `LeaseEntry.update`, `del`), `Delete`;
    `clearOldRevokes` (a goroutine: some revocation times dropped, `RevokesSub`); `leaseKey.get`
    (`getResult`, a fresh response), `isBadOp`, `inRange` (`leaseInRange`), `compareInt64`,
    `copyHeader`, `copyGetResponseMetadataOnly`, `copyKeyValue`, `closeAll`; `evalCmp`,
    `leaseCache.evalCmp`, `leaseCache.evalOps` (`InvLeaseEval.lean`: what they compute).
- **Findings**:
  - **`EvictRange` evicts the wrong key** (upstream, `cache.go`): `for k := range lc.entries { if
    inRange(k, key, end) { delete(lc.entries, key); lc.revokes[key] = time.Now() } }` deletes
    `key`, not `k`. After a failed range delete (`deleteRangeRPC`'s error path, where the delete
    may have committed), the entries in the range other than `key` stay cached: stale reads.
    Confirmed by a unit test (`EvictRange("a", "c")` leaves `"b"` cached). The spec states it
    (`LeaseCacheSt.evictRange`).
  - **`evalCmp` is not etcd's comparison** (upstream, `util.go`), so a transaction whose
    comparisons' keys are all cached is answered from the cache with the wrong `Succeeded`: on a
    key cached as absent, `result` stays `0` for every target (`CreateRevision(k) < 5` fails,
    etcd: holds; `Version(k) = 3` holds, etcd: fails; `Value(k) = ""` holds, etcd: a value
    comparison on a missing key fails); and there is no `LEASE` case (`LeaseValue(k) = 8` holds for
    a key with lease 7). Confirmed by unit tests; the spec states what it computes
    (`leaseCmpHolds`).
  - To confirm in unit 4 (kv.go): `Update` writes the op's value even for a `WithIgnoreValue` put
    (the cache then serves an empty value) and never the lease (`WithLease`: stale `Lease`); with
    two concurrent puts of one key by one client, an `Update` applied out of order bumps the version
    without the value, so a cached `Get` in between returns a version etcd never had; `waitRescind`
    returns `nil` when the watch closes without a delete event, so `revokeRange`'s bound may cover a
    lease key still present (a range delete while another client's lease protects a key).
  - `gatherOps` appends `elseOps` to `thenOps` (`append(thenOps, elseOps...)`), writing into the
    op's spare capacity: a data race if two goroutines gather one `Op` (unit 5).
- **Trust base**: two new axioms, `strings.Compare.wp_proof` (`Spec/strings/Compare.lean`: Perennial
  has no model; a Perennial trusted model and `wp_Compare` were written and proved but lost: the
  shared `.lake/packages/perennial` was reset by another worktree's Lake (`/shared/etcd-grove-mvcc`
  links its `.lake/packages` to this one) while it was at the uncommitted pin; redo it in a
  separate Perennial checkout, `lake build --packages=<file>`, as `CLAUDE.md` says) and
  `time.Time.Add.wp_proof` (`Spec/time/Time__Add.lean`: `(*time.Time).Add`, Perennial models the
  value receiver only). No `sorry`.
- **Proof-mode notes**: `wp_load` does not find a struct field's points-to inside a whole struct's
  (`AccessStrict` instances exist; the search fails): `entryOwn` is field by field and
  `leaseKey_struct` converts for `Get`'s `*li`. `wp_apply` leaves persistent premises unframed
  unless written `$H` (`$$ [$Hlc ...]`). `unfold` of a predicate also unfolds the postcondition's
  instances: `rw [entryOwn_def]` (one instance) or `iunfold X at H`.
- **Linking**: `etc/gen-link.py --leasing` writes `Link.lean` from
  `etc/link-lean-first-leasing.txt` (namespace `leasing`; a callee named like the theorem's last
  component is qualified, `EtcdGrove.leasing.wp_evalCmp`); `etc/link-lean-first-concurrency.txt`
  names clientv3's `Compare` `v3_Compare` (now ambiguous with `strings.Compare`; its `Link.lean`
  reorders two theorems). `ResponseHeader.GetRevision`'s spec takes etcdserverpb's assumptions
  (was the cache's), so both links use it. `etc/verified-code.py` counts an axiom outside a Link's
  namespace (`strings.Compare.wp_proof`) as assumed.
- **Gates**: `lake build` passes (2061 jobs); no `sorry` of this work; `etc/tcb-report.py --check`
  after `--update`: 45 axioms, 1 sorry (new: `strings.Compare.wp_proof`, `time.Time.Add.wp_proof`);
  `--collection leasing` (new): 6 axioms (`etcdState`, `etcdState_agree`, `etcdState_create_persist`,
  `etcdState_revs` and the two above), no `sorry`; the other collections unchanged;
  `etc/goose.py --check` passes (with `ETCD_SRC=/shared/etcd` until `0fc6f23b1` is pushed);
  `etc/gen-link.py --cache/--concurrency/--server/--register/--leasing` reproduce;
  `etc/verified-code.py --reuse` (with `0fc6f23b1` fetched into `.lake/go-src/etcd`):
  `client/v3/leasing` 26 verified of 67, `cache.go` 20 of 20 (231/231 lines), `util.go` 6 of 8;
  etcd 278 verified of 3599.
- **Push order**: the etcd fork's `0fc6f23b1` (to `goose-lean`), then etcd-grove `lean`
  (Perennial unchanged).

### Units 3 and 4: `txn.go` and `kv.go` (2026-10-10)

Every function of `txn.go`, of `kv.go` but the monitors (unit 5: `NewKV`, `Close`,
`monitorSession`, `monitorLease`, `rescind`, `waitRescind`, `waitSession`), and `util.go`'s
`gatherOps`/`gatherResponseOps` specified and proved, no `sorry`. Design: `decisions.md`, "Nested
transactions, owned responses, `isLeasingKV`". Files: `Proof/go_etcd_io/etcd/cache/v3/
InvEtcdTxnOwn.lean` (operation trees `OpT`, nested and owned responses, `isEtcdTxnKVO`,
`isEtcdDoKV`), `Proof/go_etcd_io/etcd/client/v3/leasing/InvLeasingKV.lean` (`isLeasingKV`,
`leasingX`, the results' predicates), lemma modules `InvLeasingKVLemmas` (the log's steps, the wait
group), `InvLeasingTxnLemmas`, `InvLeasingPutLemmas`, `InvLeasingDeleteLemmas`,
`InvLeasingGetLemmas`, `InvLeasingCommitLemmas`, `InvLeasingResults` (the pure parts of the main
theorems); `Spec`/`Proof` pairs for the 31 leasing functions, ten clientv3 functions (`OpTxn`,
`Op.Txn`, `WithKeysOnly`, `WithIgnoreLease`, `WithLastRev`, `OpResponse.Get`, the four
`OpResponse()` conversions) and three `ResponseOp` getters.

- **Model and contract extensions** (every cache/concurrency proof unchanged): `TxnOp.txn`
  (nested transactions, run at the same revision on the state the operations before them left,
  the branch chosen by their comparisons), `TxnOp.putIgnVal` (`WithIgnoreValue`), `TxnOpResult.txn`;
  `applyTxnOp`/`runOps` mutually recursive. The owned-response builder `isEtcdTxnKVO` (a second
  contract of the client's `Txn`), `isEtcdDoKV`. `HdrM`, `hdrFull`, `CachedKv`, `cachedKvOwn` moved
  from `InvLeaseCache.lean` to `InvEtcdTxnOwn.lean`. Translation: grpc `codes.Unavailable` and
  `codes.Unimplemented` (`codes.toml`), and `rpctypes.EtcdError` as a struct (`rpctypes.toml`
  imports `codes`; it was an axiomatized type whose `sorry` instances `acquire` reached).
- **Unit 5's functions are hypotheses**: their specs are written (`leasingKV__waitSession`,
  `__waitRescind`, `__monitorLease`) and `Link.lean` links every result reaching them in
  `section links_pending`, with the specs as hypotheses (`etc/gen-link.py`'s `fn: ?`;
  `etc/verified-code.py` counts them as unfinished). `Results.lean` restates the main theorems
  with the same three hypotheses.
- **The main theorems** (`Results.lean`, with `#print axioms`):
  1. **Cached reads** — `leasing_get : leasingKV.Get.spec`: `getOutcome γ pfx lo o ret err`, whose
     cache case is `getCached`: `∃ st e, leasingSeen γ st ∗ ⌜st.entries !! key = some e ∨ (key, e)
     ∈ st.frozen⌝ ∗ entryFacts pfx key e ∗ freshGetResp ret e.hm e.more e.count (getResult o e)`;
     `leasing_getResult_acq` (`e.kv = e.acq → getResult o e` is `e.acq`'s answer) and
     `leasing_cached_get_stable` (verbatim: `LeasingDataKey pfx key → e.rev ≤ b → (∀ z, e.rev < z
     → z ≤ b → h.writer z ≠ e.lease) → LeasingProtocol pfx h ∗ entryFacts pfx key e ∗ etcdState b
     [] sb ⊢ ∃ s lv, □ etcdState e.rev [] s ∗ ⌜kvOf s (pfx ++ key) = some lv ∧ lv.lease = e.lease ∧
     ∀ lb, kvOf sb (pfx ++ key) = some lb → lb.createRev = lv.createRev → kvOf sb key = e.acq⌝`).
     **Changed from the plan:** "the returned kv is `e.acq`" holds only while this client has not
     written the key since acquiring it (`Update`/`delete` change the cached key-value, theorem 3),
     hence the hypothesis `e.kv = e.acq`.
  2. **Uncached operations** — `leasing_get`'s other cases (`kvGetResult [] lo o`: the client's
     answer, linearizable unless serializable; `getAcquired`: etcd's record at a revision `≥ lo`;
     `getNotAcquired`), `leasing_put` (`putCommitted`: the put at `r ≥ lo` on etcd's state at
     `r - 1`), `leasing_delete` (`deleteCommitted`: the range deleted at `r ≥ lo`, `Deleted` its
     size), `leasing_Txn_Commit`/`leasing_Do`.
  3. **The holder's writes** — `putCommitted` includes the cache's step `leasingStep γ st
     (st.modify key (e.update (freshKv …) … hdr hm vsl o.val))` with `hm.revision = r` (consecutive
     states of the cache's log: `Update` does not change `e.rev` or `e.acq`, so "the entry's facts at
     `r`" is not what the code does); `leasing_update_tracks_put`: the bumped key-value is etcd's
     record after a plain put iff the put's lease is the cached one; `leasing_update_new_key` (a key
     cached as absent: iff no lease); `leasing_update_ignoreValue` and
     `leasing_update_out_of_order` (findings below).
  4. **Locally evaluated transactions** — `leasing_Txn_Commit : txnLeasing.Commit.spec`:
     `commitOutcome`, whose cache case `evalResult`: in a state `st` of the log,
     `leaseEvalCmps st b.cmps = (ok, true)`, `st.header ≠ null`, every operation of the chosen
     branch a cached get (`leaseEvalOk`), a fresh response with a copy of `st`'s header, `Succeeded
     = ok`, `respOpFresh` of each; otherwise exactly `txnCommitResult [] lo` of the user's
     transaction. `leasing_evalCmpM_agrees`: `leaseCmpHolds m (kvOf s m.key) = cmpHolds s m` for
     a one-key comparison not of the lease, if an absent key is not compared by value and with
     operand `0`; `leasing_leaseEvalCmps_agrees` for a transaction whose keys are cached with
     etcd's records; `leasing_evalCmpM_absent_lt`, `leasing_evalCmpM_lease`: the divergences.
- **Spec changes made while proving**: `tryModifyOp` returns `((resp, wc), err)` (Goose's tuple);
  `tryModifyOp`/`revoke` do not claim `resp ≠ null`; `Put`/`Delete` take `(opPutModel …).t = 2`,
  `(opDeleteModel …).t = 3` (the option transformers are arbitrary; as `Get`'s); `guardRanges`'s
  error case has `cmps = nil` (`guard` appends it); `eval`, `Commit` and `Do`'s transaction case
  take `len(then) + len(else) < 2^63` (`make([]Op, 0, len+len)`); `Compact`'s delegation is for a
  pair result. Contexts: writes may `revoke`, whose `waitRescind` calls `WithCancel(ctx)`, so `put`,
  `delete`, `Commit`, `Do` take `isCancelCtxCtx ctx`. User transactions are flat (`Txn().Then`
  takes plain operations).
- **Findings** (the Go code is unchanged; reproductions in an integration test, kept out of the
  tree):
  - **A write of a key not in the cache is applied twice** (`kv.go`, `put`/`delete`):
    `tryModifyOp` commits the op (guard `CreateRevision(pfx+key) < 1`) and returns a nil waiter
    channel because the key has no entry; `put`/`delete` then call `revoke` because `wc == nil`,
    which commits the op again. Confirmed: on a fresh key `lkv.Put(ctx, "k", "v")` leaves etcd at
    version 2 (create 2, mod 3); `lkv.Delete(ctx, "k")` of an existing uncached key returns
    `Deleted: 0`. The spec describes the second commit.
  - **A failed acquisition ignores the get's options** (`get`): when another client holds the
    lease, `get` returns `acquire`'s answer to `OpGet(key)`: `WithCountOnly` returns the key-value,
    `WithKeysOnly` the value, the revision filters are not applied (confirmed: count-only gives 1
    kv, keys-only the value `"v"`). `getNotAcquired` states it.
  - **`Update` and `WithIgnoreValue`, leases** (confirmed by the proof): `put`'s step caches the
    op's value (empty for `WithIgnoreValue`, where etcd keeps the old value:
    `leasing_update_ignoreValue`) and never the lease (`leasing_update_tracks_put`: a put without
    `WithLease` of a key with a lease leaves the cached lease stale).
  - **Out-of-order `Update`s** (confirmed by `leasing_update_out_of_order`): two concurrent puts
    of one key at `r1 < r2` whose `Update`s run in the opposite order leave, in between, a cached
    record with `r2`'s value and mod revision but the version incremented once: etcd never had it,
    and a cached `Get` waiting on the later waiter channel can serve it.
  - **An entry can carry an old session's lease** (`get`): the lease ID is read in `acquire`, the
    entry added later; a session reset in between (the session monitor clears the map, then sets
    a new session) leaves an entry of the expired lease, whose lease key etcd deleted, cached until
    the next reset (`monitorLease` only rescinds on a `"REVOKE"` put). Not excluded by the specs
    (the facts are about the acquisition revision); this is why `leasingX` has no "entries carry
    the current lease" invariant.
  - `waitRescind` returning `nil` without a delete event (unit 1's list): confirmed by unit 5.
- **Trust base**: three new axioms, `strings.TrimPrefix.wp_proof` (`Spec/strings/TrimPrefix.lean`),
  `errors.As.wp_proof` (`Spec/errors/As.lean`, for a `*rpctypes.EtcdError` target), both
  standard-library functions Perennial does not model (to move to Perennial), and
  `status.FromError.wp_proof` (grpc, names only; its result's `Code()` returns). The existing
  `status.Error.wp_proof` and `proto.Clone.wp_proof` are now reached. `--collection leasing`: 12
  axioms, no `sorry`.
- **Gates**: `lake build` passes (2171 jobs); `etc/tcb-report.py --check` (after `--update`: 3 new
  axioms) and every other collection unchanged; `ETCD_SRC=/shared/etcd etc/goose.py --check`;
  `etc/gen-link.py --leasing` (and the other modes) reproduce; `etc/verified-code.py --reuse
  --package go.etcd.io/etcd/client/v3/leasing`: 42 verified of 67 (`cache.go` 20/20, `util.go`
  8/8, `txn.go` 7 of 12, `kv.go` 7 of 27 verified), 17 unfinished (resting on unit 5's specs), 7
  translated (unit 5's); 509 of 921 lines verified, 917 specified; etcd 304 verified of 3599.
- **Push order**: unchanged (the etcd fork's `0fc6f23b1` to `goose-lean`, then etcd-grove).

### Unit 5: the monitors; the package (2026-10-10)

Every function of `client/v3/leasing` but `init` (not translated apart from package
initialization, `Base.lean`) is specified and proved, no `sorry`: unit 5 proved `waitSession`,
`waitRescind`, `rescind`, `monitorLease`, `monitorSession`, `Close` and `NewKV`. Files:
`Spec`/`Proof` pairs for the seven (`rescind`, `monitorSession`, `Close`, `NewKV` newly specified),
lemma modules `InvLeasingSessionLemmas` (the cache's reset `LeaseCacheSt.reset m st := { st with
emap := m, entries := ∅, frozen := st.entries.toList ++ st.frozen }`, joining the session
monitor's halves) and `InvLeasingNewLemmas` (the wait group's two owed goroutines and `Wait`, the
cache's allocation). Design: `decisions.md`, "Leasing unit 5".

- **No hypotheses left**: the link list has no `fn: ?`; `Link.lean`'s `links_pending` section is
  gone and the 17 results that took the unit-5 specs (`leasingKV.wp_Get`, `wp_Put`, `wp_Delete`,
  `wp_Do`, `txnLeasing.wp_Commit` and their callees `get`, `put`, `delete`, `deleteRange`,
  `acquire`, `revoke`, `revokeLeaseKvs`, `revokeRange`, `guard`, `guardRanges`, `revokeFallback`,
  `serverTxn`) are unconditional; `Results.lean`'s theorems take no hypotheses, with
  `leasing_NewKV`, `leasing_Close`, `leasing_waitRescind`, `leasing_monitorLease`,
  `leasing_monitorSession` added.
- **Specs**: `NewKV` (`isLeasingEtcdClient`, `closedChInit`, a thread bound) returns
  `newKVResult`: the `KV` interface value of an `isLeasingKV` with every reader slot, the "open"
  token, `leasingCloseFn` and `waitSession`'s error; `Close` needs the whole "open" token; the two
  monitors return (`True`); `waitRescind`: an error, `nil` with `leaseKeyDeleted` (the lease key
  absent at a revision above `rev`), **or `nil` with no promise** (the watch closed without a
  delete event).
- **Changes to existing specs and contracts**: `leasingXBody` holds half of `session`/`sessionc`,
  `sessionMonitor` the other half (`monitorSession` reads `session` without the lock);
  `acquireResult`'s success gives `sessionReady` (`monitorLease` calls `leaseID`), `monitorLease`
  and `waitRescind` take a revision bound (`WithRev(rev+1)`; `txnCommitOk_guarded` exports the
  header's); the range watch contract gives a delete event's `Value`/`Lease` fields readable
  (`delKvAt`; `monitorLease` reads `Value` of every event); `isEtcdLease`'s `KeepAlive` success
  gives a channel (no nil: etcd's lessor always makes one), so `NewSession`'s nil session comes
  with an error (`monitorSession` would otherwise set a nil session and close `sessionc`).
- **Findings** (reproduced by integration tests kept out of the tree):
  - **`waitRescind` returns `nil` without a delete** (confirmed, the spec's third outcome): when
    the watch channel closes while `ctx` is live (the watch canceled: its start revision
    compacted, or the client closed), it returns `ctx.Err() == nil`. A single-key write then just
    retries (its guard still fails); a **range delete goes through another client's lease**:
    `revokeRange`'s bound covers the still-present lease key, so `deleteRangeRPC`'s guard holds.
    Reproduction: A caches `k` (`lkvA.Get("k")`, A's watcher stalled so its lease monitor has not
    run); B's watcher, before its `Watch`, puts twice and compacts; `lkvB.Delete("k",
    WithPrefix())` returns `Deleted=1` while A's lease key `pfx/k` still exists, and
    `lkvA.Get("k")` returns `"v1"` though etcd has no `k`. Without the stall, A usually rescinds
    first (a race). This breaks the protocol premise (`LeasingProtocol` (1)) for leasing clients.
  - **A stale entry survives a session reset** (confirmed): `get` adds the entry after `acquire`
    commits; a reset in between (`monitorSession` clears the map before `Add`) leaves an entry of
    the old lease, whose lease key etcd deleted with the lease. `monitorLease` ignores the delete
    event (its `Value` is not `"REVOKE"`: `continue`), and a `"REVOKE"` put carrying the old
    lease (`WithIgnoreLease`) is not this client's current `leaseID()`, so it returns without
    rescinding. The entry stays until the next reset. Reproduction: A's `KV` wrapped so that after
    the acquisition's `Commit` it revokes A's session lease (as an expiry would) and waits for A's
    new session (`WithTTL(2)`); then B (`NewKV` after) puts `"v2"` (its guard holds: no lease
    key), and `lkvA.Get("k")` returns `"v1"`.
- **Trust base**: no new axiom; `--collection leasing` 12 axioms, no `sorry` (unchanged); every
  collection unchanged; `etc/tcb-report.py --check`: 48 axioms, 1 sorry (unchanged).
- **Gates**: `lake build` passes (2184 jobs); `ETCD_SRC=/shared/etcd etc/goose.py --check`;
  `etc/gen-link.py` reproduces every `Link.lean`; `etc/verified-code.py --reuse --package
  go.etcd.io/etcd/client/v3/leasing`: **66 verified of 67** (every one sorry-free; `init`, 4
  lines, not translated), 0 unfinished, 917 of 921 lines verified (`kv.go` 26/27, `cache.go`,
  `txn.go`, `util.go` all); etcd 328 verified of 3599.
- **Push order**: unchanged (the etcd fork's `0fc6f23b1` to `goose-lean`, then etcd-grove).

## Merge: the register, `node.go` and thread tokens (2026-10-10)

Merged upstream `lean` (`67c6b9292`, 43 commits: Perennial thread tokens and the cache's
wait-group counter bounded by them, `node.go` proved, the `examples/register` replicated
register, raft translated from upstream `etcd-io/raft` `40f8be7` unmodified, bbolt's
`internal/common`) into the Mutex/Election/STM line (`e5406a399`).

- **Perennial `7c93f27aa`** (`lean`): our `9276bd1ed` (`Sprintf`/`HasPrefix` models, the map-length
  bound) merged cleanly with upstream's `105fb79f5` (thread tokens, `wp_fork_tok_*`, the revert of
  our `WaitGroup.Add` assumption, `wp_slice_append_undo`, the iframe heartbeat option).
  `etc/lean-ci.sh`: 374/374; the std-lib regeneration (`GOTOOLCHAIN=go1.26.0
  etc/update-goose-new.py --compile --std-lib`) is clean; `go test ./...` in `goose/` passes.
- **Conflicts**: only the Perennial pin (`lakefile.toml`, `lake-manifest.json`: `7c93f27aa`) and
  these notes (both sides' sections; the `WaitGroup.Add` assumption marked superseded in "The cache
  as shipped"). `etc/goose.py` is upstream's (raft from `etcd-io/raft`, the `register` project) and
  already has the concurrency package and the `ab1deb078` pin; `etc/tcb-baseline.txt` is ours
  (upstream added no axiom or `sorry`). The regenerated translation is identical to the merge.
- **Thread tokens**: no proof of ours changed. Our side never touched the cache's wait-group files,
  so they are upstream's (shared writers and `cacheBound` already in, from the earlier merge).
  `wp_fork` keeps its statement (the forked thread keeps its own token, `wp_fork_tok` underneath),
  so the other `go` statements (`NewDemux`, `Session`'s keep-alive, `Observe`, `waitTillRevision`,
  the progress requestor, STM/Mutex/Election) build unchanged. The exported statements are ours but
  for upstream's thread-token changes: `New`/`newCache` assume `threadBound GF + 3 ≤ 2^31`,
  `Watch` takes and returns a `threadTok` (see "The wait-group counter and thread tokens").
- **`etc/verified-code.py`**: crashed on the `register` project (no `repo`: `fork()` now names
  its directory), and did not resolve the register's results (`register.Register.Put`: a name
  qualified by the main package's own qualifier is now looked up there).
- **Gates**: `lake build` passes (1958 jobs); `etc/goose.py --check --perennial
  .lake/packages/perennial` passes; `etc/tcb-report.py --check`: 43 axioms, 1 `sorry` (the
  baseline unchanged); per collection: btree 51 roots, no axiom; cache 152, 9 axioms, sorry-free;
  concurrency 125 (124 sorry-free), 13 axioms, 1 `sorry` (`Session.Close`); raft 213, 1 axiom,
  sorry-free; register 19, no axiom, sorry-free; server 47, 26 axioms, sorry-free. `etc/gen-link.py
  --cache`/`--concurrency`/`--server`/`--register` and `etc/gen-btree-link.py` reproduce their
  `Link.lean` (raft's is by hand since upstream's `MemoryStorage` work). `etc/verified-code.py
  --reuse`: raft 203/323 (2608 of 3646 lines), all sorry-free; etcd 243 verified, 1 unfinished, 13
  assumed of 3599 (the cache 107/107 sorry-free; `client/v3/concurrency` 59 + 1 unfinished of 62);
  register 12/12 (96 lines).
- **Push order**: Perennial `lean` (`7c93f27aa`) first, then etcd-grove `lean`.

## STM (2026-10-10)

`client/v3/concurrency`'s software transactional memory (`stm.go`) is specified and proved: every
function (28), with atomicity theorems per isolation level. Design: `decisions.md`, "STM:
a higher-order closure spec, aborts as divergence, what each isolation level gives". Files:
`client/v3/concurrency/InvSTM.lean` (vocabulary), `InvSTMAtomic.lean` (the commit key by key, the
per-level theorems), lemma modules `InvSTMMaps`, `InvSTMReads`, `InvSTMCommit`, `InvSTMRun`; `Spec`/`Proof`
pairs `NewSTM`, `NewSTM{Repeatable,Serializable,ReadCommitted}`, `mkSTM`, `runSTM`, `With{Isolation,
AbortContext,Prefetch}`, `stm__{Get,Put,Rev,Del,commit,fetch,reset}`,
`stmSerializable__{Get,Rev,gets,commit}`, `readSet__{add,first,cmps}`, `writeSet__{get,cmps,puts}`,
`isKeyCurrent`, `respToValue`, and (until the panic adoption) the trust boundary `stmPanic`,
`stmRecover`; `Results.lean`.

- **The closure** (`applySpec pfx apply Q`): for any STM with the interface's triples
  (`stmMethods`), from any state, `apply` returns an error or `nil`, and `nil` means `Q` of the
  attempt's reads and writes (`STMSt`). `NewSTM` returns an error, or `nil` with a committed attempt
  `st`, `Q st` and `stmOutcome` (`stmResult`).
- **What each level is proved to give** (`stmOutcome`: a revision `R`, the state `s` the commit ran
  on, etcd's at `R - 1` if it wrote (at `R` otherwise), and `s'`, etcd's at `R`; `STMCommitted`):
  - all levels: `s'` is `s` with the attempt's writes applied, key by key, independently of the
    write set's order (`stm_read_committed`); every read is etcd's key-value at the revision it read
    (`readFact`); `R` is at least a revision the caller had seen if the commit had an operation.
  - `SerializableSnapshot`, `Serializable` (`stm_atomicity`) and `RepeatableReads`
    (`stm_repeatable_reads`): additionally, **every read of the committed attempt is `s`'s
    key-value of its key**: the attempt ran atomically at `R` (`R - 1` → `R`). `SerializableSnapshot`
    also: no written key was modified after `first()` (the least header revision of the reads).
  - within an attempt, a key read once reads the same (repeatable reads, `GetPost`), all levels.
- **Finding: a retried serializable attempt reads from two revisions.** The serializable levels
  document "reads within the same transaction attempt return data from the revision of the first
  read". After a failed commit, the next attempt's prefetched reads are at the failed commit's
  revision `r`; if its first read is of a key not prefetched, that read is at the latest revision
  `r2` and sets the snapshot to `r2`, while later reads of prefetched keys return values at `r`. An
  attempt can then see a state that never existed (the commit fails afterwards, so serializability
  holds, but the closure ran on an inconsistent view). The specs claim no snapshot. **Reproduced**
  on upstream main (`f061acd09`) by an integration test, for both levels; fix and test on
  `/shared/etcd-stm-repro`, branch `stm-serializable-snapshot` (`479a65c65`, not pushed): after a
  failed commit, the next attempt reads at the prefetched reads' revision (`WithRev`). The existing
  STM integration tests pass with the fix.
- **Other observations** (stated, not bugs): a `RepeatableReads`/`ReadCommitted` attempt with no
  write commits an empty transaction, which etcd answers from the member's state (no recency
  promise); `fetch` of a key listed twice keeps the later response (the same key-value); after
  `apply` fails, `runSTM` returns the response field an earlier attempt left (nil in practice: a
  failed commit). A successful commit's response is not known to be non-nil from the contract
  (the spec allows nil; `runSTM` would then retry).
- **Contract changes** (`InvEtcdTxn.lean`, definitions): **read transactions** (`isEtcdReadTxnKV`,
  `readTxnResult`: gets alone, each at the current revision or its `WithRev`, serializable or not;
  `isEtcdSTMClient` bundles it with `isEtcdTxnKV`); **linearizability corrected**: `txnCommitResult`'s
  `lo ≤ r` only for a transaction with an operation that is not a serializable get
  (`TxnModel.linearizable`; etcd serves the others from the member's state; no existing proof used
  such a transaction; Mutex/Election proofs discharge it by `rfl`); a range response's header exists
  (`rangeRespAt`).
- **Trust base** (`etc/tcb-baseline.txt` after `--check --update`: 43 axioms, 1 sorry; `--collection
  concurrency` updated): a new history law `etcdState_modrev_det` (same key, same mod revision ⇒ same
  key-value); the STM's abort `stmPanic.wp_proof` (`panic(stmError{err})`, `err ≠ nil`, does not
  return) and `stmRecover.wp_proof` (`recover()` returns nil; both gone since "Panic and recover"): Perennial's `panic` is stuck and it has
  no `recover`, see decisions.md. No `sorry`.
- **Perennial `9276bd1ed`** (on `d240c1732`): `len` of a map assumes fewer than `2^63` keys (as
  `append` assumes no overflow): `wp_map_len_lt`. Needed by `make([]T, 0, len(m))` (a negative
  capacity panics).
- **Gates**: `lake build` passes (1880 jobs); `etc/tcb-report.py --check` (and per collection) passes;
  `etc/goose.py --check` passes; `etc/gen-link.py --cache/--concurrency/--server` reproduce;
  `etc/verified-code.py --reuse`: `stm.go` 28 of 28 (243/243 lines); `client/v3/concurrency` 59
  verified, 1 unfinished (`Session.Close`) of 62; etcd 243 verified of 3599.
- **Push order**: Perennial `lean` (`9276bd1ed`) first, then etcd-grove `lean`. The etcd fork's
  `goose` is unchanged; the fix branch `stm-serializable-snapshot` is for an upstream PR.

## Election (2026-10-10)

`client/v3/concurrency`'s `Election` (`election.go`) is specified and proved: all 11 functions,
with the mutex's exclusion as the election's and a pure theorem that only the leader proclaims.
Design: `decisions.md`, "Election: the mutex's leader fact, no final check, what `Observe` can
promise". Files: `client/v3/concurrency/InvElection.lean` (vocabulary, `proclaimStep_guard`),
`Spec`/`Proof` pairs `NewElection`, `ResumeElection`, `Election__*`, `Results.lean`.

- **The leader fact** is the mutex's: `leaderAt pfx key c R := lockedAt pfx key c R` (at `R`,
  under the election's prefix, `key` present with create revision `c`, no key with a smaller one).
- **Specs, in words** (the prefix `pfx` is `NewElection`'s argument plus `/`, `ResumeElection`'s
  as given; `isElection` holds the session and prefix, `electionState e s st` the fields
  `leaderKey`/`leaderRev`/`leaderSession` (nil or `s`)/`hdr`; every method runs from any state,
  knowing etcd has reached `lo`):
  - `NewElection(s, pfx)`: `isElection` and the zero state; `ResumeElection(s, pfx, key, rev)`:
    the given key and revision, `s` as leader session (nothing checked).
  - `Campaign(ctx, val)` (cancelable `ctx`): `nil` ⇒ the key `key` (under the prefix) was created
    at `rev`, had value `val` at a revision `rv` (`keyValAt`: put, found, or proclaimed), and at
    `waitDeletes`' last revision `R ≥ rv` no key under the prefix was created before `rev`:
    **`leaderAt pfx key rev R ∨ campaignLost pfx key rev R`** (the second: `key` is not there with
    create revision `rev`); the state holds the key, `rev`, the session and the transaction's header.
    Errors: some state.
  - `Proclaim(ctx, val)`: `nil` ⇒ a leader session, and (key under the prefix) etcd's states at
    `r - 1` and `r ≥ lo` are a `ProclaimStep` (`proclaimedAt`: the guard
    `CreateRevision(key) = rev` held and the key was put with `val`); `ErrElectionNotLeader` ⇒ no
    leader session (unchanged), or the guard failed (the key is not there with create revision `rev`
    at some `r ≥ lo`, `notLeaderAt`; `leaderKey` cleared); other errors unchanged.
  - `Resign(ctx)`: no leader session ⇒ `nil`, unchanged; otherwise the guarded delete, leader key
    and session cleared, and on `nil` the key is not there with create revision `rev` at the
    header's revision `R ≥ lo`.
  - `Leader(ctx)`: `nil` ⇒ the response lists one key-value, the leader at its revision
    (`leaderKvAt`); `ErrElectionNoLeader` ⇒ the prefix is empty at some `R ≥ lo`.
  - `Observe(ctx)`: an SPSC channel (`isObserveChan`) of `*GetResponse`s each listing one
    key-value `v` with `observedAt pfx v R`, the `R`s non-decreasing from `lo` (a monotone ghost
    list). `observe` is its goroutine (Perennial `go`, the channel's producer).
  - `Key`, `Rev`, `Header`: the fields.
- **What `Observe` guarantees** (`observedAt pfx v R`): `v` is in etcd's state at `R` and either
  (1) it is the leader there, or (2) `v`'s key was the leader at an earlier `R0` with create
  revision `c0`, `v` is a later incarnation of it (`c0 < v.createRev`) and no key created before
  `c0` is alive at `R`, or (3) the prefix was empty at an earlier `R0` and every key alive at `R`
  (`v` too) was created after `R0`. Responses from `Get(pfx, WithFirstCreate)` are (1); a
  forwarded put on the leader's key is (1) if it has the leader's create revision, else (2); the
  first put after an empty prefix, and puts forwarded from it, are (3). (2) and (3) are the leader
  too with etcd's real watch (gap-free: the delete before a re-creation would end the forwarding;
  the first put's batch creates every key there is), but the client contract does not promise a
  gap-free stream, nor that a key's create revision is the revision of a put event, so the spec
  says what the code gives against it.
- **Finding: `Campaign` may return `nil` without being the leader.** After `waitDeletes`, `Campaign`
  returns `nil` without looking at its own key; if the key was deleted while it waited (the
  session's lease expired or was revoked, the session closed, another `Election` value on the same
  session and prefix (which shares the key `pfx/<lease>`) resigned, or anyone deleted it), `Campaign`
  still returns `nil` once the older keys are gone, and the caller believes it is the leader while
  another candidate may be. `Mutex.Lock` had the same gap and got a final `Get` of its key
  (`ErrSessionExpired`, upstream `b14c7cd44`, 2019, "concurrency: make lock more reliable");
  `Campaign` never did. The spec states it (`campaignLost`). Not yet reproduced by a Go test;
  a reproduction: candidate B campaigns behind leader A, B's key is deleted (e.g. `client.Delete`
  or revoking B's lease) while B waits, A resigns: B's `Campaign` returns `nil`, B's key absent.
  A fix would end `Campaign` as `Lock` does (a `Get` of the key comparing its create revision).
- **Contract extensions** (definitions; `InvEtcdTxn.lean`): the single-key watch becomes a
  **range watch** (`isEtcdRangeWatcher`, in `isEtcdMutexClient`: a key or a sub-prefix under the
  client's prefix, from `rev ≥ 0`): an event is a put or a delete, its key in the range, at a
  revision `≥ rev`, `< 2^63 - 1`, reached; a delete means absent; **a put's key-value is in etcd's
  state at the event's revision**; events sorted above the stream's position (a monotone list,
  as the cache's watch); the receiver **owns the header's `Revision`** of a response with events
  (`observe` writes it). The transaction builder's `Commit` gains a triple for **any** transaction
  (`txnAnyResult`). `waitDeletes` takes `maxCreateRev ≥ 0`. `concurrencyInit` holds Election's two
  errors. `Observe` takes `lo ≥ 0` (its gets' revisions are watched from, and `Watch` needs them
  non-negative; `0` is free).
- **Other observations** (stated, not bugs): `ResumeElection` does not add `/` to the prefix
  (`NewElection` does); after a failed `Proclaim` the leader key is `""` while the leader session
  stays, so a second `Proclaim` or a `Resign` commits a transaction on the key `""` (etcd rejects
  the empty key): their specs promise nothing beyond some header then (`txnAnyResult`).
- **Gates**: `lake build` passes (1814 jobs); no `sorry` of this work; `etc/tcb-report.py --check`
  unchanged (40 axioms, 1 sorry; `--collection concurrency`: 10 axioms, 1 sorry; no new trust-boundary
  item); `etc/goose.py --check` passes; `etc/gen-link.py --cache/--concurrency/--server` reproduce;
  `etc/verified-code.py --reuse`: `client/v3/concurrency` 31 verified, 1 unfinished (`Session.Close`)
  of 62, `election.go` 11 of 11 (164/164 lines); etcd 215 verified of 3599.
- **Push order**: etcd-grove `lean` only (Perennial and the etcd fork unchanged).

## Mutex: mutual exclusion (2026-10-10)

`client/v3/concurrency`'s `Mutex` (`mutex.go`, `key.go`) is specified and proved, with mutual
exclusion as a theorem over etcd's model. Design: `decisions.md`, "Mutex: `lockedAt`, exclusion from
the two history laws". Files: `client/v3/concurrency/InvMutex.lean` (vocabulary, exclusion),
`InvMutexLemmas.lean` (the gets, the transaction, the delete, `Lock`'s last step), `Results.lean`.

- **The ownership fact** `lockedAt pfx key c R`: etcd's state at `R` under the mutex's prefix has
  `key` with create revision `c`, and no key with a smaller one. **Mutual exclusion**
  (`lockedAt_exclusion`, exported as `mutex_exclusion`): two holders `(k1, c1)` at `R1`, `(k2, c2)`
  at `R2` with `c1 ≠ c2` are never both present in etcd's state at any revision `a ≥ R1, R2`; from
  `etcdState_revs` and `etcdState_create_persist` alone. `mutex_holder_unique`: two ownership facts
  at one revision have the same create revision (`etcdState_agree`). Equal create revisions with
  different keys (two keys created by one transaction) are not excluded: the model does not record
  who wrote a key (a mutex's transaction creates one).
- **Specs, in words** (the mutex's prefix `pfx` is `NewMutex`'s argument plus `/`; `isMutex` holds
  the session and prefix, `mutexState m st` the fields `myKey`/`myRev`/`hdr`, which every method
  accepts in any state; all knowing etcd has reached `lo`):
  - `NewMutex(s, pfx)`: `isMutex` and the initial state, for a client answering for `pfx + "/"`
    (`isEtcdMutexClient`). `NewLocker`: the same, wrapped in a `lockerMutex`.
  - `tryAcquire`: `myKey` under the prefix (`Sprintf`), then the transaction: an error, or
    `acquireResp` (at `r ≥ lo`, the key with create revision `myRev ≤ r`, and the owner get).
  - `TryLock`: `nil` ⇒ `lockedAt pfx key rev r`; `ErrLocked` ⇒ the key deleted (absent at some
    `r ≥ lo`), released state; other errors, some state.
  - `Lock` (a cancelable context): `nil` ⇒ at the last `Get`'s revision `R ≥ lo`,
    `lockedAt pfx key rev R` **or `keyRecreated`** (below); `ErrSessionExpired` ⇒ the key absent at
    `R`; other errors, some state.
  - `Unlock`: `nil` ⇒ the key absent at some `R ≥ lo`, released; `ErrLockReleased` ⇒ no key;
    other errors (the delete, the `HasPrefix` check), unchanged.
  - `IsOwner`: the comparison `CreateRevision(myKey) = myRev`; `Key`, `Header`: the fields.
  - `waitDelete(ctx, client, key, rev)`: `nil` ⇒ `key` absent at some `r ≥ rev` (a delete event);
    `waitDeletes(ctx, client, pfx, n)` (`n > 0`): `nil` ⇒ at some `R ≥ lo` no key under `pfx` has a
    create revision `≤ n`.
- **Finding: `Lock` may return `nil` without the lock.** `Lock`'s last check is that `myKey`
  exists (`len(gresp.Kvs) == 0`), not that its create revision is still `myRev`. Two `Mutex`
  values of one session on one prefix share the key (`pfx/<lease>`); if the other one unlocks
  (e.g. its `Lock`'s context is canceled, which calls `Unlock`) and locks again while this one
  waits, the key is re-created with a later create revision, `waitDeletes(myRev - 1)` returns, and
  `Lock` returns `nil` while a key created between `myRev` and the new create revision may hold the
  lock too. The spec states it (`keyRecreated pfx key rev R`: present with a create revision above
  `rev`, nothing older); with one `Mutex` per session and prefix the disjunct cannot arise, but the
  model cannot express that (it does not record who writes). Not confirmed by a Go test; a fix
  would compare `gresp.Kvs[0].CreateRevision` with `m.myRev`.
- **Client contracts, extended** (definitions; `isEtcdMutexClient` bundles them):
  `kvGetResult` lists, for any get of a range under the prefix at the latest revision, etcd's
  selection (`getRespRange`: sorted, limited, filtered — `rangeKvsOk`; the single-key `Get` and
  `waitDeletes`' `WithLastCreate, WithMaxCreateRev`); `isEtcdDeleteKV` (`Delete` as a
  one-operation transaction, `deleteResult`); `isEtcdKeyWatcher` (a single-key watch from `rev`:
  an SPSC channel whose events are of the key, at revisions `≥ rev` etcd reached, and a delete
  event at `r` means the key is absent at `r`, `keyWatchRespOk`); `txnOpRespAt`'s `ResponseOp` is
  non-nil.
- **`Sprintf`**: Perennial's model returned the format string, so `myKey` would have been
  `"%s%x"`, not under the prefix (the transaction's `Under` premise and `Unlock`'s `HasPrefix` need
  it). Perennial **`d240c1732`** (on `7d0b56b07`): `fmt.Sprintf` formats `%%` and `%s` of a string
  argument exactly and makes the rest arbitrary at any other directive or with arguments left
  over (`fmt.SprintfOut`, an over-approximation); `wp_Sprintf` needs `StringArgsWf` (an argument
  of dynamic type `string` holds a string), so raft's `fmt.Sprintf.spec` gained that premise
  (`newRaft` passes `uint64`s). The mutex gets `pfx <+: myKey`; nothing about `%x` (not needed:
  exclusion does not use distinct keys). Also a trusted model of `strings.HasPrefix`
  (`wp_HasPrefix`: `decide (pfx <+: s)`; a byte loop, Goose has no string slicing).
- **The panic question** (settled since "Panic and recover": specified, a return or `panic(err)`):
  `lockerMutex.Lock`/`Unlock` call `panic(err)` on any error of
  `Mutex.Lock`/`Unlock`, which every client call allows, and Perennial's `panic` is a stuck
  expression (a WP of it is unprovable). A `sync.Locker` spec would have to promise no error, which
  is false of the client contract: they are not specified (counted "translated"), and `NewLocker`
  is.
- **Translation**: `etcdserverpb.ResponseOp.GetResponseRange` (proved), `mvccpb.Event_PUT`/
  `Event_DELETE` (constants; were axiomatized `val`s). `withTop`/`WithFirstCreate`/
  `WithLastCreate` return the slice's capacity (`waitDeletes` appends to it). concurrency's package
  facts (`concurrencyInit`): Mutex's three errors. No change to etcd's Go code.
- **Perennial tooling** (worked around in `Mutex__tryAcquire.lean`): `wp_apply` fails silently on
  a triple whose continuation's premise is a local predicate (`B b`, the transaction builder's
  state): `wp_apply_post` calls `whnfR` outside the goal's context ("unknown free variable",
  swallowed); `wp_apply_raw` works. A fix in Perennial would run it under `mv'.withContext`.
- **Gates**: `lake build` passes (1791 jobs); no `sorry` of this work; `etc/tcb-report.py --check`
  after `--update`: 40 axioms, 1 sorry (new in the trust base, all existing model axioms:
  `etcdState_revs`, `etcdState_create_persist`, `etcdState_agree`); `--collection concurrency`
  (now `Link` and `Results`): 10 axioms, 1 sorry; the other collections unchanged;
  `etc/goose.py --check` passes; `etc/gen-link.py --cache/--concurrency/--server` and
  `gen-btree-link.py` reproduce; `etc/verified-code.py --reuse`: `client/v3/concurrency` 20
  verified, 1 unfinished (`Session.Close`) of 62, `mutex.go` 9 of 11 (89/101 lines), `key.go` 2 of 2;
  etcd 204 verified of 3599.
- **Push order**: Perennial `lean` (`d240c1732`, a fast-forward of `7d0b56b07`) first, then
  etcd-grove `lean`. The etcd fork is unchanged.

## The register example: verified over raft, logically atomic (2026-10-10)

`examples/register/register.go` (a replicated register on raft's `Node`; Goose project
`register`, `Code/github_com/mit_pdos/etcd_grove/examples/register.lean`) is specified,
proved and linked: `encode`, `decode`, `fits`, `NewStorage`, `(*Storage).InitialState`,
`(*Storage).Snapshot`, `New`, `run`, `apply`, `do`, `Put`, `Get`
(`Proof/github_com/mit_pdos/etcd_grove/examples/register/`; `Link.lean` generated by
`etc/gen-link.py --register` from `etc/link-lean-first-register.txt`, raft's callees linked
in raft's `Link.lean`; `#print axioms` in `Results.lean`; collection
`etc/tcb-collections/register.txt`). No `sorry`, and no axiom of this repository: the
results rest only on Perennial's axiomatized standard-library types.

The client-facing statements (`Results.lean`; decisions.md, "The register: TaDa proposals
over raft's client log"):

- `Put(val)` (`val.length < 2^62`): `{isRegister γr γp r ∗ opCred γp 1 ∗ AU <{∃∃ x, regVal γr
  x}> @ regMask, ∅ <{regVal γr val, COMM Φ}>} … {Φ}`; `Get()` the same with `<{regVal γr x,
  COMM Φ x}>`, returning `x`. The update runs when raft commits the operation's first entry
  (the linearization point); `regMask` is everything but raft's commit invariant and the
  register's.
- `New(id, node, storage, send)`: `regInv γr`, the node's driver token at `[]`
  (`nodeDriver`), the storage's record, `isCommitted γr.raft []`, `id ↪[γr.seq] 0` and
  `sendSpec send` give `∃ γp, isRegister γr γp r ∗ opCred γp (2^64 - 1)`; `run` is forked.
- `*register.Storage` is a raft `Storage` (`register_storage_isStorage`: `regStorRec ⊢
  isStorage (regStorIface s)`, the storage model `regStorageModel`), its `InitialState` what
  `RestartNode` asks (`register_storage_initialState`).
- The ghost state: `regStorInv_alloc`, `regInv_alloc` (`Alloc.lean`), from raft's
  `ownRaftGhost_alloc` (which now also hands the client `cLog γ []` and the authorities of
  the fresh-data tokens and of the proposed slices).

Raft changes for it (commit `b856a83be`): proposals are logically atomic over a client
log (`cLog`); `node.Propose` deposits the client's atomic update, which the ghost commit
fires; `node.Step` takes a forwarded `MsgProp` (`fwdP`); `isEntryR` records each entry's
client data (`entData`). `MemoryStorage.Append` takes an empty batch without a token
(`26a6bc1d4`). Go changes (`ec7dc0a13`, `b4a362514`, minimal, `go test -race` passes):
`apply` dedups by the operation's encoding (`applied map[string]bool`), not by a sequence
number (wrong under concurrent operations of one replica); `encode` appends
`[]byte(val)`; `InitialState` returns the empty `HardState` and the voters slice itself
(no `MemoryStorage` call: `RestartNode` takes a fixed `ConfState`); `run` spins rather
than append past `2^61` entries (`fits`).

Out of scope: liveness (an operation may wait forever), the transport (`send` is a
callback that gets the messages with what `Ready` says of them), `Stop`.

## `node.go`: the concurrent `Node` (2026-10-10)

Specified, proved and linked (`Link.lean` by hand, `etc/link-lean-first.txt`; `#print
axioms` in `Results.lean`): `RestartNode`, `newNode`, `node.run`, `node.Propose` (through
`stepWait`/`stepWithWaitOption`), `node.Step` (through `step`), `node.Tick`, `node.Ready`,
`node.Advance`, and `raft.hasLeader`. No `sorry`, no new axiom: every node result rests on
exactly the axioms of the RawNode results it calls. Out of scope (their channels carry
`P := False`, never sent on): `Stop`, `Status`, `ProposeConfChange`, `ApplyConfChange`,
`Campaign`, `ReadIndex`, `TransferLeadership`, `ReportUnreachable`, `ReportSnapshot`,
`ForgetLeader`, `StartNode`/`Bootstrap`; `ctx` is `context.Background()` only.

The client-facing specs (`InvNode.lean` defines the predicates; decisions.md, "node.go"):

- `RestartNode`: `NewRawNode`'s premises plus `inv budgetN (budgetInv bud) ∗ termLB bud 0`
  ⇒ `∃ γn n, ⌜γn.raft = γ ∧ γn.bud = bud ∧ γn.stor = si ∧ nd = interface.mkOk (*node) n⌝ ∗
  isNode γn id n ∗ nodeDriver γn id n []`.
- `Propose(ctx, data)`: `{isNode ∗ data ↦*□ _} … {err, True}`.
- `Step(ctx, m)`: `{isNode ∗ netP γ id m} … {err, True}`; `netP` = `NetMsgOk id m`, the
  entries/context read-only, `isMessage` of its abstraction, and `termLB bud m.Term`.
- `Tick()`: `{isNode ∗ tickCred bud 1} … {True}`.
- `Ready()`: `{isNode} … {ch, isReadyChan γ ch}`; receiving (`node_ready_receive`) with
  `nodeDriver γ id n ds` gives `readyData γ rd ds ce es ms` (the committed entries `ce`
  with `isCommitted (ds ++ ce)`, the entries `es` with `appendRight`, the messages with
  `isRaftMsg` and `termLB` of their terms) and `nodeDriverBusy γ id n (ds ++ ce) es`.
- `Advance()`: `{nodeDriverBusy γ id n ds es ∗ appendReceipt γ.stor es} … {nodeDriver γ id n ds}`.
- The term budget (`budget_alloc N`, `N < 2^64 - 1`): `M + c < 2^64 - 1` for the bound `M`
  on every term and `c` tick credits out; `budget_spend` turns a credit and `termLB t`
  into `t + 1 < 2^64 - 1` and `termLB (t + 1)`.

`run`'s proof (`node__run.lean`, lemmas in `InvNodeRun.lean`): the loop invariant
`runHead` (the node at `ownRawNode`, `headRest`: no `Ready` out with `rof` whole, `dlv`'s
half, a stale `Ready` possibly armed (`staleOk`); or one out, `rof`'s half recording it);
after the first statement `runMid` (also a fresh `Ready`, `ownRawNodeReady`, or an idle
node with a stale one). `wp_join` twice (the `HasReady` branch, the leader check), one
`select` of eight cases. `r.Step` on the node: `wp_rn_raft_Step_net`/`_prop` (the tails of
`RawNode.Step`/`Propose`); an abandoned `Ready` stays armed
(`ownRawNodeReady_abandon_keep`, `SliceShape` to rebuild its empty messages slice).

RawNode spec changes for `node.go` (this session; commits `b68a476e6`, `7796d5635`,
`9a67d5ce5`, `23c156cfc`): `HasReady`'s `false` gives `ownRawNodeIdle` (pinned: no
message queued, no unstable entry); `RNState` lower bounds `outlb`/`unst`/`clb`
(`NGhost` in `NState`) raised by `ownRawNodeReady_abandon`; `acceptReady` takes
`ownRawNodeReady … true` (the append right handed out first, `ownRawNodeReady_handout`,
`logHanded`) and no longer returns it; `raftLog.acceptUnstable` likewise; `Advance` takes
`rs.unst = false` and returns `t = rs.term`; `raft.Step`'s `MsgStorageAppendResp` premise
has `s.gh.unst = false`; `OutTermOk`: no `MsgPreVoteResp` with pre-vote off; the raft
struct's `id` and `logger` persistent (`raftOwn`, `rawNodeOwn`: `Tick` reads them
concurrently); `newRaft` returns `s.gh = {}`.

Not checked: `etc/tcb-report.py --check` (needs a full build; the disk is short).

## bbolt: not goosable as written; the `unsafe` it needs (2026-10-10)

bbolt (v1.5.0, etcd's dependency) works by reading `[]byte` buffers (the mmap'd file, heap
pages) as structs through `unsafe.Pointer`, with `uintptr` arithmetic. Perennial's typed heap
gives that no meaning, and it leaves `uintptr ↔ pointer` stuck on purpose. `notes/bbolt-unsafe.md`
inventories every use and says what a model needs: layout constants, a byte view of
pointer-free structs (the core change), byte-offset arithmetic, slices over raw memory, and a
file-backed mmap. It also covers the fork alternative. What is goosable now:
`internal/common`'s page-id helpers are translated with bodies
(`Code/go_etcd_io/bbolt/internal/common.toml`), with package init, the sorted-list model,
`wp_slice_append_in_place` and the `Mergepgids` spec in
`{Proof,Spec}/go_etcd_io/bbolt/internal/common/`. `Mergepgids` is proved (no `sorry`; `Results.lean` prints its axioms). Most of
`internal/freelist` and `errors` are goosable too.

Toward modeling and verifying all of bbolt (`notes/bbolt-unsafe.md`, "Where Perennial stands"):
- Perennial's array allocation is a `-- TODO` that diverges (`AngelicExit`), so every proof past
  a non-empty `make` here holds vacuously (31 files use `wp_slice_make*`/`wp_slice_append`).
- Perennial has no byte-level memory and no crash semantics; both are core changes.
- Goose now folds `unsafe.Sizeof`/`Offsetof`/`Alignof`, `uintptr` constants and labeled loops
  (Perennial branch `goose-bbolt`, `ff60796`; not pinned).

## `node.go` groundwork: abandoning a `Ready`, pre-vote off, the messages' terms (2026-10-10)

Three pieces `node.go`'s proof will need (uncommitted Perennial change: `Slice.lean`).

- **Abandoning a computed `Ready`.** Perennial: `wp_slice_append_undo` (`Slice.lean`, next
  to `wp_slice_append`): `wp_slice_append`'s triple plus a wand
  `s' ↦* (vs ++ vs') ∗ ownSliceCap V s' (DFrac.own 1) -∗ sl ↦* vs ∗ ownSliceCap V sl
  (DFrac.own 1)` -- in place, the new slice is split at `len(sl)` and the rest goes back
  to `sl`'s capacity (`ownSlice_append_undo_in_place`); reallocating, the old slice and
  capacity are kept. `readyWithoutAccept` builds `rd.Messages` with it, so
  `ownRaftPhysReady` holds `Hundo` (from `rd.Messages`' contents and capacity back to
  `r.msgs`'), and `ownRawNodeReady` gained the index `ms` (the messages handed out;
  `acceptReady.spec` takes it as one more `∀`). `ownRawNodeReady_abandon`
  (`InvRawnodeReady.lean`): `rd.Messages' ↦* ms -∗ ownSliceCap … -∗ ownRawNodeReady γ rn
  id rs rd ce es ms -∗ ownRawNode γ rn id rs` (premises `rs.steps = []`,
  `rs.unpersisted = []`, `readyWithoutAccept`'s); `readyWithoutAccept.spec` returns it as
  `"Habandon"`.
- **Pre-vote off at the RawNode.** `NetFrame` and `LocalFrame` (hence `TickStep`) gained
  `s'.prevote = s.prevote` (`keep_frame`/`stepdown_frame`/`keep_frame_logst`/
  `NetFrame.of_logst` take it as an auto-param `rfl`; `hup`'s post states it);
  `ownRawNode` and `ownRawNodeReady` have the scope conjunct `"%Hpvoff" ∷ ⌜s.prevote =
  false⌝` (named so as not to clash with the proofs' `Hpv`), `ownRawNode_intro` takes it,
  and `NewRawNode.spec` requires `cv.PreVote' = false`.
- **The terms of `Ready`'s messages.** `readyWithoutAccept.spec` and `Ready.spec` return
  `"%Hmsgs_term" ∷ ⌜∀ m ∈ ms, uint.Z m.Term' ≤ uint.Z rs.term⌝`. The route, the cheapest
  sound one found: `ownRaftPhys` records of every queued message (both queues)
  `OutTermOk s.prevote s.term m` -- `s.prevote = false → Term ≤ s.term` (monotone in the
  term, `wp_store_Term` keeps it; `ownRaftPhys_intro`, the queue accessors' wands,
  `ownRaftPhys_view` and its `Hclose` carry it). `send` stamps the node's term into
  everything but a forwarded `MsgProp` (`0`) and a vote message, whose term `SendOk`'s
  vote clause now bounds: `s.prevote = false → Term ≤ s.term`. Its callers: a
  `MsgVote`/`MsgVoteResp` is of the node's term (`campaign`'s election, `Step`'s vote
  branches); a pre-vote message is sent only by `campaign`'s pre-election, which (with
  `hup`) now takes `t = campaignPreElection → s.prevote = true` (`Step`'s `MsgHup`
  branch calls it so exactly when `r.preVote`), or in answer to a `MsgPreVote`, for which
  `raft.Step.spec` now requires `s.prevote = true` (a transport premise: pre-vote
  messages reach only nodes with pre-vote on, the setting being the cluster's;
  `RawNode.Step` takes no pre-vote message, so it is vacuous there). So no ghost
  tracking of "no pre-vote message in the outbox" was needed. *Rejected*: tracking
  "no `MsgPreVoteResp` to another node in the outbox" in `ownRawNode` (needs a new
  `raft.Step` postcondition on the outbox's growth, proved per branch) or a ghost flag in
  `NState` (the same per-branch frame work).

`lake build Proof.go_etcd_io.raft.v3.Link Proof.go_etcd_io.raft.v3.Results` passes; no
new `sorry` or axiom.

## `RawNode.Ready` split: `readyWithoutAccept` and `acceptReady`, for `node.go` (2026-10-10)

`node.go`'s `run` does not call `Ready`: it calls `readyWithoutAccept`, hands the `Ready`
to the application (`readyc <- rd`), and only then `acceptReady(rd)`, with no raft step in
between. Both halves are now specified, proved and linked (Lean-first), and `Ready`'s proof
composes their specs; `RawNode.Ready.spec` is unchanged.

- `ownRawNodeReady γ rn id rs rd ce es` (`InvRawnodeReady.lean`, new): the node between
  the two -- `ownRawNode`'s conjuncts at an empty queue and nothing unpersisted, with the
  raft struct open without the outbox's contents (`ownRaftPhysReady`: `ownRaftPhys_view`'s
  output minus `r.msgs`' slice, which `readyWithoutAccept` built `rd.Messages` from in
  place), and what `acceptReady` reads of `rd`: `SoftState` `nil` or read-only, no snapshot
  nor read states, `CommittedEntries ↦*□ ce` with its capacity (for the queued
  `MsgStorageApplyResp`), `ce` the next committed entries (`logCommittedEnts`) extending
  `rs.delivered` (`isCommitted`), `es = nextUnstable`. `acceptReady` does not read
  `rd.Messages` (it reads `msgsAfterAppend` again, which the node keeps, and sets both
  outbox fields to `nil`).
- `RawNode.readyWithoutAccept.spec`: premises as `Ready`'s (`rs.steps = []`,
  `rs.unpersisted = []`); post `ownRawNodeReady γ rn id rs rd ce es` and everything the
  application gets with `rd` (`CommittedEntries`, `isCommitted γ (rs.delivered ++ ce)`,
  `Entries`, `Messages` with their capacity and `isRaftMsg`, no snapshot/read states).
- `RawNode.acceptReady.spec`: from `ownRawNodeReady … rd ce es` to `ownRawNode γ rn id
  { rs with delivered := rs.delivered ++ ce, unpersisted := es, steps := steps }` and
  `appendRight rs.storage es`.
- The proofs are the old `Ready` proof cut at the call of `acceptReady`
  (`RawNode__readyWithoutAccept.lean`, `RawNode__acceptReady.lean`; the helpers went with
  the half that uses them). `acceptReady` keeps less of `rd`: `prevSoftSt`/`prevHardSt`
  become some read-only `SoftState`/some value (no spec states them), so the joins no
  longer track `nodeSoftstate`/`nodeHardstate`. Neither half needs the `maxHeartbeats`
  bump the one proof had.
- Linked by hand in `Link.lean` (`RawNode.wp_readyWithoutAccept`, `RawNode.wp_acceptReady`,
  `RawNode.wp_Ready` from the two); `etc/link-lean-first.txt` lists the two and overrides
  `RawNode__Ready`'s Rocq callees; `Results.lean` prints their axioms.

**Open** (closed the same day: `ownRawNodeReady_abandon`, "`node.go` groundwork" above):
abandoning a `Ready` (`node.go` recomputes `rd` when its `select` takes another
case, then steps the node) has no lemma: the messages would have to go back to the node,
but `readyWithoutAccept`'s appends to `rd.Messages` may reallocate, consuming `r.msgs`'
slice. A `node.go` proof needs either such a lemma (e.g. `readyWithoutAccept` keeping
`r.msgs`' slice and handing out only a copy's worth, or a spec variant) or to treat the
outbox as handed out once computed.

`lake build Proof.go_etcd_io.raft.v3.Link Proof.go_etcd_io.raft.v3.Results` passes; no
new `sorry` or axiom (`wp_Ready`, `wp_readyWithoutAccept`, `wp_acceptReady` have no
`sorryAx`).

## The storage contract: a pending append, for `node.go` (2026-10-10)

The application may now append a `Ready`'s entries while raft keeps reading the storage
(decisions.md, "Storage: a pending append, for node.go"):

- `StorState.pend` (the batch being appended); `isStorageWith P AT DT st` answers `Term`
  and `Entries` only below the batch (`PendFrom`), `LastIndex` only with nothing pending,
  and has two laws, `Hhandout` and `Habsorb`; `StorageModel` gained `appendTok` and
  `appendedTok`. `storApp` moved to `InvStorage.lean` (`storAbsorb`, `PendOk`).
- `ownRaftLog`: `Hstor` (`lv.storage' = ls.storage`, the new `LogState.storage`) and
  `Hpend` (`PendLogOk`: the batch is `unpersisted`, at or above `unstable.offset`); the
  reseal macro tries `exact Hstor`/`exact Hpend`. `NetFrame`/`LocalFrame`, the
  `maybeAppend`/`handleAppendEntries` frames and `newRaft`'s post keep the storage.
- `raftLog.acceptUnstable` takes `ls.snap = none` and returns `appendRight ls.storage
  (nextUnstable ls)`; `RawNode.Ready` returns `"Happ" ∷ appendRight rs.storage es`.
  `ownRawNode_persist` is gone: `ownRawNode_appended` absorbs `appendReceipt rs.storage
  rs.unpersisted`. `RNState.storage` (new): `NewRawNode` returns `storage := interface.ok
  si` and takes `σ.pend = []` (as `newRaft`, `newLogWithSize`).
- `MemoryStorage`: `ownMemoryStorage ms γs σ` (names `MemStorNames`: `hist`, `done`, `ep`,
  see `InvMemstorage.lean`'s header), `memAppendTok`/`memAppendedTok`, the laws
  `memStorage_handout`/`memStorage_absorb`; the method specs take `γs` and the new
  premises (`Snapshot` no longer promises non-emptiness); `MemoryStorage.Append`
  (consumes the right, returns the receipt, under the lock) and `NewMemoryStorage` (at
  `memStorEmpty`) specified and proved, linked (`etc/link-lean-first.txt`, `Link.lean` by
  hand: `etc/gen-link.py` against the Rocq checkout no longer reproduces `Link.lean`).
  `is_Storage_MemoryStorage ms γs` is for `ownMemoryStorage ms γs σ ∗ ⌜σ.ss.index ≠ 0⌝`.

**Open**: a new `MemoryStorage` (empty snapshot) is not an `isStorage`: `maybeSendSnapshot`
follows `ErrUnavailable` too (a peer's `Next` past the log), not only `ErrCompacted`, so the
`Snapshot` clause cannot be weakened to "non-empty once compacted" without a bound
`Next ≤ lastIndex + 1` in the tracker invariant (decisions.md, same section).

`lake build Proof.go_etcd_io.raft.v3.Link Proof.go_etcd_io.raft.v3.Results` passes (and
every raft module); no new `sorry` or axiom.

## Merge: upstream's RawNode work (2026-10-10)

Merged upstream `lean` (`f380444db`: `RawNode.Step`/`Tick`/`Campaign`/`NewRawNode` proved,
the `Advance` gap closed, `raft.Step` framing, the generic TCB/verified-code scripts, their
replacement of the `Sprintf`/`Join`/`rand.Int` axioms, Perennial `f52ce33dc`) into the
cache-as-shipped and `client/v3/concurrency` line (`56084b262`). Resolutions:

- **Pin**: ours, Perennial `7d0b56b07` (contains their `f52ce33dc`; on GitHub). Their
  lakefile change was only the pin.
- **Scripts**: theirs (`etc/proof_roots.py`, `tcb-report.{py,lean}`, `verified-code.{py,go}`).
  They find the roots themselves (every `Link.lean`/`Results.lean`), so the cache's
  `Link`/`Results`, the concurrency `Link`, the btree's and the server's (its own Lean run,
  through `EtcdDeps`) are roots without a list. Two additions for the concurrency `Link`,
  whose results are in a namespace of their own: `proof_roots.link_namespace`, and
  `verified-code.py` drops that namespace before another package's qualifier
  (`concurrency.v3.wp_OpPut` is clientv3's `OpPut`; what our `NAMESPACED` did, now generic);
  and `resolve_local` takes a qualifier shared by a part's package and another (`v3`: the
  `EtcdDeps` raft and clientv3) as the other's when that package has the function (else
  clientv3's 23 linked functions counted as `EtcdDeps`'s raft). New collections
  `etc/tcb-collections/{cache,concurrency,server,btree}.txt`, and every collection's
  baseline recorded (raft: `reflect.DeepEqual` only; cache 9 axioms; concurrency 4 axioms +
  `context.wp_WithDeadlineCause`; server 26 axioms; btree none).
- **Axioms**: both sides proved `fmt.Sprintf`/`strings.Join` from Perennial's models; theirs
  (`66665c735`) also proves `rand.Int`, with `mz < 2^63` added to its spec (what Perennial's
  model covers; `lockedRand.Intn` passes an `int64`, and proves the bound), which is sound:
  taken, the axiom is gone. The merged files have one theorem each; `Base.lean` no longer has
  `isRandInitialized` (Perennial's).
- **Baseline** (`etc/tcb-baseline.txt`): the union, relative to `d45daf8ab`: +
  `etcdStep_delete_present`, `proto.Clone.wp_proof`, `sorry Perennial.context.wp_WithDeadlineCause`
  (ours), − `rand.Int.wp_proof` (theirs; their RawNode work added none); 37 axioms, 1 sorry.
- **Gates**: `etc/goose.py --check` (both translations up to date at Perennial `7d0b56b07`,
  etcd `ab1deb078`); `lake build` passes (1764 jobs), no proof fix needed; `etc/tcb-report.py
  --check` matches without `--update`; every collection `--check`s; `etc/gen-link.py
  --cache`/`--concurrency`/`--server` and `etc/gen-btree-link.py` reproduce their `Link.lean`
  (raft's needs the Rocq directory: untouched); `etc/verified-code.py --reuse`: etcd-raft
  187/323 (2322 of 3641 lines), etcd 193 verified, 1 unfinished, 13 assumed of 3599; the cache
  107/107 sorry-free; `client/v3/concurrency` 9 verified + 1 unfinished (`Session.Close`);
  `client/v3` 58; the server's `etcdserver` 6, `cindex` 8, `schema` 5. (`Compare.GetKey`, named
  `concurrency.Compare.wp_GetKey` in the concurrency `Link`, still resolves outside the totals.)
- **Push order**: Perennial `7d0b56b07` is on GitHub; the fork's `ab1deb078` on `goose-lean`;
  so etcd-grove alone.

## `RawNode.Step`: a `MsgApp` between `Ready` and `Advance` (2026-10-10)

`RawNode.Step.spec` lost its premise `m.Type' = MsgApp → rs.steps = []`: every message type
may be stepped with a `Ready` outstanding, as the concurrent `node.go` does (decisions.md,
"RawNode: the acknowledgement across a truncation"). The premise was there because the
queued `MsgStorageAppendResp` asked `e.index < offsetInProgress` (`PendingOk`), which a
truncating `MsgApp` breaks. A single-step argument does not repair it: a first `MsgApp`
may truncate the log below `e`, and a second, from a leader of a higher term that has
`e`, put it back, so the acknowledgement hits with `e.index ≥ offsetInProgress` (reachable,
Figure 8 of the Raft paper). It is still right because the storage holds the log of the
`Ready` up to `e`, which agrees with the log up to `e` by Log Matching. So:

- `LogState` gained the ghost field `stored` (what the storage holds once `unpersisted` is
  appended; `LogPersistOk`'s new last conjunct `storApp σ pend = stored`); only `Ready`
  changes it (`logAcceptUnstable`: the whole log); `newLogWithSize`/`newRaft` start it at
  the storage's entries.
- `StableOk` (`raft.Step`'s `MsgStorageAppendResp` premise, `raftLog.stableTo`'s) asks
  `stored = (sents ++ uents).take (id.index - prev.index)` instead of
  `id.index < offsetInProgress`; `persist_stable` covers both cases.
- `NetFrame` and `LocalFrame` (`raft.Step`'s postconditions) also keep `prev` and `stored`
  (`HandleAppResult`, `raftLog.maybeAppend`'s spec, `logStableTo_fields`,
  `logAcceptApplying_fields` say so; `keep_frame`/`stepdown_frame` take them as
  auto-params, `rfl`).
- `PendingOk (.appendAck t e)` is `t ≤ term ∧ plogLast prev stored = e`; `stepsOk_mono_le`
  takes `prev`/`stored` kept instead of `offsetInProgress` not moving back.
- `ownRawNode` keeps `storedRecs γ prev stored` (`PlogWf` and `logRecs` of `stored`,
  `Hstrecs`; `ownRawNode_intro` takes it); `Ready` takes it from the ghost state
  (`ownRaftGhost_storedRecs_keep`), `NewRawNode` has `stored = []`. `Advance` derives
  `StableOk` with `stableOk_of_stored` (`stored_agree`: Log Matching via `logRecs_agree`
  and `plog_match_down`).

`lake build Proof.go_etcd_io.raft.v3.Link Proof.go_etcd_io.raft.v3.Results` passes; no new
`sorry` or axiom.

## The `Advance` gap closed (2026-10-10)

`RawNode.Advance` steps any queue `Ready` left, the node's own responses included;
`RNState.advanceable` is gone (decisions.md, "RawNode: client-facing specs", "The gap --
closed"). `Advance` now takes `rs.term + 1 < 2^64` and returns the term up by at most one
(`∃ t, ownRawNode … { rs with steps := [], term := t } ∗ ⌜rs.term ≤ t ≤ rs.term + 1⌝`);
`Ready` returns no flag. Underneath: `ownRaftPhys` records `msgsAfterAppend`'s messages
(`AAMsgOk`) and the term never moves back (`raft.wp_store_Term`'s premise, threaded through
`reset`/`becomeX`/`loadState`); `SendOk`'s response clauses, `appendEntry`/`becomeLeader`
(`s.term ≠ 0`), `handleAppendEntries`/`handleSnapshot` (`m.From ≠ id`),
`stepFollower`/`stepCandidate`/`stepLeader` gained premises; `raft.Step`'s spec gained
`RespStep` in its postcondition and its `MsgPreVoteResp` no-wrap premise is only for a
pre-candidate; `ownRaftGhost_term_nz` (`Protocol/Facts.lean`). `lake build
Proof.go_etcd_io.raft.v3.Link Proof.go_etcd_io.raft.v3.Results` passes; no new `sorry`
or axiom.

## `RawNode.Campaign`, `RawNode.Step` (2026-10-09)

Both proved and linked (`RawNode.wp_Campaign`, `RawNode.wp_Step`; Lean-first, in
`etc/link-lean-first.txt`, added to `Link.lean` by hand: `etc/gen-link.py`'s output already
differed from the checked-in file, e.g. `confchange.Restore`'s callees). `RNState` gained
`term` (`ownRawNode`: `rs.term = s.term`).

- `Campaign`: for `rs.term + 1 < 2^64` (Go panics when the campaign wraps the term), `nil`,
  the term up by at most one; the rest of `rs` kept, also between `Ready` and `Advance`
  (`stepsOk_mono_le`: the queue survives a higher term).
- `Step`: for a message of replication or election (`NetMsgOk`: `MsgApp`, `MsgAppResp`,
  `MsgVote`, `MsgVoteResp`, `MsgHeartbeat`, `MsgHeartbeatResp`, with `raft.Step`'s transport
  premises; no pre-vote, snapshots, read-index or leader transfer), its `isMessage`, read-only
  entries with the capacity owned, a `Context` that is not the transfer marker: the term
  moves up to at most the message's, `err` unspecified (the guards' rejections change
  nothing). A `MsgApp` only with no `Ready` outstanding (`rs.steps = []`: it may lower
  `offsetInProgress`; premise gone 2026-10-10, see above). The guards' `IsLocalMsg`/`IsResponseMsg` (`isMsgInArray`) are
  specified to return some `bool` (for a nonnegative type: `MessageType` is an `int32`, a
  negative one panics); `isInitialized` gained their tables and the two error globals.

- `Tick` (proved and linked, `RawNode.wp_Tick`): for `rs.term + 1 < 2^64`, the term up by at
  most one, the rest of `rs` kept (also between `Ready` and `Advance`). `ownRaftPhys` now
  records `r.tick` (`Htick`: once `NState.ticking` is set, `TickFnOk r rv.tick'`: the method
  value `r.tickElection` or `r.tickHeartbeat`, not tied to the role -- both are safe in any
  role); every `becomeX` model sets `ticking`, and `NStateWf` says it is set (only
  `newRaft`'s struct before its `becomeFollower` has `r.tick = nil`). `raft.tickElection`
  and `raft.tickHeartbeat` are specified like `raft.Step` (`TickStep`: `NetFrame`, the term
  up by at most one, `offsetInProgress` not back) and proved, with `pastElectionTimeout`.

- `NewRawNode` (proved and linked, `wp_NewRawNode`): a node of a new cluster -- an empty
  storage, no `HardState`, nothing applied, synchronous writes, and `ownRaftGhost γ id
  initPState` with `isCommitted γ []` (what `ownRaftGhost_alloc` hands out) -- comes out as
  `ownRawNode` with nothing delivered, to persist or to step, at term `0`. `newRaft`'s
  postcondition gained the initial log (`prev`, `sents`, `uents`, `committed`, `applying`,
  `unpersisted`, `snap`) and gives the `validate`d `Config` back (`ConfigPreserved` gained
  `AsyncStorageWrites`); `raft.softState`/`raft.hardState` are specified and proved;
  `newRaft_post_init` moved from `Results.lean` to `Spec/NewRawNode.lean`.

Next: the `Advance` gap.

## `raft.Step` frames the log and bounds the term (2026-10-09)

Towards `RawNode.Step`/`Tick`/`Campaign` (a network message, a tick): `raft.Step`'s
postcondition gained, for every type but `MsgSnap`, `"%Hframe"` (`NetFrame s s'`:
`applying`, the pending snapshot and `unpersisted` kept; not for a
`MsgStorageApplyResp`) and `"%Hterm"` (`TermStep m s s'`: the term never moves back, a
`MsgHup` raises it by at most one, any other message but a `MsgPreVoteResp` at most to the
message's term, and `offsetInProgress` moves back only on a `MsgApp`). Every branch
lemma under `Proof/go_etcd_io/raft/v3/raft__Step/` states both (`stepPost`,
`finish_branch` carry them); `raft.hup`'s spec says the log is untouched and the term
moves up by at most one; `raftLog.maybeAppend`'s and `handleAppendEntries`'
(`HandleAppResult`) postconditions keep `applying`, `snap`, `unpersisted`. `lake build
Proof.go_etcd_io.raft.v3.Link Proof.go_etcd_io.raft.v3.Results` passes; no `sorry` added.

## Perennial `f52ce33dc`; retargeting raft to upstream (2026-10-09)

Re-pinned to Perennial `f52ce33dc` (`lean`: `79adaac01` below merged with the Goose
work for upstream raft, `b0293f805`/`d57475ff3`: each loop iteration has its own iteration variables where that
is observable, range loops over arrays, `fallthrough`, a `break` in a `switch`/`select`
case ends that statement, function-local types, an empty void function body is
`return: #()`). Regenerated: `Code/go_etcd_io/raft/v3.lean` (the `trace*` stubs; `node.run`'s
`select` is wrapped in `catchBreak`; `entsSize`'s range variable `ent`, whose address
`ent.Size()` takes, is allocated in the body), `Code/go_etcd_io/etcd/cache/v3.lean`
(`demux.resyncLaggingWatchers`'s `w, nextRev`, captured by the `AscendGreaterOrEqual`
callback, allocated in the body) and `cindex.lean` (empty bodies). Proofs: `entsSize` and
`demux.resyncLaggingWatchers` drop the per-iteration variables from their loop invariants
(each iteration allocates them afresh); nothing else changed.

**Retargeting raft to upstream `etcd-io/raft` (2026-10-10: done, to `40f8be7`).** Raft is
now goosed from upstream `etcd-io/raft` unmodified, at `40f8be7` (2026-04-15), the last
commit before raftpb moved to protobuf-go v2; the fork `upamanyus/etcd-raft` is gone from
`etc/goose.py`. Relative to the fork's translation: `JointConfig.IDs` ranges over the array
value with `array.forRange 2` (its proof is a `wp_for` over the index, unrolled for the two
elements, with the old map-range proof inside); `ConfChange`/`ConfChangeSingle`'s `NodeID`
and `ID` fields are `NodeId`/`Id` (`addNodeCC` in `InvConfchange.lean`); the enum constants
`MessageType_*`, `EntryType_*`, `ConfChangeType_*`, `ConfChangeTransition_*` are translated
(raftpb.toml), with `MsgHup`-style aliases; `MajorityConfig.String`/`Describe` format ids in
hex (not proved). No spec changed. The original goal was upstream `1c0011d2` (2026-09-22):
(upstream `24643b3` of 2026-03-10 plus two edits in `quorum/`: `JointConfig.IDs` ranging
over the two configs by index, and `MajorityConfig.Describe`'s local type `tup` hoisted;
the new Goose translates both as written). Between those two upstream commits raft moved
raftpb from gogoproto to protobuf-go v2 (March to May 2026: `Entry`, `Message`, `Snapshot`,
`HardState`, `ConfState`, `ConfChange*` are passed as pointers, their fields are pointers read
through `GetXXX` getters, `[]pb.Entry` is `[]*pb.Entry`, `proto.Clone`/`Marshal`/`Unmarshal`/
`Size` replace the generated methods). The mechanics work: branch
`raft-upstream-1c0011d2-wip` has `etc/goose.py` pointed at upstream `1c0011d2` (with
`google.golang.org=` as a Lean root, so raft's `proto` import is the names-only
`Code.google_golang_org.protobuf.proto` of the etcd project) and a new
`Code/go_etcd_io/raft/v3/raftpb.toml` (everything but the protobuf runtime plumbing), and
the regenerated `Code/` and `GeneratedProof/` build against Perennial `d57475ff3`. The proofs
do not: 154 Spec/Proof files (36k lines) mention the raftpb types as values (`List
raftpb.Entry` in `LogState`, `absMsg`, ...), so the retarget is a redesign of the raft proof's
entry/message/snapshot ownership (heap entries shared between the log, messages and
`Ready`), not an adaptation. The last upstream commit before the migration, `40f8be7`
(2026-04-15), translates unmodified with the new Goose and differs from the fork's
translation only by the gogoproto option cleanups (`NodeID` to `NodeId` in `ConfChange*`,
the `MessageType_*`/`EntryType_*` enum constants with `MsgHup`-style aliases) and the
Goose changes above: that is the cheap retarget, taken on 2026-10-10 (above). The retarget to
`1c0011d2` stays parked on that branch.

Gates (2026-10-09): `lake build` passes (1659 jobs); `etc/goose.py --check` passes;
`etc/tcb-report.py --check` matches the baseline. Building against a Perennial checkout
other than `.lake/packages/perennial` (other worktrees share it): `lake build
--packages=<override manifest>`, and `LAKE_OPTS=--packages=<file> etc/tcb-report.py`.
`etc/goose.py` needs a Go toolchain that can load etcd (`go 1.27`): with an older default
`go`, `GOTOOLCHAIN=go1.27.1 etc/goose.py ...`.
## Perennial `7d0b56b07`: Goose with per-iteration loop variables (2026-10-09)

Perennial `lean` at **`7d0b56b07`**: our `9092f8eaa` merged (cleanly) with upstream's
`724880f7b` (Goose: range over arrays, `fallthrough`, `break` out of `switch`/`select`, local
types), `a938c20b1` and `3a79c5282` (each loop iteration has its own iteration variables),
`79adaac01` (`context.wp_WithCancel` builds again) and `d57475ff3` (only the local types of
translated functions). In Perennial: `etc/lean-ci.sh` 372/372; the std-lib regeneration
(`GOTOOLCHAIN=go1.26.0 etc/update-goose-new.py --compile --std-lib`) changes nothing; `go test
./...` in `goose/` passes. No Perennial follow-up commit.

- **The generated code** (`etc/goose.py`; `ab1deb078` from `--src etcd=/shared/etcd`, not yet
  on `goose-lean`): 3 files (`Code/`; `GeneratedProof/` and `EtcdDeps/` unchanged), +20/−29.
  - *Per-iteration loop variables*: Goose allocates a loop variable per iteration only where
    sharing it would be observable (captured by a function literal, or its address taken,
    including a pointer-receiver call); every other loop keeps one shared cell, unchanged. Two
    loops here: raft's `entsSize` (`ent.Size()` has a pointer receiver: `ent` is now allocated
    in the body from `$value`) and the cache's `demux.resyncLaggingWatchers` (`w` and
    `nextRev`, captured by the `AscendGreaterOrEqual` callback, now allocated in the body from
    `$key`/`$value`, no longer stored at the end of each iteration).
  - *`break` out of `select`*: `node.run`'s `select` is wrapped in `catchBreak`. Its
    `case m := <-n.recvc` filters a response from an unknown peer with `break`, which the old
    translation took as breaking out of the `for` loop (ending `run`): a mistranslation, now
    fixed. `node.run` has no spec here, so nothing depended on it.
  - *Empty function bodies* end in `doReturn #()` instead of `doExecute #()`: raft's 11 `trace*`
    no-ops (`state_trace_nop.go`), `cindex`'s `fakeConsistentIndex.UnsafeSave`/`SetBackend`.
    `wp_start` handles both; no proof changed.
  - Nothing translated here uses `fallthrough`, array ranges or local types. The fork's "Avoid
    fallthrough" commit (`client/v3/leasing/kv.go`) is in a package not translated here: it
    does not matter for this repository (it could be reverted now that Goose translates
    `fallthrough`).
- **Proofs**: 2 fixed, both loop invariants that named the shared cell: `entsSize.wp_proof`
  (drop `ent` from the `wp_for` invariant; each iteration's fresh cell is passed to
  `Entry.Size`) and `demux.resyncLaggingWatchers.wp_proof` (drop `nextRev`, `w` from the
  `wp_map_for_range_mut_keys` invariant and from its three re-establishments). No spec, no
  `Link.lean` changed.
- **Gates**: `lake build` passes (1740 jobs); `etc/goose.py --check --src etcd=/shared/etcd
  --perennial .lake/packages/perennial` passes; `etc/tcb-report.py --check` matches without
  `--update` (38 axioms, 1 sorry); `etc/gen-link.py --cache`/`--concurrency`/`--server` and
  `etc/gen-btree-link.py` reproduce; `etc/verified-code.py --reuse` unchanged: Raft 175/323,
  cache 107/107 sorry-free, `client/v3/concurrency` 9 verified + 1 unfinished, server 19, etcd
  193 verified, 1 unfinished, 13 assumed of 3599.
- **Push order**: Perennial `lean` (`7d0b56b07`) first; the etcd fork's `ab1deb078` to
  `goose-lean` (if not pushed yet); then etcd-grove `lean`.

## Merge: the cache as shipped and client/v3/concurrency (2026-10-09)

Branch `cache-as-shipped` (the four commits of "The cache as shipped", made on `d45daf8ab`) merged
into the concurrency work ("client/v3/concurrency", below). Conflicts only in `etc/goose.py` (the
etcd pin: **`ab1deb078`**, which is `207c8f747` plus the two cache reverts, with the concurrency
side's packages and roots) and this file (both sections kept); `InvEtcd.lean`, `InvCache.lean`,
`InvNew.lean`, the Perennial pin (**`9092f8eaa`**) and `etc/tcb-baseline.txt` merged cleanly
(`isEtcdClient` is the concurrency side's: the cache side did not change its shape). Rerunning
`etc/goose.py` changed no generated file. No proof needed a fix: `Session`'s proofs use none of
the store or loop predicates the cache side redesigned.

- **Gates**: `lake build` passes (1740 jobs); `etc/goose.py --check --src etcd=/shared/etcd
  --perennial .lake/packages/perennial` passes; `etc/tcb-report.py --check` matches the merged
  baseline without `--update`: 38 axioms (the cache's 36 + `etcdStep_delete_present` +
  `proto.Clone.wp_proof`), 1 sorry (Perennial's `context.wp_WithDeadlineCause`);
  `etc/gen-link.py --cache`/`--concurrency`/`--server` and `etc/gen-btree-link.py` reproduce
  their `Link.lean`; `etc/verified-code.py --reuse` (`ab1deb078` fetched into
  `.lake/go-src/etcd`): cache 107/107 verified, sorry-free, 1202/1202 lines;
  `client/v3/concurrency` 9 verified, 1 unfinished (`Session.Close`) of 62; etcd 193 verified
  (all sorry-free), 1 unfinished, 13 assumed of 3599; Raft 175/323.
- **Push order**: Perennial `lean` (`9092f8eaa`) first; then the etcd fork's `ab1deb078` to
  `upamanyus/etcd` `goose-lean` (a fast-forward of `6ab61a1c7` through `207c8f747`); then
  etcd-grove `lean`.

## The cache as shipped: shared writers, a revision bound, no code change but the fix (2026-10-09)

Rule (the user's): no change to etcd's code unless it fixes a bug. The fork's fix branch
`cache-ready-after-retry` had three commits; only `64313a1f8` (`Init` before the store watcher
is registered: finding 2) fixes a bug. The verified code is now `upamanyus/etcd` branch
`goose-revert` at **`ab1deb078`** (on `goose` `207c8f747` = `goose-lean` `6ab61a1c7` plus the
concurrency package's Gooseable commit): two plain reverts, `43c553f32` (of `a7de41a72`: `watch`
waited for `applyStorage`, the goroutine left the wait group) and `ab1deb078` (of `21ac13e0d`: the
upstream watch in a child context canceled on return), so `cache/cache.go` is upstream main plus
the readiness fix and the Gooseable changes. `go build ./...`, `go vet ./cache/`, `go test
./cache/ -race -count=2` pass (`TestCacheReadyAfterWatchRetry`, from the fix, passes).
`etc/goose.py` pins it; only `Code/go_etcd_io/etcd/cache/v3.lean` changed (`watch`,
`watchEvents`). Design: `decisions.md`, "No code changes unless a bug".

- **Perennial `9092f8eaa`** (branch `wg-assume`, on `56b1b6651`; push Perennial first;
  **the `WaitGroup.Add` assumption is superseded** by the thread-token bound, Perennial `105fb79f5`,
  see "The wait-group counter and thread tokens"):
  `614fa61d3` **`WaitGroup.Add`'s counter overflow is a model assumption**: `WaitGroup.Add` is a
  trusted model (`TrustedCode/sync.lean`), Goose's translation of Go's `Add` verbatim but for the
  atomic add, which is `waitGroupStateAddAssume` (a compare-and-swap loop that `assume`s the
  `int32` counter plus the delta is at most `2^31 - 1`; with the assumption true, Go's atomic
  add); `wp_Add`'s caller bounds the counter only from below and the commit gives it the
  no-overflow fact; `Add`'s and `Done`'s atomic updates open at `⊤ \ ↑N` (as `Wait`'s). The
  shipped loop `Add(1)`s per iteration with each `Done` in a goroutine the demonic scheduler may
  delay for ever: without the assumption it is unprovable. `9092f8eaa`: a token-free writer
  spec for `RWMutex` (`isRWMutexGuard`, `wp_Lock_guard`, `wp_Unlock_guard`): any number of
  goroutines write the store. `etc/lean-ci.sh`: 369/369.
- **The store has shared writers** (`InvStore.lean`). No `storeWriter` token: the lock
  invariant holds the whole state (and the newest snapshot's counter `γ.snap`, `Synced`, the
  latest tree's lending flag); the latest tree lives in an invariant of its own
  (`storeTreeInv`, in `isStore`), borrowed under the write lock; writers use the persistent
  `isStoreWriter`. The new statements:
  - `store.Restore.spec`: `{{ isStore ∗ isStoreWriter s γ cap E R ∗ kvs… ∗ P ∗
    ⌜∀ r, (P ∗ R r ⊢ ⌜r ≤ rev⌝)⌝ ∗ □ E rev (restoreMap kvs) ∗ □ R rev }} s.Restore(kvs, rev)
    {{ kvs… ∗ P ∗ storeRevLb γ rev ∗ storeSnapLb γ rev }}` (for whatever state it finds; `P`
    dominates every revision the store can be at).
  - `store.Apply.spec`: `{{ isStore ∗ isStoreWriter ∗ respAt resp r ∗ ⌜EvRevSorted⌝ ∗
    storeSnapLb γ lo ∗ ⌜0 ≤ lo⌝ ∗ storeApplyCert cap E R lo r }} s.Apply(resp) {{ err;
    ⌜r.canceled ∧ err ≠ nil⌝ ∨ ∃ st, ⌜StoreInv cap st ∧ st.Synced ∧ ∃ Y, newest snapshot of st is
    (Y, st.latest) ∧ lo ≤ Y⌝ ∗ storeRevLb γ (applyResp cap st r).1.latestRev ∗
    monoNatLbOwn γ.snap (storeSnapKey (applyResp cap st r).1) ∗ ⌜err iff (applyResp cap st
    r).2⌝ }}`; `storeApplyCert cap E R lo r` is the caller's persistent certificate for any
    state `st` whose newest snapshot `(Y, st.latest)` is at or above `lo`, given `□ E Y st.latest`:
    `Apply` changes nothing or succeeds, and its snapshots and revisions are certified.
  - `newStore` returns `isStoreWriter` (persistent) instead of the writer.
- **The revision bound** (`InvCache.lean`, `CacheFields.γb`): a cache-level `monoNat` the watch
  loop alone advances (`cacheBound cf B`: the authority at `B`, with `etcdReached B`), before
  each `Broadcast` to the response's revisions (`respCert_cacheCert`) and before each `Restore`
  to the `Get`'s revision. The store's `R` is `cacheRev cf` (`etcdReached` and at most the bound),
  the demux's certificate `cacheCert cf` (`etcdStepCert` and at most the bound): every revision
  the store can reach, now or by a pending drain, is at most the bound, and the `Get`, from
  `etcdReached` of the bound, returns at least it (`cacheBound_dom`: `Restore`'s dominance).
- **A new model axiom, `etcdStep_delete_present`** (`InvEtcd.lean`): a delete event of a step
  removes a key present when it is applied (etcd emits no delete event for a missing key). The
  store's `Apply` fails on a delete of a missing key; with one writer a failure was followed by
  a `Restore`, but with shared writers another writer could build on the half-applied map. With
  the axiom, a batch etcd certifies applies to a map that is etcd's state before it
  (`isEtcdKvs_applyBatch_ok`, `applyEvents_ok`), so `Apply` never fails on a response it
  accepts and the store stays synced. Reached by `cache_New` only (the watch loop).
- **The loop as shipped**: `applyStorage` (any goroutine; `storeSnapLb (s - 1)`; returns
  `True`), `get` (`cacheBound B` in, `cacheBound R` out, `R ≥ B`), `watch` (`cacheWriter`, the
  wait-group token `cacheWgRunning`, `storeSnapLb R`, `0 < rev ≤ R + 1`; per iteration
  `wp_cacheWg_AddRunning` and a goroutine with a deferred `Done`; no wait; `applyErr` a handoff
  carrying nothing), `getWatch`, `getWatchLoop` (the wait-group token in and out), `watchEvents`
  (no `WithCancel`: the internal context; raises the bound before `Broadcast`).
- **Changed statements** beyond dropping the writer token: `applyStorage`, `get`, `watch`,
  `getWatch`, `getWatchLoop`, `Restore`, `Apply`, `newStore` (above); `RequestProgress`'s demux
  handle is `cacheCert cf`'s (was `etcdStepCert cf.pfx`'s); definitions behind unchanged
  statements: `isCacheFields` (the demux at `cacheCert`, `isStoreWriter`), `cacheReader` (`R =
  cacheRev`), `cacheWatchSlot` (the demux handle at `cacheCert`), `cacheWriter` (the bound's
  authority), `cacheWgInv` (spent budget tokens apart from the counter), `isStore` (the tree
  invariant), `StoreNames` (`snap`, `tree`). **`Get`'s, `Watch`'s and `New`'s statements are
  unchanged** (`Watch`'s channel stays `etcdStepCert`'s: the demux's publications are weakened
  to it, `demuxPubBody_cacheCert`), and so is every `Results.lean` statement.
- **`Close`**: `Wait` returns once the counter is zero, i.e. once every goroutine added to the wait
  group has run its `Done`, the drained `applyStorage` goroutines of every iteration included;
  its postcondition is unchanged (the "open" token; nothing comes back through the wait group).
- **Gates** (2026-10-09): `lake build` passes (1660 jobs), no `sorry` of this work;
  `etc/tcb-report.py --check` after `--update`: 37 entries, all axioms, 0 sorries (new:
  `etcdStep_delete_present`; the WaitGroup assumption is trusted code, not an axiom, and adds
  nothing); `Results.lean`'s `#print axioms`: unchanged but for `cache_New`, which gains
  `etcdStep_delete_present`; `etc/goose.py --check --src etcd=/shared/etcd-cache-revert
  --perennial .lake/packages/perennial` passes; `etc/gen-link.py --cache` reproduces `Link.lean`;
  `etc/verified-code.py --reuse` (with `ab1deb078` fetched into `.lake/go-src/etcd`): the cache
  107 of 107 verified, sorry-free, 1202 of 1202 lines; Raft 175/323, etcd 161 verified, 13 assumed.
  Push Perennial (`wg-assume`, `9092f8eaa`) first; the fork's `goose-revert` (`ab1deb078`).

## The wait-group counter and thread tokens (2026-10-10)

Perennial `105fb79f5` (merged into `lean`) reverts `614fa61d3`: `WaitGroup.Add` is
Goose's translation again and `WaitGroup.wp_Add` asks its caller to bound the new counter by
`2^31` (two `Add(1 << 30)` calls panic in Go, so the overflow was reachable and must not be
assumed). The bound is discharged with Perennial's **thread tokens** (`GooseLang/Threads.lean`;
`docs/PERENNIAL_PROOF_REFERENCE.md`, "Thread tokens"): the trusted semantics counts the live
threads (`GlobalState.threads`; `Fork e` spawns `e ;; ThreadExit`), the bounded layer has a
thread fuel next to the step fuel, and `threadToks n ⊢ n < threadBound GF` for a bound `T`
fixed at adequacy time (`goose_adequacy N T`, about executions along which fewer than `T` threads
are live). `Fork` hands the forking thread a token (`wp_fork_tok`, `wp_fork_tok_self`,
`wp_fork_tok_body`) and the forked thread returns one at its exit.

- **`cacheWgInv`** (`InvCache.lean`): the counter is `k + d`; `k` goroutines (`cacheWgRunning`,
  `γwr`) have their **thread token deposited** in the invariant (`threadToks k`), `d` goroutines
  (`cacheWgRunningOwed`, `γwo`) keep their own token and spent a capacity (`cacheWgOwedCap`,
  `γwc`; `cacheWgOwedMax = 3`: the resync loop, the watch loop, the progress requestor, for the
  cache's lifetime). `k` tokens give `k < threadBound GF`, so the counter is below
  `threadBound GF + 3`; **`New` assumes `threadBound GF + cacheWgOwedMax ≤ 2^31`** (a pure
  premise of `New.spec`/`newCache.spec`, kept in `isCacheFields` as `%Hthreads`): fewer than
  `2^31 - 3` threads are live at once. The `cacheWgBudget` slots are unchanged.
- **Who deposits.** The watch loop (`getWatchLoop`, `getWatch`, `watch`: `cacheWgLoopRunning`,
  its owed running token and its own thread token) deposits its token at each iteration's
  `Add(1)` (`wp_cacheWg_AddRunning`) and gets a fresh one at the `go` statement
  (`wp_fork_tok_self`); the iteration's goroutine exits with the token its deferred `Done`
  returns (`wp_cacheWg_Done`). `Watch` (`threadTok` in and out of its spec) does the same with a
  budget slot (`wp_cacheWg_Add`). `NewDemux`'s slot protocol and `newCache`'s `Add(2)` start the
  three owed goroutines (`wp_cacheWg_AddOwed`, `wp_cacheWg_Add2`; `wp_cacheWg_DoneOwed` returns
  the capacity); `New`'s spec needs no token of its own.
- **Changed statements**: `New`, `newCache` (the thread-bound premise), `Watch` (`threadTok`),
  `watch`, `getWatch`, `getWatchLoop` (`cacheWgLoopRunning` for `cacheWgRunning`). `Close` and
  the delivery theorem are unchanged.
- **Trust base**: the model assumption is gone from Perennial's trusted code; what replaces it is
  the semantic thread count and thread fuel (Perennial's `Lang.lean`, `BoundedLang.lean`,
  `Threads.lean`, `Lifting.lean`, `Adequacy.lean`; see Perennial's README) and the adequacy
  hypothesis `RealThreadsBelow T`, instantiated here by `New`'s premise. `etc/tcb-report.py
  --check` is unchanged (the premise is a hypothesis of a spec, not an axiom).

## client/v3/concurrency: the transaction and lease model, Session (2026-10-09)

etcd's model now has transactions and leases, `go.etcd.io/etcd/client/v3/concurrency` is
translated with bodies, and `Session` (`session.go`) is proved: 9 of its 10 functions
verified, `Close` unfinished only through Perennial's `wp_WithDeadlineCause` `sorry`. Design:
`decisions.md`, "The transaction model: sequential ops at one revision, per prefix; leases
without liveness; the create-revision persistence law".

- **Translation** (commit "Translate client/v3/concurrency ..."): `etc/goose.py` pins etcd at
  `207c8f747` = `goose-lean` (`6ab61a1c7`) + one **Gooseable** commit (not pushed; push it to
  `upamanyus/etcd`'s `goose-lean` first): concurrency calls the methods it uses of `*Client`'s
  embedded interfaces through the field (`client.Lease.Grant(...)`, `client.KV.Txn(...)`, ...),
  because Goose translates a promoted method as `MethodResolve (*Client) "Grant"` with no
  unfolding for it; and binds `wr.Events` to a `[]*mvccpb.Event` (the alias issue of
  `5ae038f0f`). `client/v3.toml` gained `Client.Ctx`, `Client.GetLogger`, the comparison
  builders, `OpPut`, `OpDelete`, `WithLease`, `WithSort`, `WithFirstCreate`, `WithLastCreate`,
  `withTop`, `WithMaxCreateRev` (and imports proto, fmt); `etcdserverpb.toml` `Compare` and its
  oneof wrappers, `Compare.GetKey`, `TxnResponse`, `ResponseOp` and its wrappers, `PutResponse`,
  `DeleteRangeResponse`, `LeaseRevokeResponse`; `zapcore.toml` imports `time` and `io` (so
  `zap.Logger`'s field types are no longer axiomatized types with `sorry` instances).
- **The model** (`cache/v3/InvEtcdTxn.lean`): `CmpModel` (`client/v3/InvCmp.lean`), `cmpHolds`
  (etcd's `applyCompare`; a value comparison on a missing key **fails**, a correction of the
  plan), `TxnOp` (get/put/delete), `TxnModel`, `applyTxnOp`/`runOps`/`runTxn` (ops in order, each
  on the state the previous left, at one revision), `txnWrote`, `rangeKvsOk` (a get's response:
  sorted, limited, as a relation since etcd's sort is unstable). The client's contracts, as
  definitions: `isEtcdTxnKV kv pfx` (`kv.Txn(ctx)` returns a builder with an abstract state;
  `If`/`Then`/`Else` append; `Commit` returns `txnCommitResult`: an error, or a response at
  `r ≥ lo` reached, with a state `s` such that the response is `runTxn r s t`, and `s` at `r - 1`
  and the result at `r` if it wrote, `s` at `r` otherwise) and `isEtcdLease l` (`Grant`: an ID
  `≠ NoLease`; `KeepAlive`: a channel of which nothing is promised, `isChanAny`; `Revoke`).
  `isEtcdClient` gained `isEtcdTxnKV` and `isEtcdLeaseClient`. `OpFull` gained `val`,
  `rangeEndSet`, the sort option, `ignoreValue`/`ignoreLease` (`InvOp.lean`).
- **New axioms** (`etc/tcb-baseline.txt` after `--update`: 37 axioms, 1 sorry):
  `proto.Clone.wp_proof` (protobuf's deep copy of a `*pb.Compare`, the comparisons' trust
  boundary) and Perennial's `sorry` `context.wp_WithDeadlineCause` (reached by `Session.Close`
  through `WithTimeout`). The two history laws `etcdState_revs` and `etcdState_create_persist`
  are axioms in `InvEtcdTxn.lean` but no result uses them yet (the recipes will), so the
  baseline, which lists what results reach, does not show them.
- **Proved**: the clientv3 builders (`Value`, `Version`, `CreateRevision`, `ModRevision`,
  `LeaseValue`, `Compare`, `Cmp.WithRange`/`WithPrefix`/`Clone`/`ensureCompare`, `cloneCompare`,
  `mustInt64`, `mustInt64orLeaseID`, `OpPut`, `OpDelete`, `WithLease`, `WithMaxCreateRev`,
  `WithSort`, `withTop`, `WithFirstCreate`, `WithLastCreate`, `Client.Ctx`, `Client.GetLogger`,
  `pb.Compare.GetKey`); `Session`: `NewSession`, `Client`, `Lease`, `Ctx`, `Done`, `Orphan`,
  `Close`, `WithTTL`, `WithLease`, `WithContext` (`client/v3/concurrency/InvSession.lean`:
  `isSession s γ client id`, persistent; `sessionDone s γ`, persistent once `donec` is closed).
  `WithSort`/`withTop` take `¬ (target = SortByKey ∧ order = SortAscend)` (decisions.md: the
  closure writes its captured `order` in that case, a race). `NewSession` takes the resulting
  options' context to be a `*cancelCtx` (Perennial's `wp_WithCancel`).
- **Linking**: `etc/gen-link.py --concurrency` writes
  `Proof/go_etcd_io/etcd/client/v3/concurrency/Link.lean` from
  `etc/link-lean-first-concurrency.txt` (results in the namespace `concurrency`, clientv3's with
  `v3.`); `etc/tcb-report.lean`'s default roots, `etc/tcb-report.py` and `etc/verified-code.py`
  include it. The clientv3 specs take clientv3's `Assumptions` (were the cache's), the zap specs
  import the cache's `Base` (were the server's `InvApplier`), and the proto/protoreflect
  package-init instances moved from the server's `BaseApply` to the cache's `Base`.
- **Gates**: `lake build` passes (1740 jobs); `etc/goose.py --check` passes (with
  `ETCD_SRC=/shared/etcd` until `207c8f747` is pushed); `etc/tcb-report.py --check` matches the
  updated baseline; `etc/gen-link.py --cache`/`--server`/`--concurrency` reproduce their
  `Link.lean`; `etc/verified-code.py --reuse` (with `207c8f747` fetched into `.lake/go-src/etcd`
  from `/shared/etcd`): `client/v3/concurrency` 9 verified, 1 unfinished (`Session.Close`) of 62,
  `session.go` 63 of 70 lines; `client/v3` 58 verified of 337; etcd 193 verified of 3599; cache
  107/107 unchanged; Raft 175/323 unchanged.
- **Next**: `Mutex` (`mutex.go`), then `Election`, `STM`, on `isSession` and the transaction
  contract; they will need `etcdState_create_persist`. Push order: the etcd fork's `207c8f747`
  (to `goose-lean`), then etcd-grove (Perennial is unchanged).

## Perennial models of `fmt.Sprintf`, `strings.Join`, `crypto/rand.Int` (2026-10-09)

The three standard-library axioms of the Raft proof are theorems now, from trusted models
in Perennial (`Perennial/TrustedCode/{fmt,strings,crypto/rand}.lean`, wired through
`trusted` in the packages' `.toml`; Perennial `00b3c10ea`, merged with upstream's
`3ae7dc6a4` as `56b1b6651`; pinned at `79adaac01`, which also fixes `context.lean`'s
`wp_withCancel`: at `3ae7dc6a4` `Perennial.Proof.context` does not build, so neither does
`lean` at `55d80f991`):

- `fmt.Sprintf`: returns its format string (as `Errorf`'s model does); `fmt.wp_Sprintf`
  promises some string, which is all `Spec/fmt/Sprintf.lean` says.
- `strings.Join`: goose's translation of a `+` loop; `strings.wp_Join` returns
  `sep.intercalate xs`. Go's panic when the length overflows `int` is not modelled (as
  for `append` and string `+`), which is the overflow the old axiom's no-panic claim
  glossed over.
- `crypto/rand.Int`: an arbitrary value in `[0, max)` and no error for `0 < max < 2^63`,
  read from `max`'s sign and one magnitude word; a panic otherwise; the reader is not
  read. `crypto.rand.wp_Int` is for the package's own `Reader` (which never returns an
  error), so `Spec/crypto/rand/Int.lean` gained `mz < 2^63` (`lockedRand.Intn` passes an
  `int64`). Perennial's `math.big.ownInt` now records a normalized magnitude (Go's
  invariant), which reading a value below `2^63` as one word needs, and Perennial owns
  `math/big`'s and `crypto/rand`'s `isPkgInit` (the `Reader` points-to, formerly
  `isRandInitialized` in `Base.lean`).

(`d45daf8ab`, from a parallel session, had proved `Sprintf` and `Join` from the same
models, kept `rand.Int` an axiom and pinned `56b1b6651`; this supersedes it.)
`etc/tcb-report.py --check` (after `--update`): 35 axioms, no `sorry`. The Raft proof's one
remaining axiom is `reflect.DeepEqual`, which `RawNode.wp_Propose`, `wp_Advance`,
`wp_newRaft` and `raft.wp_Step` reach (through `assertConfStatesEquivalent` in `newRaft`
and `raft.restore`); `RawNode.wp_Ready` and `wp_HasReady` rest on none of this
repository's axioms.

## The TCB and verified-code scripts: generic, per-collection trust base (2026-10-09)

`etc/tcb-report.py`, `etc/tcb-report.lean`, `etc/verified-code.py` and `etc/verified-code.go`
name no project any more: what they need comes from the layout and `etc/goose.py`, through
the new `etc/proof_roots.py` (shared by the two Python scripts):

- **Roots**: every `Link.lean`/`Results.lean` under `Proof/` and a part's `<root>/Proof/`
  (was a hard-coded list in each script and in `tcb-report.lean`'s defaults, which are gone:
  it takes the modules and `--part=ROOT` for each part root). Lean runs are grouped by the
  part roots a module reaches through the import graph (here: the server's `Link` alone, as
  before). The namespace stripped from names is the common one of the `Link.lean` files.
- **`.lake/tcb.json`** starts with a meta line (modules, commit), is written only when every
  Lean run succeeds, and `--reuse` refuses one of other modules. Before, a failed run left
  it empty and `--reuse` then counted nothing as verified (what the main checkout's empty
  `tcb.json` did: its build lacked the cache's `Link`).
- **`tcb-report.py --roots PATTERN...`** / **`--collection FILE`**: the axioms and `sorry`s a
  set of roots rests on (regexes over the name, module file and spec file), the roots that
  reach a `sorry`, and `--check [--update]` against the collection's own baseline.
  `etc/tcb-collections/raft.txt` is the Raft proof (`Link` and `Results`); its baseline is
  not recorded yet (no build of this commit on the machine when written): run
  `etc/tcb-report.py --collection etc/tcb-collections/raft.txt --check --update` after
  `lake build`.
- **`verified-code.py`**: tables per project of `etc/goose.py` (by module if it has more than
  one, by package for the packages Goose touches, by file), not "Raft"/"etcd". The counted
  Go modules are `Project.counted_modules` in `etc/goose.py` (the list that was `ETCD_MODS`,
  and raft's main module: its checkout also has `go.etcd.io/raft/tools/v3`). The by-file
  tables (and `--functions`) now include every file with a function translated with its
  body or specified: the server's `server.go` (apply thread), `cindex.go`, schema's
  `cindex.go`, `client/v3`'s `op.go`/`watch.go` were missing, so `server/v3` showed
  nothing verified there. `--package PREFIX` adds a summary row and narrows those tables.
  Specs of packages whose Go code is not in the sources (the btree, zap, raft v3.7's raftpb
  in `EtcdDeps/`, humanize) are listed with the package instead of as "outside"
  (`zap.Int'`, methods of names-only packages, `go-humanize` were mis-resolved). Totals are
  unchanged (checked on the same `tcb.json`); `raftpb/confchange.go` (nothing translated, in a
  package with names-only functions) is no longer listed.

## Sorry-free (2026-10-09)

Every cache result is `sorry`-free: re-pinned to Perennial `3ae7dc6a4`, which closes the
four Perennial `sorry`s the cache reached:
- `fmt.wp_Errorf` (`4e1bfe544`: `fmt.Errorf` as a trusted model, `wp_Errorf` proved;
  `errors.wp_New`'s `Error()` returns the message);
- `wp_map_for_range_mut_keys` (`6519b44f5`: `map.forRange` no longer holds the map across the
  body; `wp_map_for_range_mut{,_keys}` are now Perennial's, in `Perennial.Golang.Theory.Map`,
  with the statements of our deleted `MapRangeMut.lean`);
- `context.wp_WithCancel` and `context.wp_WithCancel_Background` (the `ctx-withcancel`
  branch: `atomic.Value` trusted model, both proved; `wp_WithCancel` needs its parent to be a
  `*cancelCtx` (`isCancelCtxCtx`), and the cancel function's postcondition gives
  `ContextClosed`);
- and `3ae7dc6a4` (ours): `context`'s `isInit` no longer holds ghost state, so its
  `IsPkgInit` instance (and raft's, the cache's, the client's, the server's) needs no
  `[AllG GF]`; `closedchan`'s closed state is the persistent package-init fact
  `context.isClosedchanInit`, carried by every `*cancelCtx` (`isCancelCtxOf`).

Proof-side changes: `InvCache`'s internal-context fact is `∃ ics, isContext cf.ictx ics ∗
isCancelCtxCtx cf.ictx ics` (`watchEvents` passes it to `wp_WithCancel`); `newCache` gets it
from `wp_WithCancel_Background` and keeps `"#HisStop"`'s old form through
`context.cancel_spec_forget`; **`New` and `newCache` take `context.isClosedchanInit`** (a
package-init fact of `context`, which a program's `main` establishes once `context` is
initialized, as it does `isPkgInit`), for `WithCancel(Background())`; the five
`wp_apply Hcancel` sites drop `ContextClosed` (`as -`). No other statement changed; raft,
btree and server proofs unchanged.

Gates: `lake build` passes (1655 jobs); `etc/goose.py --check` passes (no translation
changed); `etc/tcb-report.py --check --update`: the baseline lost exactly the four sorries
(`Perennial.context.wp_WithCancel`, `Perennial.context.wp_WithCancel_Background`,
`Perennial.fmt.wp_Errorf`, `wp_map_for_range_mut_keys`), 38 entries, all axioms, 0 sorries;
`etc/gen-link.py --cache`/`--server` and `etc/gen-btree-link.py` reproduce their `Link.lean`;
`etc/verified-code.py --reuse`: cache 107 verified, 0 unfinished of 107, 1206 of 1206 lines
(100%), all sorry-free; Raft 175 of 323 (2240 of 3641 lines, 61.5%); etcd 161 verified (all
sorry-free), 13 assumed of 3599 (1560 of 45566 lines, 3.4%), `server/v3` 19 verified, 0
unfinished, 9 assumed (215 lines). `Results.lean`'s `#print axioms` of `cache_New`,
`cache_Get`, `cache_Watch`, `cache_Watch_delivery`: no `sorryAx`. Push Perennial
(`3ae7dc6a4`) first.
## The cache: linearizability as a model fact, `etcdReached` (2026-10-09)

The client assumption no longer mentions caches. "etcd has reached revision `r`"
(`etcdReached r`, `InvEtcd.lean`) is a fact of the model, produced by the client's responses
and carried to every place the store's or the demux's revision moves; `isEtcdKV`'s `Get` triple
is linearizable against it. Design: `decisions.md`, "`New` and the client" (the paragraph
"fixed 2026-10-09").

- **The model**: `axiom etcdReachedAt (r : w64) : IProp GF` and `axiom etcdReachedAt_timeless`
  (an instance); `etcdReached r := ⌜sint.Z r ≤ 0⌝ ∨ ∃ r', ⌜sint.Z r ≤ sint.Z r'⌝ ∗ □
  etcdReachedAt r'`, so persistence, timelessness, downward closure (`etcdReached_mono`) and
  `etcdReached_zero` are instances/lemmas.
- **The client**: `isEtcdKV`'s triple takes any `lo` with `etcdReached lo` and returns
  (`kvGetResult pfx lo`) a header revision `r` with `etcdReached r`, `r < 2^63 - 1`, and `lo ≤ r`
  **unless the request is serializable** (a serializable get may be served by a lagging member);
  `isEtcdKVFrom` and `isEtcdKVLin` are gone. The watch contract (`watchRespOk`) gives
  `etcdReached` of a created notification's and a progress notification's header revision, and
  `etcdStepCertBody` (each batch) of the batch's revision.
- **The store** takes a second parameter `R : w64 → IProp GF` beside `E` (`storeLockInv`,
  `storeReader`, `storeWriter`; not `storeLockedPhys`): the lock invariant and the writer hold
  `□ R latestRev`; `newStore` asks for `□ R 0`, `Restore kvs rev` for `□ R rev`, `Apply` for
  `revCerts R (applyRespRevs st r)` (a progress notification's revision, or each snapshot's it
  appends: `applyResp_latestRev_mem`); `getSnapshot`/`Get`/`LatestRev` return `□ R` of the
  state seen. `applyEventsLocked` and `applyProgressNotifyLocked` are unchanged. The cache's `R`
  is `etcdReached`.
- **The demux**: `DemuxCert` gained `prog : w64 → IProp GF` (timeless, downward closed, `prog 0`,
  and `cert_prog`: a batch's certificate gives `prog` of its revision); the lock (`demuxLockRest`,
  `demuxLocked`) holds `□ C.prog maxRev`; `respCert` of a progress notification adds
  `□ C.prog hdrRev`; `demuxPubBody` adds `□ C.prog v.maxRev`, from which `demuxPubBody_prog`
  gives it of every progress notification of a published log. Every other demux statement
  unchanged (`pub_send`/`pub_close`/`demuxPub_intro` take the extra premise). The cache's `prog`
  is `etcdReached`.
- **The cache**: `get` calls `kv.Get` with the writer's `etcdReached st.latestRev`
  (`storeWriter_rev`), so `get`, `getWatch` and `getWatchLoop` lost their linearizability
  premises; `applyStorage` supplies `Apply`'s `revCerts` from the store watcher's publication
  (`storeW_revCerts`); `watchEvents` supplies `respCert`'s `prog` from the watch receive.
  `isEtcdClient` is the two field points-tos with `isEtcdKV`, `isEtcdWatcher`,
  `isEtcdProgressNotifier`, no quantification over caches. `New.spec` is unchanged.
- **Gates** (2026-10-09): `lake build` passes (1656 jobs); `etc/tcb-report.py --check` (after
  `--update`): 38 axioms (new `etcdReachedAt`, `etcdReachedAt_timeless`), 4 sorries;
  `#print axioms` of `cache_New`, `cache_Get`, `cache_Watch`, `cache_Watch_delivery` now include
  both; `etc/gen-link.py --cache` reproduces `Link.lean`; `etc/goose.py --check` passes;
  `etc/verified-code.py --reuse`: cache 97 verified, 10 unfinished of 107 (unchanged).

## Merged with upstream's server work (2026-10-09)

Our final cache unit (`New`/`newCache`, `Close`, the loops, the clock, the options,
`Results.lean`) and the re-pin to Perennial `8c33774d0` merged with upstream's `aa4020095`
(the consistent index and the apply thread, raft v3.7 in `EtcdDeps/`, the one-record
predicate refactors and `proj_simps`, the client-facing `RawNode` specs). Union everywhere:
`etc/goose.py` takes upstream's structure (`Part`, `owned`, the server's packages and roots)
plus our five names-only packages of `Client`'s field types, without `-lean`; zap is
translated once (upstream's `imports = ["!*", "go.uber.org/zap/zapcore"]`), regenerated by
`etc/goose.py` (only `zap.lean` changed from our side: zap now imports zapcore, so the
cache's `Base.lean` gained `IsPkgInit`/`GetIsPkgInitWf` instances for zapcore; no proof
changed); `etc/tcb-report.{lean,py}` have both the cache's `Results` root and the server's
second run; `etc/verified-code.py` now counts the server's `Link` too (run twice, as
`etc/tcb-report.py`). Gates: `lake build` passes (1656 jobs); `etc/goose.py --check` passes;
`etc/tcb-report.py --check` matches the baseline (the union: 36 axioms, 4 sorries; 389 + 47
root theorems); `etc/gen-link.py --cache`/`--server` and `etc/gen-btree-link.py` reproduce
their `Link.lean`; `etc/verified-code.py --reuse`: Raft 175/323; etcd 150 verified, 11
unfinished, 13 assumed of 3599 (cache 97 verified, 10 unfinished of 107; `server/v3` 18
verified, 1 unfinished, 9 assumed).

## Perennial `8c33774d0`: Goose without `-lean` (2026-10-09)

Perennial's `6fa346618` merges our `f35530719`/`8c7000190`/`f8b35ddbf` with upstream's
`37416dd10` (Rocq code, tooling and prose removed from the `lean` branch) and `cdf8c0f81`:
`goose` and `proofgen` no longer take `-lean` (the output is always Lean), and the names
`Foo.impl`, `T.M.impl` are produced directly instead of through an internal `ⁱᵐᵖˡ` suffix
that the Lean printer decoded. The generated names are the same: regenerating both
translations changed no file. `etc/goose.py` no longer passes `-lean` (it keeps
`-lean-root`). The merge resolved the `goose/glang/coq.go` conflict by deleting the file,
which also deleted the `GenericTypeExpr` type of our `f35530719` (goose did not build);
`8c33774d0` restores it in `goose/glang/syntax.go` (one implementation; its Lean printer is
unchanged). The std-lib translations regenerate byte for byte (Go 1.26.0, no `--lean` flag
now). Gates: Perennial's `lake build` passes; here `lake build` passes (1472 jobs),
`etc/goose.py --check` passes, `etc/tcb-report.py --check` matches the baseline (10 axioms,
4 sorries, unchanged), `etc/gen-link.py --cache` and `etc/gen-btree-link.py` reproduce their
`Link.lean`, `etc/verified-code.py`: Raft 175/323, cache 97 verified and 10 unfinished of 107.
Push Perennial (`8c33774d0`) first.

## Merged with upstream's layout (2026-10-09)

The demux, the `MessageState` translation, the key predicates and request validation and
`verified-code.py`'s cache count (done on the old layout, `EtcdGrove/Cache/`,
`EtcdCache/`) were merged into the layout by kind and Go package path: specs and proofs
under `{Spec,Proof}/go_etcd_io/etcd/cache/v3/`, but the `clientv3` functions translated
for the validation (the 16 `Op` getters, `getPrefix`, `GetPrefixRangeEnd`) under
`{Spec,Proof}/go_etcd_io/etcd/client/v3/` (next to `WatchResponse__IsProgressNotify`);
`InvDemux`, `InvCache` and `MapRangeMut` under `Proof/go_etcd_io/etcd/cache/v3/`; every
file a module (`module`, `public import`, `@[expose] public section`). Perennial is
pinned at `cbb85c041` (upstream's `11fd2db` merged with `bytes.Compare`, which the key
predicates need). `etc/tcb-report.py --check`: 4 axioms (`fmt.Sprintf`,
`rand.Int`, `reflect.DeepEqual`, `strings.Join`) and 2 sorries (Perennial's
`fmt.wp_Errorf`; `wp_map_for_range_mut_keys`, the demux's documented Perennial gap): no
btree, `slices.Sort` or `MessageState` entries, no `newStore_RLocker`. `lake build`
passes (1333 jobs), `etc/goose.py --check` passes, `etc/gen-link.py --cache` reproduces
`Proof/go_etcd_io/etcd/cache/v3/Link.lean`.

## Done (at `857d09190`)

- Lake project depending on Perennial (`lakefile.toml`); `Base.lean`.
- `plog.v`, `protocol.v` (7.1k lines: `Protocol/{Model,Ghost,GhostState,StepGhost,
  LeaderCompleteness,Refinement,Facts}.lean`): **fully proved**. `#print axioms` of
  `ownRaftGhost_step`, `leader_completeness`, `state_machine_safety`,
  `ownRaftGhost_alloc`: only `propext`, `Classical.choice`, `Quot.sound`.
- `defs.v`, `step_lemmas.v`, `inv_*.v` (incl. `inv_memstorage.v`, `inv_readylog.v`,
  `inv_rawnode.v`): no `sorry`.
- The 167 specs and the 167 proofs (`raft.Step`'s branches in `Proof/raft__Step/`,
  one module per Rocq helper file, incl. `MsgStorageAppendResp`/`MsgStorageApplyResp`).
  Trust boundary as in the Rocq at first: the state/logger axioms and nine
  `axiom … .wp_proof` for code outside the scope (since 2026-10-08 only `.wp_proof`
  axioms remain; see below).
- **`RawNode.Ready` is proved here although it is `Admitted` in the Rocq**: the Rocq
  script stops (`Show. Admitted.`) after stepping all the code and closing the struct,
  before the postcondition; `Proof/RawNode__Ready.lean` ports that script and proves the
  postcondition from the Rocq file's own (Qed) helper lemmas. Its spec was checked
  clause by clause against `spec_RawNode__Ready.v`.
- `memstorage_instance.v` (`MemstorageInstance.lean`) and `election.v` (the links:
  `Link.lean`, generated by `etc/gen-link.py` from the 857d09190 Rocq; the
  results: `Results.lean`, which `#print axioms` the top-level results): no `sorry` of
  their own. **no `sorry` at all since 2026-10-08**: `raftLog.slice`'s one `sorry` (Rocq's deliberate
  `admit`, "the log fits in memory") is gone, see below.

- **`confchange.Restore` is proved (2026-10-08)**, no longer an axiom. The package is
  now translated in full (Perennial's `confchange.toml`), and `Restore` is proved from
  `toConfChangeSingle`, `chain` and `Changer.Simple` (itself from `checkAndCopy`,
  `Config.Clone`, `apply`, `makeVoter`, `initProgress`, `symdiff`, `checkAndReturn`,
  `checkInvariants`, `joint`/`incoming`/`outgoing`, `nilAwareDelete`): 16 new
  spec/proof pairs, Lean-first (no Rocq counterpart), listed in
  `etc/link-lean-first.txt` for `etc/gen-link.py`; shared vocabulary in
  `InvConfchange.lean`. `Restore.spec` is unchanged. `JointConfig.IDs.spec` was
  generalized (any `JointConfig` cell, any fractions) with the old tracker form derived
  (`IDs.spec_tracker`); `apply`/`Simple` take a `size vm < 2^63` premise (their
  `len == 0` test is a 64-bit comparison). The translation needed a Goose fix: `cc := cc`
  (the loop-local-copy idiom in `Restore`) read the *new* cell; see notes/decisions.md.
- **`raftpb.ConfState.Equivalent` is proved (2026-10-08)**, no longer an axiom: `raftpb`'s
  translation includes it (`Code/go_etcd_io/raft/v3/raftpb.toml`: `ConfState.Equivalent`, imports
  `fmt`/`reflect`/`slices`). What it calls that Goose cannot model is
  `reflect.DeepEqual`; that is the new axiom, stated on two `ConfState` values as Go's
  `DeepEqual` reads on this struct (`Spec/reflect_DeepEqual.lean`, `confStateDeepEq` in
  `InvRaftpb.lean`, which also has `sorted_perm_eq` and `wp_slice_append_nil_empty`:
  `append` of nothing onto `nil` is `nil`, with no ownership of the empty source,
  which the callers do not have). So the two axioms about core raft code are gone;
  the 13 that remain are all outside raft (`reflect`, `math/big`, `fmt`, `strings`,
  `slices`, `rand`, the `Logger` and `Storage` interfaces, protobuf's `Entry.Size`).
- **The last `sorry` is gone (2026-10-08).** `raftLog.slice` admitted
  `|ents| + |unstable| < 2^63`, the bound `extend.spec` asked for and nothing could
  supply (Rocq: `Admitted. (* Trusted *)`). `extend.spec` no longer asks for it: past
  `2^63` the Go `int` `need` wraps negative, the code runs `append(dst, vals...)`, and
  Perennial's `append` model assumes no length overflow (`sumAssumeNoOverflowSigned`,
  Goose's standing treatment of Go's `growslice` panic) -- the admission restated. So
  the proof takes it from the model (`Proof/extend.lean`), and what is trusted is
  unchanged. Every result is now `sorry`-free; `etc/tcb-report.py --check`: 13 axioms,
  0 sorries.
- **`big.NewInt` and `big.Int.Int64` are proved (2026-10-08)**, in Perennial
  (`Proof/math/big.lean`; `math/big.toml` translates `NewInt`, `Int.Int64` and `low64`):
  `ownBigInt` is Perennial's `math.big.ownInt` (sign and little-endian word slice) instead
  of an abstract axiom, the two specs are unchanged, and `crypto/rand.Int` (still assumed)
  is stated over the concrete predicate. Perennial's Go semantics gained unary minus on
  unsigned integers (`neg_uint64` & co., `Golang/Defn/Predeclared.lean`), which `NewInt`
  uses. Perennial pinned at 584b17c54: `lake build` passes, `etc/goose.py --check`
  passes, `etc/tcb-report.py --check`: 10 axioms, 0 sorries. `slices.Sort` and `strings.Join` stay assumed, and both specs
  claim more than Go's code does in the model: `Sort` overflows `2*root+1` in its
  heapsort fallback past 2^62 elements, `Join` panics if the total length overflows
  `int` (and cannot be translated: `strings.Builder` uses `unsafe.String`).
- **`ownInflightsRaw` is indexed by one pure record (2026-10-08)**, `InflightsRing`
  (window, `start`, buffer length), instead of the Goose value and the buffer's
  contents; `grow`'s spec is now deterministic and the public `Inflights` specs are
  unchanged. The rule (one record, as small as the specs allow) is in decisions.md,
  "Predicate indices", with what else it was applied to and what is left as is.
- **`ownUnstable` is indexed by one pure record (2026-10-08)**, `UnstableSt` (entries,
  `offset`, `offsetInProgress`, pending snapshot), instead of the Goose value and the
  entries; the predicate carries the snapshot's `ownSnap` and the logger, so the
  `unstable` specs lost those premises and their "unchanged" facts.
- **The same rule, applied to the rest (2026-10-08)**: the storage's `prev`/`ents`/`ss`
  are one `StorState` (`StorageModel.ownStorage`, `isStorageWith`, the
  `MemoryStorage` predicates); `ownProgressMap`'s pointer map is existential; `Progress.recentActive`
  and `ReadOnly.safe`, which no spec reads, are gone.
- **The `raftLog` layer follows it too (2026-10-08)**: `ownRaftLogCore` is inlined into
  `ownRaftLog l ls` (storage `∃ σ : StorState`), the proofs keep `ls` a variable, and
  `newLogWithSize` lends the storage with a wand back to `ownRaftLog`. `proj_simps`
  (`ProjSimps.lean`) generates `@[simp, word_unfold]` projection lemmas for 31
  record-building functions; `CLAUDE.md` ("Proof writing", "Records") says how proofs
  handle records (keep them variables, `word` over `omega`). The `ownRawNode` fold into one
  record was reverted, then superseded by the client-facing `RawNode` specs below.
- **The `Logger` and `Storage` interfaces assume nothing (2026-10-08).** `isLogger`
  (`InvLogger.lean`) is a definition, the formatting methods' triples bundled as
  `isStorageWith` bundles `Storage`'s, so `isLogger_persistent` is an instance and
  `Logger.wp_logf` a theorem: a client supplies the triples with its `Logger`.
  `ownStorage` (`InvStorage.lean`) is the field of `class StorageModel GF`, a
  parameter every section that reaches it carries (`[StorageModel GF]`, also in
  `etc/gen-link.py`'s template), with deliberately no global instance; it stays
  abstract (not specialised to `ownMemoryStorage`), but the results now hold for
  *every* storage predicate instead of one unknown one, which no client could have
  established (`newRaft`'s precondition asks for it, and `ownRawNode_persist` hands it
  to the application to `Append`). Four axioms gone (`isLogger`,
  `isLogger_persistent`, `Logger.wp_logf`, `ownStorage`); `etc/tcb-report.py
  --check`: 6 axioms (`reflect.DeepEqual`, `fmt.Sprintf`, `strings.Join`,
  `slices.Sort`, `rand.Int`, `raftpb.Entry.Size`), 0 sorries. `RawNode.wp_Ready` rests
  on `Entry.Size` alone, `RawNode.wp_Propose` on `Entry.Size`, `rand.Int`,
  `slices.Sort` and `reflect.DeepEqual`.
- **`raftpb.Entry.Size` is proved (2026-10-08)**, no longer an axiom: `raftpb.toml`
  translates `Entry.Size` and `sovRaft` (gogoproto, `raft.pb.go`) and imports
  `math/bits`; `Proof/Entry__Size.lean` proves the triple from the body, with
  `sovRaft` a Lean-first spec/proof pair (`etc/link-lean-first.txt`). The triple gained
  only an `isPkgInit raftpb` conjunct (for `bits.Len64`), which `limitSize`/`entsSize`
  discharge from `isPkgInit raft.v3`; no caller's spec changed. `etc/tcb-report.py
  --check`: 5 axioms, 0 sorries; `RawNode.wp_Ready` and `wp_HasReady` now rest on none
  of this repository's axioms, `RawNode.wp_Propose` on `rand.Int`, `slices.Sort`,
  `reflect.DeepEqual`.
- **`slices.Sort` is proved (2026-10-09)**, no longer an axiom: Perennial (pinned at
  c061d3b22) translates `Sort` and the `*Ordered` pdqsort and proves
  `slices.wp_Sort_uint64` (`Proof/slices_proof/sort.lean`), which
  `Proof/slices/Sort.lean` is. Its spec gained the premise `len ≤ 2^62` (past it the
  heapsort fallback's `2*root+1` overflows `int`, so the old spec was false in the
  model), and the bound is carried as follows:
  - `ownTracker`'s `Hcfg_size` and `ownConfig`'s `Hcsz` are tightened from
    `size cfg < 2^63` to `≤ 2^62`. Nothing in the heap bounds a voter set, so this
    is still a property of the configuration.
  - The bound enters at `newRaft`, whose spec has a new premise that the storage's
    initial `ConfState` has at most `2^62` voters. This is the only new assumption.
  - `raft.restore` takes the bound from the old tracker (`ownTracker_size`): the
    snapshot's voters are a permutation of the current configuration.
  - The tighter premise replaces `< 2^63` on `MajorityConfig.CommittedIndex`,
    `JointConfig.CommittedIndex` and `readOnly.maybeAdvance` (an exported result with
    no callers).
  - It is a new premise on `MajorityConfig.Slice`, `ConfState.Equivalent` and
    `assertConfStatesEquivalent`, whose callers discharge it from the tracker or the
    configuration.

  `lake build` passes; `etc/tcb-baseline.txt` lost exactly `slices.Sort`: the Raft proof's own axioms are now
  `reflect.DeepEqual`, `fmt.Sprintf`, `strings.Join` and `rand.Int`.
  Since Perennial `56b1b6651` (2026-10-09) `fmt.Sprintf` and `strings.Join` are theorems
  from Perennial's trusted models; the Raft proof's own axioms are `reflect.DeepEqual` and
  `rand.Int` (Perennial's `wp_Int` covers only `mz < 2^63`).
- **What the four remaining axioms would take** (checked 2026-10-08, with "no
  higher-level spec changes" as the constraint; since 2026-10-09 only `reflect.DeepEqual`
  remains, the other three are Perennial models, see the section at the top):
  - `fmt.Sprintf`, `strings.Join`: not translatable (`fmt`'s printer reaches
    `reflect`; `strings.Builder.String` is `unsafe.String`), and `Join`'s no-panic claim
    needs a bound on the strings' total length that `Sprintf`'s "some string" cannot
    give.
  - `reflect.DeepEqual`: reflection, outside Goose.
  - `rand.Int`: `crypto/rand.Reader` reads the OS RNG (a syscall), outside GooseLang.
  The last four can only go by changing the Go code (the `upamanyus/etcd-raft`
  `goose` fork) or by trusted models (`Perennial/TrustedCode`), which move the
  trust rather than remove it.
- **`RawNode` specs are client-facing (2026-10-09)**: `ownRawNode γ rn id rs` hides the
  node state, the ghost state and `NStateRel`; `RNState` is what a client observes
  (delivered committed log, entries to persist, queued steps, term); `Ready`'s
  committed entries come with `isCommitted γ (rs.delivered ++ ce)`, no `applying`.
  `PstepCommitMono` and `ready_stable_ok` are proved; `raft.Step`'s spec gained a frame
  for local messages. The `Advance` gap (`advanceable`) is closed since 2026-10-10 (see
  the section of that date).
- Trust base: `etc/tcb-report.py` (gate: `--check` against `etc/tcb-baseline.txt`).
- **Build checked 2026-10-08** at Perennial c35b7710d (a `--packages` override pointing
  at a checkout of the pinned commit): `lake build` completes (977 jobs, 0 errors); `etc/tcb-report.py --check`
  passes (13 axioms, 0 sorries). Perennial's own `sorry`s (`Proof/errors.lean`,
  `GeneratedProof/{os,strings,sync,fmt}.lean`, `Proof/context.lean`) are not reached by
  any result.

- Build timing: `etc/build-report.py build` (parallelism over time, critical path;
  design in `decisions.md`); CI: `.github/workflows/lean.yml` (self-hosted runner
  `coqdev`, as in mit-pdos/xv6iris; build with the report on the summary page,
  `tcb-report.py --check`). First full build of this
  repository's modules (dependencies built, 24 cores, 2026-10-08): 402 modules,
  3m48s wall, 40m35s CPU; the import chain bounds it at 3m02s, of which
  `Proof/stepLeader.lean` is 1m08s (the slowest module, and last on the path before
  `Link`); the Protocol chain (`Plog` … `Facts`) ran one compile at a time for the
  first 1m10s. Since `Protocol.lean` imports only `Model`/`Ghost`/`GhostState` (what
  `Defs` and `Inv*` use), `Defs` starts at 0:29 and the build takes 3m01s (bound
  2m19s); what limits it now, and two measured upstream options (precompiled
  Perennial: −11% CPU; the module system for faster imports), are in
  `decisions.md` ("Build speed"). With every file (here and in Perennial) a module, a
  compile's peak memory is 1.8 GiB instead of 2.8 GiB and a spec module (almost all
  import) takes 2.1s of CPU instead of 2.6s; whole-build times on a quiet machine
  are still to be measured (the 2026-10-08 runs shared the machine).
- Verified code: `etc/verified-code.py` (since 2026-10-09 it takes the forks and pins
  from `etc/goose.py`, reads the translations in `Code/` and counts the linked results of
  both `Link.lean`s, raft's and the cache's). After the merge (2026-10-09; `upamanyus/etcd-raft`
  `531b20c`, `upamanyus/etcd` `48fd5a5`): raft 175 of 323 functions verified, 2240 of
  3641 Go code lines (61.5%, all sorry-free); etcd 80 of 3599 functions (76 sorry-free),
  584 of 45564 lines (1.3%): the cache package 61 of 107 functions verified, 8 unfinished
  (their proofs use a `sorry`: the demux's three loops over a map they write,
  `wp_map_for_range_mut_keys`, and five error paths through Perennial's `fmt.wp_Errorf`), 550 of 1204
  lines (45.7%), and 19 `clientv3` functions (the `Op` getters, `getPrefix`,
  `GetPrefixRangeEnd`, `WatchResponse.IsProgressNotify`). The btree (not etcd's code) is
  not counted.

## etcd `cache`: the `EtcdCache` library (2026-10-08; translation only, no proofs)

Preparation for verifying etcd's `cache` package (`go.etcd.io/etcd/cache/v3`) here, set
up like the raft translation (in `{Code,GeneratedProof}/{go_etcd_io/etcd,k8s_io,
google_golang_org}/` since the layout by Go package path; it was the library `EtcdCache`),
generated and checked by `etc/goose.py` (now two projects, `etcd-raft` and `etcd`).

- **Source**: fork `upamanyus/etcd`, branch `goose-lean`, pinned at `48fd5a507`: branch
  `goose` rebased onto upstream `main` (`f061acd09`; it was on `3efe157f6`, 2026-03-29) without
  conflicts ("Avoid fallthrough", in `client/v3/leasing`, is now `b6b069ede`), plus two
  new commits that change `cache/` only, both behavior-preserving workarounds for Goose
  bugs: `5ae038f0f` names `mvccpb.Event` instead of its alias `clientv3.Event`
  (Goose's `getStructInfo` does not `Unalias`, so `ev.Kv` on an alias-typed pointer is
  rejected), `48fd5a507` selects `entry[T].revision` from a variable instead of from
  `r.at(mid)` (Goose's `StructFieldGet` on a generic struct value omits the type
  argument: `entry.ty`, not `entry.ty T`). It is a *new* branch because the Rocq
  translations (etcd-grove `main`, Perennial `master`: `etc/ci-goose-check.py`) are
  regenerated from branch `goose` by name, so `goose` must stay at the March upstream.
  Pushed 2026-10-08, so `etc/goose.py` fetches it from GitHub (`--src etcd=<checkout>` or
  `$ETCD_SRC` only for an unpushed revision). CI's Go is now 1.27 (etcd's `go.mod`).
  **Since 2026-10-09 pinned at `6ab61a1c7`**: `48fd5a507` merged with the fork's branch
  `cache-ready-after-retry` (three fixes of `cache.go`, see "The watch loop and Cache.Watch"),
  pushed as `goose-lean` the same day (`etc/goose.py --check` fetches it from GitHub).
- **With bodies**: all of `cache/v3` (every function and method, non-test files;
  `cache/v3.toml`: `translate = ["*"]`).
- **Types and names only** (`translate = ["!*"]`, `translate_types = true`, a few
  imports kept so their types translate): `client/v3`, `api/v3/etcdserverpb`,
  `api/v3/mvccpb`, `api/v3/v3rpc/rpctypes`, `k8s.io/utils/third_party/forked/golang/btree`
  (with `sync` imported so that the generic `FreeList[T]` is translated: an
  axiomatized generic type comes out as `∀ (T : go.type), go.type`, which is not Lean).
- **The protobuf messages the cache reads are real structs** (2026-10-08, second
  commit): `mvccpb.KeyValue`, `mvccpb.Event`, `etcdserverpb.{ResponseHeader,
  RangeResponse,WatchResponse}` are listed in their package's `translate` (type only,
  no methods). `translate_types` alone never translates them: every protobuf-go v2
  message has `state protoimpl.MessageState`, `unknownFields protoimpl.UnknownFields`,
  `sizeCache protoimpl.SizeCache`, and Goose's `translate_types` refuses any type
  mentioning another package's alias. Those three aliases come from two more
  packages: `google.golang.org/protobuf/runtime/protoimpl` (just the three aliases;
  `SizeCache`/`UnknownFields` translate to `int32`/`[]byte`; protoimpl's other aliases
  must not be left to `translate_types`, which axiomatizes an alias-of-an-alias as
  `axiom SizeCache`, not `SizeCache.ty`, a name the users do not find) and
  `google.golang.org/protobuf/internal/impl` (names only, but for the struct
  `impl.MessageState`, translated since 2026-10-09; its pointer field's `*MessageInfo`
  stays axiomatized), and `google.golang.org/protobuf/internal/pragma` (types only, all
  four translated: `NoUnkeyedLiterals`, `DoNotCompare` (`[0]func()`) and `DoNotCopy`
  (`[0]sync.Mutex`, so `sync` is imported), which `MessageState` embeds, and
  `DoNotImplement`).
  `clientv3.GetResponse` (`type GetResponse pb.RangeResponse`), `clientv3.WatchResponse`,
  `Op`, `OpOption`, `KV`, `Watcher`, `WatchChan` were already translated.
  `clientv3.Client` is translated since 2026-10-09 (the cache reads its `KV` and
  `Watcher` fields in `newCache`), with the packages of its other fields' types names-only
  (`google.golang.org/grpc`, `grpc/credentials`, `client/v3/credentials`,
  `client/v3/internal/resolver`, `go.uber.org/zap`; "The whole package" below).
- Nothing else (grpc, zap, ...) is reached; types that would need it are axiomatized
  (212 `axiom X.underlying`, by `grep '^axiom .*\.underlying'` in `Code/`), and their
  generated instances are `sorry -- axiomatized type` (424, in `GeneratedProof/`: 150
  in the protobuf packages, 236 in
  `etcdserverpb`, 36 in `client/v3`, 2 in `rpctypes`; no proof uses them, and the raft
  trust base is unaffected). Standard-library packages are Perennial's.
- **`impl.MessageState` is a real struct** (2026-10-09): its generated `TypedPointsto` and
  `IntoValTyped` instances are proved (`solve_into_val_typed_struct`), so the two
  `sorry -- axiomatized type` instances the cache proofs reached (allocating
  `&pb.ResponseHeader{}`) are gone from the trust base. `Proof/go_etcd_io/etcd/cache/v3/Base.lean`
  gained a `True` package instance for `internal/pragma` (translated names-only,
  `Code/google_golang_org/protobuf/internal/pragma.toml`). The field-only message
  predicates and `InvStore.lean`'s high-priority `TypeRepr` instances (`decisions.md`) were
  kept: they still work, and no longer guard against a `sorry`.
- `-lean-root` maps `go.etcd.io/etcd`, `k8s.io` and `google.golang.org` to the empty root
  (modules `Code.go_etcd_io.etcd.cache.v3`, ...).
- The two Goose bugs above belong fixed in Perennial's `goose/types.go`: `types.Unalias`
  in `getStructInfo` (tried: two lines, and the alias errors go away), the type arguments
  in `structInfoToGlangType` (not tried); with them the two fork commits could be dropped.
  The `go.type` in axiomatized generic types is a third (Lean backend).

## The cache's btree: verified (`Proof/k8s_io/utils/third_party/forked/golang/btree/`)

The B-tree etcd's cache uses, `k8s.io/utils/third_party/forked/golang/btree` (the fork
of google/btree's generic `BTreeG`, renamed, without the non-generic `Item` API), is
translated with bodies (part of the `etcd` project of `etc/goose.py`; its `.toml` no
longer restricts it) and proved. The proof was first done on google/btree `aeba20f`
(2026-10-08) and moved onto the fork with the layout by package path (2026-10-09):
every proof carried over unchanged but for the renames (the fork's `freeNode` and
`ReplaceOrInsert` are restructured but equivalent). Design in `decisions.md`
("google/btree: a second proof tree").

- **Every function is proved**: 51 specs, 51 linked results (`Link.lean`, generated by
  `etc/gen-btree-link.py`), no `sorry` and no axiom of this repository; `Results.lean`
  prints every result's axioms: `propext`, `Classical.choice`, `Quot.sound` and
  Perennial's names-only Go declarations (no `sorryAx`). The API (`New`,
  `NewWithFreeList`, `NewOrdered`, `Less`, `NewFreeList`; `BTree`'s `Clone`,
  `ReplaceOrInsert`, `Delete`/`DeleteMin`/`DeleteMax`, `Get`, `Has`, `Min`, `Max`,
  `Len`, `Clear`, the eight `Ascend*`/`Descend*`), its internals (the `items` methods,
  the free list under its mutex, copy-on-write contexts, `mutableFor`/`mutableChild`,
  `split`/`maybeSplitChild`, `insert`, `get`, `min`/`max`,
  `remove`/`growChildAndRemove` (one joint Löb induction), `iterate`, `reset`), and
  package initialization.
- The top-level predicate `ownBTree o t dq s` (`Defs.lean`): the tree at `t` holds the
  entries `s` (Go item, key), keys strictly increasing under `o`; `ownBTree_split`
  (`Fractional.lean`) divides it between readers.
- **No bug found.** Restrictions the specs carry: `1 < degree <= 2^62` (`New` panics
  below; above, `maxItems()` overflows and the second insert panics), `less` deciding
  a strict total order on keys, `Len()` modulo `2^64`. `iterate`'s
  `includeStart`/`hit` skip branches are dead for every caller.
- **The cache uses it** (`InvBtree.lean`): the cache's seven btree specs (its trust
  boundary until now) are the proved ones; its `ownBTree` (models under a strict weak
  order) is defined over the btree's, with the classes of the order as keys, and the
  store's proofs derive their model-level triples from the proved specs
  (`*.modelSpec_of`, all proved; the cache's `ownBTree` keeps the list of (Go item,
  model) pairs, and `ownBTree_persist` rests on `btree.ownBTree_persist`,
  `Fractional.lean`). `btree.New` and `newStore` (and `isStore`) now require
  `degree <= 2^62`.
- **Needs Perennial `11fd2db`** (its `lean` since 2026-10-09, pinned here): three
  commits on top of `2b8cb96`: (1) `copy` as a memmove -- the old model copied in place
  front to back, which is not Go's `copy` for overlapping slices and made `insertAt`'s
  `copy(s[i+1:], s[i:])` corrupt the tree (`decisions.md`); (2) a step rule for
  converting between pointer types with the same underlying type; (3)
  `sort.wp_initialize'`. Raft needed one change for (1)
  (`Proof/go_etcd_io/raft/v3/InvRaftpb.lean`).
- Regenerating the `etcd` project needs Go 1.27 for goose (the fork requires it):
  `GOTOOLCHAIN=go1.27.1 etc/goose.py --project etcd`.
- Cost of the proof (time, tokens, build time, size): `COST.md` in the proof directory.

## Next

- Follow the Rocq RawNode branch past 857d09190 (its worktree has an uncommitted
  edit to `proof_RawNode__Ready.v`, not ported).

## Differences from the Rocq besides the language

- No axiom for the `Logger` and `Storage` interfaces (Rocq: `is_Logger` and
  `own_Storage` are `Axiom`s, with `wp_logf` a third): `isLogger` is a definition and
  `ownStorage` a typeclass parameter (`StorageModel`), see "Done".
- Names follow Perennial's Lean conventions (`raft.wp_Step`, `own_raft_phys` →
  `ownRaftPhys`, …); see Perennial's `etc/lean-rename/renames.tsv` for the
  framework's Rocq → Lean names.
- The framework changes `main` made to Perennial's Rocq framework
  (`new/golang/theory/*.v`) are ported to Perennial's Lean framework where a proof
  here needs them, not to this repository.

### The ring buffer (`cache/ringbuffer.go`): proved (2026-10-08)

`ringBuffer[T]` is specified and proved in full, Lean-first, for any Go type argument `T`
with Lean representation `T'` (Perennial's `atomic.Pointer[T]` instance assumptions):
`newRingBuffer` and the 13 methods (`Append`, `full`, the four iterations, `PeekLatest`,
`PeekOldest`, `RebaseHistory`, `moduloIndex`, `at`, the two binary searches), one
`{Spec,Proof}/go_etcd_io/etcd/cache/v3/<fn>.lean` pair each, linked in `Proof/go_etcd_io/etcd/cache/v3/Link.lean`
(generated: `etc/gen-link.py --cache`, from `etc/link-lean-first-cache.txt`). Package
instances in `Proof/go_etcd_io/etcd/cache/v3/Base.lean` (`True` for the cache and the etcd, k8s and protobuf packages
it imports). No `sorry`, no axiom: `etc/tcb-report.py --check` now also takes
`Proof.go_etcd_io.etcd.cache.v3.Link`'s 14 results as roots (200 roots) and the baseline is unchanged.

- **The predicate** (`InvRingBuffer.lean`): `ownRingBuffer r cap isItem revOf items`, the
  model a list of abstract values `items : List V`, oldest first. `r ↦ rb`, `rb.buffer' ↦*
  ents`, `RingOk` (`0 < cap ≤ 2^61`, `len(buffer) = cap`, `size = |items|`, `tail < cap`,
  `head = (tail + size) % cap`), item `i` in slot `(tail + i) % cap` with `revision =
  revOf items[i]` (pure) and `isItem item items[i]` (under `□`), revisions strictly
  increasing (`RevSorted`), and the stored `revisionOf` closure's triple
  (`revisionOfSpec`). `cap` is a parameter.
- **Specs**: `Append` takes `isItem item v` (persistent) and `RevAbove` (revision above the
  newest), and leaves `ringAppend cap items v`; the searches return `ltCount` /
  `leCount - 1`; the iterations are loop-invariant style (`iterSpec`, `P : Nat → IProp`,
  `Q` on early stop) over the exact visited sublists (`ascendGeVisited`, ...).
- `newRingBuffer` asks for `capacity ≤ 2^61`: `at` computes `tail + i + len(buffer)`, up
  to `3·cap`, which overflows a Go `int` past that, and Goose's `make` does not bound the
  length. The demux's caller (`historyWindowSize`, unbounded in `Config`) will have to
  supply it. See `decisions.md`.
- No Goose or proofgen problem with the generic structs: `ringBuffer T'`/`entry T'`
  points-tos, field access and the `[]entry[T]` slice all worked as generated.

### The store (`cache/store.go`, `cache/snapshot.go`): proved (2026-10-08)

`newStore` and `store`'s `Get`, `getSnapshot`, `Restore`, `Apply`,
`applyProgressNotifyLocked`, `applyEventsLocked`, `LatestRev`, with `validateRevisions`,
`newKVItem`, `kvItemLess`, `newClonedSnapshot`, `snapshot.Range`, `isPrefixScan`,
`probeItemFromKey`, and two methods of other packages translated for the store
(`clientv3.WatchResponse.IsProgressNotify`, `etcdserverpb.ResponseHeader.GetRevision`;
`client/v3.toml` also translates the constants `EventTypeDelete`/`EventTypePut`): one
`Spec`/`Proof` pair each, linked in `Proof/go_etcd_io/etcd/cache/v3/Link.lean`. Design and rejected alternatives:
`decisions.md`, "store: btree as the trust boundary, ghost state under the RWMutex".

- **State model** (`InvStore.lean`): `StoreState` = latest revision, latest map, history of
  `(rev, map)` snapshots, oldest first; a map (`KvMap`) is the btree's item list, entries
  `(key, *KeyValue)` strictly sorted by Go's `<` on strings (`kvLess`, `go.GoStringLt`).
  `StoreInv cap st`: `latest.rev ≥ 0`, maps sorted, at most `cap` snapshots with strictly
  increasing revisions none above `latest.rev`. `StoreState.Synced` (newest snapshot =
  latest map) holds after `Restore` and a successful `Apply` (`applyResp_synced`), not after a
  failed one. Models: `snapModel` (`getSnapshot`), `kvRange` (`Range`), `applyEvents`/`applyResp`
  (`Apply`, with the exact partial state of a failed delete), `restoreState` (`Restore`).
- **Ghost shape**: `storeLockInv s γ cap q` is the `RWMutex`'s fractional `P q` (Perennial's
  `ownRWMutex`): `q` of `latest.rev`, of the history ring (`ownRingBuffer` is now fractional) and
  of a `monoNat` on `latest.rev`, and `q/2` of a `ghostVar` with the `StoreState`.
  `storeWriter s γ cap st` (the other half, a mutex token, the latest tree, a lower bound);
  `storeReader s γ cap` (a reader token: `RWMutex` bounds the readers; `newStore` returns
  `actualMaxReaders - 1`); `storeRevLb γ r` (persistent); `isStore s γ cap` (persistent:
  `revCond`'s `isCond`, `degree > 1`, `0 < cap ≤ 2^61`). Readers (`Get`, `getSnapshot`,
  `LatestRev`) return facts about *some* state at least their lower bound (`storeSeen`);
  `Apply`/`Restore` take and return `storeWriter` with the exact transition.
- **Errors** are package variables (`Base.lean`: the cache's `ErrNotReady`, `rpctypes`'
  `ErrFutureRev`/`ErrCompacted` point to fixed non-nil errors); specs return "the value of
  that variable" (`snapErr`).
- **Axioms (trust boundary)**: none of the store's own since 2026-10-09: the btree is
  proved (`Proof/k8s_io/.../btree/`, see above), and its seven specs and `ownBTree` are
  the proved ones (`InvBtree.lean`).
- **`sorry`**: none of the store's own since 2026-10-09: `newStore_RLocker`
  (`RWMutex.RLocker()`'s conversion `*RWMutex → *rlocker`) steps by Perennial's new
  `convert_pointer_same_underlying` (Perennial `11fd2db`). `fmt.Errorf` (the error paths)
  is Perennial's own `sorry` (`Proof/fmt.lean`), reached.
- **Perennial gaps found**: the pointer-to-pointer conversion above (closed in
  `11fd2db`); no `isLocker` for
  `rlocker` (the cache's `revCond.Wait` will need it); `wp_load` through a fractional or
  persistent struct points-to fails (the Access search takes the field-store instance, which
  needs `DFrac.own 1`, and does not backtrack), worked around per proof with
  `attribute [-instance] …_access_store_…`; a struct field access finds `TypeRepr` through
  the struct's `IntoValTyped` (for protobuf messages a `sorry` until `MessageState` was
  translated), worked around with direct `TypeRepr` instances in `InvStore.lean`.
- `etc/tcb-report.py --check` (2026-10-09, roots now including the btree's `Link`): 4 axioms (`fmt.Sprintf`, `rand.Int`, `reflect.DeepEqual`, `strings.Join`) and 3 sorries, all outside this repository's proofs (Perennial's `fmt.wp_Errorf`, two generated protobuf instances); the nine btree axioms and `newStore_RLocker` are gone. `etc/goose.py --check` passes (fetching the fork from GitHub; Go 1.27 for the etcd fork). Since the merge with the demux and `MessageState` work: 4 axioms, 2 sorries ("Merged with upstream's layout" above).

### watcher, notifier, ready (`cache/watcher.go`, `cache/demux.go`, `cache/ready.go`): proved (2026-10-09)

Three small concurrent components, Lean-first like the store, one `Spec`/`Proof` pair per
Go function, linked in `Proof/go_etcd_io/etcd/cache/v3/Link.lean` (the 15 new specs are stated at
`HeapGS HasLC.hasLC GF`, as Perennial's channel, `Once` and `context` specs are;
`etc/gen-link.py --cache` now emits them in a second section, as the raft side does).
Design and rejected alternatives: `decisions.md`, "watcher, notifier, ready".

- **watcher** (`InvWatcher.lean`, `OnceFrame.lean`): `newWatcher`, `enqueueResponse`,
  `Compact`, `Stop`. Predicates `isWatcher w γ pred` (persistent; `pred :
  Option (GoString → Bool)`, the `keyPred` closure's triple `keyPredSpec`, nil iff `none`),
  `watcherOpen γ sent` (the producer's), `watcherClosed γ sent c` (persistent; `c = none`
  from `Stop`, `some rev` from `Compact rev`), `watcherConsumer γ received` (the
  consumer's); the invariant `watcherInv` ties the two logs to the channel state (any
  capacity `≥ 0`, unbuffered included). `enqueueResponse` returns `ok` with
  `enqueueResult pred r sent ok sent'` (the pure model `filterResp`: dropped responses are
  reported delivered; otherwise `ok → sent' = sent ++ [r']`, `!ok → sent' = sent`); the sent
  values are `respSent` (`respAt` and a non-nil `Header`). `Stop`/`Compact` take
  `watcherAt γ sent ph` (open or already closed) and give `watcherClosed γ sent
  (ph.cancelAfter c)`. Consumer side, as lemmas: `watcher_recv_au` (the `recvAu` of
  `<-w.respCh`, for `Cache.Watch`'s `select`), `wp_watcher_receive`, `isWatcher_isChan`,
  `wp_watcher_cancelResp` (`w.cancelResp` after `watcherClosed`: `cancelAt p c`),
  `watcher_received_prefix(_closed)`.
- **notifier** (`InvNotifier.lean`): `newNotifier`, `notify`, `wait`. A notification counter
  (`notifierLb γ k`); `notify` takes a `notifierHandle` (an `RWMutex` token; `newNotifier`
  returns `actualMaxReaders` of them) and gives `notifierLb γ (k0 + 1)`; `wait ctx` returns
  `nil` with `notifierLb γ (k0 + 1)` (a `notify` after the read) or a non-nil error with the
  context done (`notifierWaitResult`).
- **ready** (`InvReady.lean`): `newReady`, `Ready`, `Set`, `Reset`, `waitForState`,
  `WaitReady`, `WaitNotReady`. An epoch counter (`readyEpochLb γ e`), the state in epoch `e`
  being `readyParity e`; `Ready`/`Set`/`Reset` return `readySeen γ e0 b` (state `b` in an
  epoch `≥ e0`; `true` after `Set`, `false` after `Reset`); `waitForState ctx pred` is
  higher-order (`readyPredSpec r pred P`, `P : Bool → Bool`), instantiated with `id` and
  `not`, returning `readyWaitResult` (`nil` with a seen state satisfying `P`, or a non-nil
  error with the context done).
- **`Base.lean`**: `rpctypes`' package facts gained `errorStringSpec` for `ErrCompacted`
  (its `Error()` returns some string), which `Compact` calls; the two store proofs that
  destructure `rpctypesInit` were adjusted (patterns only).
- **New `sorry`s in the trust base** (`etc/tcb-report.py --check --update`: 14 axioms, 4
  sorries): `impl.MessageState`'s generated `MessageState_typed_pointsto` and
  `MessageState_into_val_typed` ("axiomatized type"), reached by `&pb.ResponseHeader{}` in
  `enqueueResponse` (a nil header) and `Compact`: allocating a protobuf message needs the
  message's `IntoValTyped`, which contains its opaque `state` field. They go once
  `protobuf/internal/impl.MessageState` (and the `internal/pragma` types it embeds) are
  translated rather than axiomatized (done 2026-10-09: both gone, see the `EtcdCache`
  section). `Stop`, `newWatcher`, the consumer lemmas, the
  notifier and ready rest on no `sorry`; Perennial's `context` `sorry`s (`WithCancel`, ...)
  are not reached (only `isContext`'s `Done`/`Err` are used).
- **Perennial gaps found**: `Once.wp_Do` takes a persistent closure triple, so a closure
  cannot use the caller's resources; `OnceFrame.lean` proves `Once.wp_Do_frame` (the caller
  lends `R`, gets `R'` back if its closure ran, `R` otherwise) from `isOnce`'s definition.
  `RWMutex` (both specs) needs a token for `RLock`, so there is no persistent `isNotifier`.
  `init_RWMutex`'s `List.replicate (Int.toNat actualMaxReaders)` is unfolded by the kernel
  (deep recursion) unless the count is first abstracted with an equation and `rw`
  (`generalize` is not enough; `Proof/newNotifier.lean`). `wp_start` on the closure's triple
  in `Compact` failed looking for a `MethodUnfold` of the `Error` method named by a
  persistent hypothesis (`errorStringSpec`) still in context; clearing it fixed that
  (`Proof/watcher__Compact.lean`).


### The demux (`cache/demux.go`): proved, modulo one Perennial gap (2026-10-09; gap closed, see "Sorry-free")

`newDemux` and `demux`'s `Register`, `Unregister`, `Init`, `Broadcast`, `LatestRev`,
`BroadcastProgress`, `BroadcastProgressTo`, `updateStoreLocked`, `broadcastLocked`,
`broadcastProgressLocked`, `broadcastEventsLocked`, `Purge`, `purge`, `Compact`,
`resyncLaggingWatchers`: one `Spec`/`Proof` pair each, linked in `Proof/go_etcd_io/etcd/cache/v3/Link.lean` (all at
`HeapGS HasLC.hasLC`). Out of scope (the Cache stage): `NewDemux`, `resyncLoop`,
`WaitForNextResync`. Vocabulary and every shared lemma in `InvDemux.lean` (no `sorry`);
design and rejected alternatives: `decisions.md`, "demux: the delivery invariant under the
lock".

- **State.** The writer's `DemuxCore` (`minRev`, `maxRev`, the history's batches, the ghost
  `stream` of every batch since the last purge; a `Batch` is the events of one revision,
  `batchRev` the ring's `revOf`), invariant `DemuxInv`; the watcher maps, the registrations
  (ghost map `w ↦ RegInfo`: names, resolved start `s`, filter agreement) and their `View`s
  (stream, `maxRev`, next revision `n`, phase active/lagging/closed) live in the lock
  (`RegsOk`; the Go maps are `actOf views`/`lagOf views`).
- **The delivery theorem** (`Unregister`'s postcondition, `DeliveredLog`): when a registrant
  unregisters its watcher, the watcher is closed after a log `sent` such that the events sent
  are exactly the events of the stream batches with `s ≤ revision < n` (for the watcher's
  last `n`), filtered by its key predicate, in stream order (so no gap and no duplicate); the
  log is in order (responses' events strictly increasing from one response to the next, and a
  progress notification at `p` is at or above every earlier event and below every later one);
  and a compaction cancel is at `n`. `demux_watcher_delivered` gives the same at any time under
  a read lock, combined with the consumer: what it received is a prefix of such a log.
- **Overflow premise.** `DemuxInv` has `maxRev < 2^63 - 1` (so `maxRev + 1`, `lastRev + 1`,
  `PeekOldest() + 1` do not wrap); `Broadcast` takes it of the response
  (`RespRevsBounded`: header and event revisions below `2^63 - 1`). Also: events sorted
  (`EvRevSorted`, as for the store), `newDemux`'s capacity in `(0, 2^61]`.
- **`Register`'s premise `watcherUnique w γ`** (`w` has no other ghost name): needed to know
  `w` is not registered yet; not derivable from `isWatcher`. The Cache stage has to get it
  from `newWatcher` (e.g. a registry of `respCh` points-tos), which today does not provide it.
- **Findings against the design:** (1) `minRev` is not a lower bound of the history's
  revisions: `Broadcast` checks events against `maxRev` only, so `Init(100)` then an event at
  5 keeps a batch below `minRev` (etcd's watch from 100 never sends it). `DemuxInv` keeps only
  "every stream batch at or above `minRev` is in the history", which is what resync needs; the
  delivery invariant is unaffected. (2) `resyncLaggingWatchers`'s outcome is not observable
  outside the lock: its postcondition `∃ c views views', ResyncStep c views views'` is proved
  with the lock's real views (the loop tracks `ResyncOutcome` per key) but is satisfiable
  trivially as a statement. No case where the delivery invariant breaks.
- **`sorry`** (closed 2026-10-09: Perennial's `6519b44f5` proves it, `MapRangeMut.lean` is
  gone; see "Sorry-free"): one, `wp_map_for_range_mut_keys` (`MapRangeMut.lean`), a **Perennial gap**:
  `broadcastProgressLocked`, `broadcastEventsLocked` and `resyncLaggingWatchers` write the map
  they range over (current key only, which Go allows), and Perennial's `map.forRange` keeps the
  map `StartRead`-locked for the whole loop, so a write in the body is stuck: the lemma is what
  Go guarantees and is false in Perennial's present model. Fix in Perennial: read the domain
  once, then look each key up when it is visited (skipping deleted keys). Also reached: the two
  known `impl.MessageState` sorries (`&ResponseHeader{}` in the progress responses; gone
  2026-10-09, `MessageState` is now translated).
  `etc/tcb-report.py --check --update`: 14 axioms, 5 sorries (the baseline gained
  `wp_map_for_range_mut_keys`). `lake build` passes; `etc/gen-link.py --cache` reproduces
  `Proof/go_etcd_io/etcd/cache/v3/Link.lean`.

### Key predicates and request validation (`cache/predicate.go`, `cache/cache.go`): proved (2026-10-09)

`ExactKey`, `FromKey`, `Range`, `KeyPredForRange`, and `Cache`'s `validateRange`,
`validateGet`, `validateWatch`, `Ready`, `WaitReady`, `RequestProgress`: one `Spec`/`Proof`
pair each, linked in `Proof/go_etcd_io/etcd/cache/v3/Link.lean`; vocabulary in `InvCache.lean`. No `sorry`, no axiom
(`etc/tcb-report.py --check` unchanged: 14 axioms, 3 sorries; the unsupported-option errors
reach Perennial's `fmt.wp_Errorf` `sorry`, already in the baseline).

- **Newly translated** (`client/v3.toml`, with bodies): the 16 `Op` getters the cache reads
  (`IsCountOnly`, `IsPrevKV`, `IsSortSet`, `Limit`, `Min/MaxModRev`, `Min/MaxCreateRev`,
  `IsFragment`, `IsCreatedNotify`, `IsFilterPut`, `IsFilterDelete`, `RangeBytes`, `Rev`,
  `IsSerializable`, `IsProgressNotify`), `GetPrefixRangeEnd`, `getPrefix` and the variable
  `noPrefixEnd`; each proved (`Spec/go_etcd_io/etcd/client/v3/Op__*.lean`, `getPrefix`, `GetPrefixRangeEnd`).
  `OpOption`s, `OpGet`/`OpWatch` are not (the `Get`/`Watch` stage decides how to model them).
- **`bytes.Compare` is now in Perennial** (Perennial `d292dc284`, pinned here): it calls
  `internal/bytealg` (assembly), so `bytes.toml` marks it trusted, with a model in
  `TrustedCode/bytes.lean` (compare the contents as strings) and `bytes.wp_Compare` proved
  from it (`compareResult`). Push Perennial before this repository.
- **Keys** are `GoString`s (a `[]byte`'s contents); the predicates are `exactKeyPred`,
  `fromKeyPred`, `rangePred` and `keyPredForRange start end` (`GoString → Bool`, in
  `go.GoStringLt`), and `mem_kvRange` says `kvRange`'s entries are exactly the map's entries
  whose key satisfies `keyPredForRange` (for `Get`/`Watch` to agree). The closures keep the
  key slices: the specs take them read-only (`↦*□`) and return `keyPredSpec f p`
  (`InvWatcher.lean`) with `f ≠ nil`, i.e. `keyPredOk f (some p)` for `newWatcher`.
- **`validateRange`** returns `rangeErr`: `nil` iff `validRange prefix start end`, else the
  value of `ErrKeyRangeInvalid`; `prefixRangeEnd` is `GetPrefixRangeEnd` as a function.
  **`validateGet`/`validateWatch`** return `validateResult`: some non-nil error (the
  `fmt.Errorf` wrapping of `ErrUnsupportedRequest` is not modelled) if the `Op` asks for an
  unsupported option (`OpModel.getUnsupported`/`watchUnsupported`), else `rangeErr`'s
  outcome with a nil predicate, else `nil` and the `KeyPredForRange` closure for
  `[key, op.RangeBytes())`. `Base.lean`'s package facts gained `ErrUnsupportedRequest`,
  `ErrKeyRangeInvalid` (cache) and `noPrefixEnd` (`clientv3`).
- **`isCacheFields c cf γr γd cap`** is a partial, persistent `Cache` predicate (fields
  `prefix`, `cfg`, `ready`, `demux`, with `isReady`/`isDemux`); the `Cache` stage extends it.
  `Ready`/`WaitReady`/`RequestProgress` are the `ready`/`demux` specs through it.
- `lake build` passes; `etc/goose.py --check` passes; `etc/gen-link.py --cache` reproduces
  `Proof/go_etcd_io/etcd/cache/v3/Link.lean`.

### Cache.Get and the etcd model (2026-10-09)

`Cache.Get` is proved end to end, with `Cache.serverRevision`, `Cache.waitTillRevision`,
`conditionalProgressRequestor.add`/`remove`, and the `clientv3` functions that build a `Get`'s
`Op` (`OpGet`, `NewOp`, `Op.applyOpts`, `IsOptsWithPrefix`, `IsOptsWithFromKey`, `WithLimit`,
`WithRev`, `WithPrefix`, `WithRange`, `WithFromKey`, `WithSerializable`, `WithCountOnly`,
translated with bodies in `client/v3.toml`): one `Spec`/`Proof` pair each, linked in
`Proof/go_etcd_io/etcd/cache/v3/Link.lean`. No `sorry`. Design: `decisions.md`, "The etcd
model".

- **The model** (`InvEtcd.lean`): `axiom etcdState rev pfx s` (etcd's state at `rev`, keys with
  prefix `pfx`, as `EtcdKv` contents) and `axiom etcdState_agree` (one state per revision).
  `isEtcdKvs rev pfx m` (a definition, persistent): the map `m`'s `*KeyValue`s hold, in order,
  such a state (`kvValAt`, read-only fields), keys sorted with prefix `pfx`;
  `isEtcdKvs_agree`: same revision, same keys and contents. Contents rather than pointers,
  because each response allocates fresh `KeyValue`s (pointer agreement would be false of the
  real client).
- **The client**: `isEtcdKV kv pfx` is a definition, the triple of `kv.Get(ctx, key, opts...)`
  for options with model transformers `gs` (`optsAt`, `optSpec`, `OpFull` in
  `client/v3/InvOp.lean`, covering every field `toRangeRequest` sends): any error; or a header
  revision `r` with `isEtcdKvs r pfx m` for some `m`, and, for a prefix get
  (`OpFull.isPrefixGet`), `resp.Kvs` lists exactly `m`. It is a premise (`isCacheFields`), not
  an axiom: the Cache stage will assume it of `client.KV` (the axiom about the client). Since the
  `etcdReached` change (top section) the triple is also linearizable: it takes `etcdReached lo`
  and returns `etcdReached r` with `lo ≤ r` for a non-serializable request.
- **The Get theorem in words** (`Spec/go_etcd_io/etcd/cache/v3/Cache__Get.lean`,
  `cacheGetResult`): for a reader of the store (with a lower bound `r0`), options that do not
  make `OpGet` panic, and `o` the request's `Op`, `c.Get(ctx, key, opts...)` returns either
  `nil` and an error — the context done, an unsupported option, a range outside the prefix
  (`ErrKeyRangeInvalid`), and for a linearizable request the client's error, a revision above
  etcd's (`ErrFutureRev`, with the etcd revision it saw), or `ErrCacheTimeout`; or the store's
  `getSnapshot` error — or a fresh response, owned by the caller, whose header revision is the
  store's latest revision in some state `st` (at least `r0`) and whose `Kvs`/`Count` are the
  key-values in `[key, o.rangeEnd)` of the snapshot `(r, m)` that `snapModel st o.rev` picks
  (the greatest cached revision at most `o.rev`, or at most the latest for `0`;
  `snapModel_ok_spec`: `r ≤` the latest revision), where **`m` is etcd's state at `r`**
  (`isEtcdKvs r prefix m`); and, unless the request is serializable, etcd had a state at a
  revision `serverRev` with `o.rev ≤ serverRev ≤` the latest revision of `st` (the answer is at
  least as fresh as etcd when the call started). Note: for `rev = 0`, `r` need not be the latest
  revision (a progress notification moves it without a snapshot); the header still reports it.
- **Store generalization**: the store's lock-protected predicates take a certificate
  `E : w64 → KvMap → IProp GF` (`storeLockInv`, `storeReader`, `storeWriter`,
  `storeLockedPhys`); every history snapshot carries `□ E r m` (ring item `snapCert E`);
  `newStore` takes `E`; `Restore` asks for `□ E rev (restoreMap kvs)`; `Apply`/
  `applyEventsLocked` ask for `snapCerts E` of every snapshot they append (`applyRespSnaps`,
  `applyEventsSnaps`); `getSnapshot` returns `snapCert E p (r, m)`, `Get` `□ E r m`. Other store
  statements unchanged; `isStore` now fixes `revCond`'s locker to `sync.rlockerOf (s.mu)`. The
  cache's `E` is `etcdCert prefix`.
- **`isCacheFields`** gained `store` (`isStore`, with `cf.γs`, `cf.scap`), `kv` (`isEtcdKV`),
  `progressRequestor` (an interface holding `*conditionalProgressRequestor`,
  `isProgressRequestor`: `mux` guards the waiter count, `cond` a `Cond`). Readers of the
  store use `cacheReader cf` (a store reader token): `Get` and `waitTillRevision` take it and
  give it back; where clients get them from is the Cache stage's.
- **`waitTillRevision`**: `nil` only with `storeRevLb γs rev`, else `ErrCacheTimeout` or the
  context's error (`waitResult`). Proved, including the goroutine (`select` on the
  `time.After` channel and `ctx.Done()`, then `revCond.Broadcast()`) and `revCond.Wait()` under
  the read lock.
- **Perennial (`48e1192c7`, pinned)**: `sync.toml` translates `rlocker.*`;
  `sync_proof/rlocker.lean` proves `RWMutex.wp_RLocker`, `rlocker.wp_Lock`/`wp_Unlock`,
  `rlocker_isLockerWith`; `isLockerWith` (a locker whose `Lock` needs a resource that `Unlock`
  gives back) and `Cond.wp_Wait_with`; `time.wp_Since` is a new Perennial axiom (like
  `wp_Now`/`wp_Until`: `time.Since` is not translated). Push Perennial first.
- **Trust base**: new axioms of this repository `etcdState`, `etcdState_agree` (see the
  `tcb-baseline.txt` diff in the commit); `isEtcdKV` is a premise, to become the client axiom
  at the Cache stage.
- **Remaining gaps**: the client axiom itself (where `client.KV` enters, `New`); the `Watch`
  side of the model (the watch loop must produce `isEtcdKvs` for every snapshot it appends,
  `applyEventsSnaps`); `conditionalProgressRequestor.run`; `WaitForRevision`.
- **Gates** (2026-10-09, Perennial `48e1192c7`): `lake build` passes (1370 jobs);
  `etc/tcb-report.py --check`: 5 axioms (`etcdState` new; `etcdState_agree` is not reached by
  any linked result, only by the lemma `isEtcdKvs_agree`), 2 sorries (unchanged);
  `etc/goose.py --check` passes; `etc/gen-link.py --cache` reproduces `Link.lean`;
  `etc/verified-code.py --reuse`: the cache package 66 of 107 functions verified (636 of 1204
  lines), `clientv3` 31 functions.

### The watch loop and Cache.Watch (2026-10-09)

`Cache.Watch` is proved end to end, with `Cache.watchEvents`, `Cache.applyStorage`,
`Cache.get`, `Cache.WaitForRevision`, and the `clientv3` functions `OpWatch`,
`WithProgressNotify`, `WithCreatedNotify`, `WatchResponse.Err` (translated with bodies), and
(since the fixes below) `Cache.watch`, `getWatch`, `getWatchLoop`; out of scope as planned:
`New`/`newCache`, `Close`, `NewDemux`/`resyncLoop`/`WaitForNextResync`,
`progressRequestor.run`, `realClock`/`realTimer`. Design: `decisions.md`, "The stream model:
`EtcdStep`, certificates through the demux".

- **Verified against the code as shipped (2026-10-09; supersedes the fixed-code verification).**
  The verified code is upstream main plus the readiness fix only: `goose-revert` at `ab1deb078`
  (`64313a1f8` kept; `a7de41a72` and `21ac13e0d` reverted, `43c553f32` and `ab1deb078`). See
  "The cache as shipped" (top) and `decisions.md`, "No code changes unless a bug". From
  2026-10-09 until then the verified code was `goose-lean` `6ab61a1c7`, with all three commits,
  and `watch`/`getWatch`/`getWatchLoop` were proved with a single store writer (a token threaded
  through the loop and handed back through `applyErr`, `Handoff.lean`).
  - `Cache.watch`: with the demux's writer (and the revision bound), the wait-group token, the
    store's newest snapshot at least `R` and `0 < rev ≤ R + 1`, returns a non-nil error, the token
    and the demux's writer; it does not wait for the iteration's goroutine, which is one of the
    store's writers (`applyStorage` needs only `storeSnapLb (rev - 1)`).
  - `Cache.getWatch`, `Cache.getWatchLoop`: the demux's writer and the wait-group token through.
  - `watchEvents` watches in the internal context; the stream it opens is never canceled before
    the cache is (see finding 1b).
- **The stream model** (`InvEtcd.lean`). One new axiomatized proposition, `EtcdStep r0 r1 pfx
  evs`: etcd had no event under `pfx` strictly between `r0` and `r1`, and its events at `r1` are
  `evs` (etcd's contents, `EtcdEv`); `r0 ≤ r1`, `r0 < r1` for events. Two property axioms:
  `etcdStep_transfer` (`etcdState a pfx s` for `r0 ≤ a < r1` gives `etcdState r1 pfx
  (applyEvsState s evs)`) and `etcdStep_compose` (a step without events then a step is a step).
  The bridge `isEtcdKvs_step` (proved) turns a map that is etcd's state at `Y` and a step from
  `p ≤ Y` whose events the store's batch matches (`evsMatch`) into etcd's state at the batch's
  revision: what certifies the store's snapshots from the watch stream.
- **The client's watch** (`isEtcdWatcher`, a definition like `isEtcdKV`): a prefix watch from
  `rev > 0` returns an SPSC channel whose responses satisfy etcd's watch contract from the
  position before to the one after (`watchRespOk`: an error, the created notification, a progress
  notification with its step, or sorted events above the position, below `2^63 - 1`, in batches
  each the step after the previous one); `etcdWatch_recv_au` is the receive.
- **Certificates through the demux**: `isDemux d γd cap C`, `demuxWriter … C`, …, for a
  certificate `C : DemuxCert GF` (the cache's: `etcdStepCert pfx`). The lock holds the stream's
  certificate chain from `DemuxCore.base` (the revision before `Init`'s); `Broadcast` takes, for
  an accepted response, `respCert` (its batches chained from the stream's last batch; a progress
  notification at or above `base`). A watcher publishes, for each log its producer had, the
  delivery facts and the delivered batches' chain (`demuxPub`, `WatcherPub`; the consumer learns
  it at each receive, `watcher_recv_au`), from a revision below its start (`RegsStart`). The
  demux's other statements are unchanged but for the `C` argument; `Register` takes the
  watcher's publication and `watcherUnique w` (now an exclusive half of `w.keyPred`'s points-to,
  produced by `newWatcher`).
- **The Watch theorem in words** (`Spec/go_etcd_io/etcd/cache/v3/Cache__Watch.lean`,
  `cacheWatch_delivery`): for a context, options (`OpWatch` must not panic) and a demux token
  and wait-group slot (`cacheWatchSlot`), `c.Watch(ctx, key, opts...)` returns a channel; if
  `WaitReady` fails it is closed and empty; if the request is rejected (`validateWatch`) it holds
  one canceled response and is closed; otherwise, with `o` the request's `Op`, the responses the
  caller receives, in order, are a prefix of the responses the demux sent the watch's watcher,
  possibly followed by the compaction's cancel response, and for every prefix received:
  the events received are exactly the events of a list of etcd's batches `b_1 … b_k` (each the
  events of one revision, increasing) whose keys are in `[key, o.rangeEnd)`, in order, with no gap
  and no duplicate; each `b_i` is certified by etcd's step from at most `b_{i-1}`'s revision
  (`EtcdStep`: its events are etcd's events at that revision, and nothing under the prefix
  changed in between), `b_1` from a revision `p₀` below the start revision `o.rev` when it is not
  `0`, and every `b_i` is at or above it: nothing etcd did under the prefix from `o.rev` on is
  missing; the responses are in order (`SentOrdered`: events increase from response to response,
  and a progress notification is at or above every earlier event and below every later one); a
  compaction cancel at `n` comes after every batch below `n` was sent.
- **The loop's pieces**: `watchEvents` (the demux's writer, `cacheWriter`: certifies every batch
  it broadcasts from the watch's steps, through its knowledge `TailOk`/`CursorOk` of where the
  stream is; `readyOnce.Do(Init; Set)` with the framed `Once`), `applyStorage` (the store's writer:
  every snapshot `Apply` appends is etcd's state at its revision, from the store watcher's
  publication and the bridge), `get` (`Restore` of etcd's state at the response's revision; it
  needs etcd's linearizability: finding 4; now from `etcdReached`), `WaitForRevision`.
- **`Cache.Watch`'s premises and costs**: `cacheWatchSlot` (a demux token and a wait-group
  budget token, both kept by the goroutine: each `Watch` spends one of the `2^31 - 1` slots of
  `cacheWgInv`, which keeps the `int32` counter from overflowing); `isCacheFields` gained the
  watcher, internal context, clock (`isClock`/`isTimer`, definitions: the clock's trust boundary,
  to be met by `realClock`), the wait group (Perennial's `isWaitGroup`, no waiters: `Close` is out
  of scope) and `0 ≤ PerWatcherBufferSize` (finding 5). The rejected request's cancel reason is
  `err.Error()`: Perennial's `fmt.wp_Errorf` (still a `sorry`) now says `Error()` returns some
  string (Perennial `099c2a08b`), and the package facts say so of `ErrKeyRangeInvalid`.
- **Perennial** (pinned at `099c2a08b`, on `640a605cc`, on `48e1192c7`; push Perennial first):
  `640a605cc`: the channel model's `TrySend`/`TryReceive` return "not ready" on a nil channel
  (they dereferenced it, so a `select` with a nil-channel case was stuck: `Watch`'s
  `case <-progressChan` without `WithProgressNotify`), with `wp_TryReceive_nil`,
  `wp_TrySend_nil`, `nilClausePre`, `chan.wp_select_blocking_nil`/`_nonblocking_nil`;
  `099c2a08b`: `fmt.wp_Errorf`'s error has an `Error()` spec.
- **Findings** (about etcd's cache, `upamanyus/etcd` `48fd5a507`, `cache/cache.go` unless noted;
  since the cache as shipped, only 2 is fixed in the verified code, `ab1deb078`: 1 and 1b are not
  bugs):
  1. *Two writers of the store: not a bug.* `watch` does not wait for an iteration's
     `applyStorage` goroutine before the next iteration, nor `getWatchLoop` before the next
     `get`'s `Restore`: after `Unregister`, the old goroutine keeps draining its watcher's
     buffered responses into `store.Apply`, concurrently with the next writer. The shared-writer
     proof shows this is harmless: a drained response at or below the store's latest revision is
     rejected by `validateRevisions` (`applyResp_stale`) and changes nothing; every revision a
     drain can apply is at most the revision bound, at or below which the next `Get` returns
     (linearizability); an accepted one follows the store's newest snapshot along etcd's steps.
     It does rest on etcd's semantics: a delete event is of a present key
     (`etcdStep_delete_present`), else a failed `Apply` could leave a half-applied map another
     writer builds on. The fix `a7de41a72` is reverted.
  1b. *The upstream watch is not canceled when `watchEvents` returns* (a finding for the
     maintainers, not a correctness issue): `watchEvents` watches in the cache's internal context,
     so each retry leaves the previous client watch (its goroutines, the server-side watcher) open
     until the cache is closed. A resource leak; the proofs are unaffected. The fix `21ac13e0d`
     is reverted.
  2. *The cache can stay not ready after a retry* (**the one bug; fixed by `64313a1f8`, kept**).
     Before the fix, `watch` registered the store watcher (352) before `Init` (406); on a retry whose `Get` revision `R'` differs from the demux's `maxRev`
     (or with `maxRev = 0`), `Init(R'+1)` purges (`demux.go:131-135`, `141-143`), stopping the
     store watcher; `applyStorage` returns `nil` (378-379) and closes `applyErr` (360);
     `watchEvents` receives `nil`, resets `ready` (418-420) and returns `nil`; `watch` loops
     (366-369) with the same `readyOnce` (349), so `Init`/`ready.Set` (405-408, the only `Set`)
     never run again: `Get`/`Watch` block in `WaitReady` until `watch` fails. The first
     iteration's client watch is never canceled (it runs on `internalCtx`), and the next
     iteration re-watches from the original `rev`, whose replayed events `Broadcast` rejects once
     the stream has events (another round of the retry loop). Liveness, not safety: the specs
     are unaffected. **Confirmed in Go (2026-10-09)**: `cache/ready_liveness_test.go` in the
     fork's working tree (not committed; its own per-stream fake watcher, since the tests'
     `mockWatcher` feeds every stream from one channel) drives exactly this: first `Get` at 9,
     event at 10, stream canceled, retry `Get` at 12 → `watch(13)`, `Init(13)` purges (the
     `141-143` branch), `ready` set then reset, a second upstream stream opens (the first is
     never canceled), the event at 13 reaches the store, and `Ready()` stays false:
     `WaitReady` and `Cache.Watch` time out (5 of 5 runs under `-race`, no data race). The
     control with the retry `Get` at 10 (`Init(11)`, no purge) recovers. The retry backoff is
     `defaultConfig().InitialBackoff`, real time, not the cache's clock or `Config`.
  3. *The store watcher starts lagging.* On a fresh demux (`maxRev = 0`), `Register(storeW,
     rev)` with `rev ≠ 0` makes it lagging (`demux.go:89-95`): it gets the stream only at the
     first resync, so the store, and linearizable `Get`s, lag by up to `ResyncInterval` at
     start. Performance only.
  4. *`get` needs linearizability.* `store.Restore` (`store.go:105-117`) does not check that the
     revision does not go back, and the store's readers' lower bounds (`storeRevLb`) need it;
     `isEtcdKV` related no two calls, so `Cache.get`'s spec took `isEtcdKVFrom kv pfx
     st.latestRev` (a prefix get returns at least the store's revision) as a premise. Now
     (`etcdReached`, top section) the writer knows etcd reached its latest revision and the
     client's get is linearizable: no premise.
  5. *`PerWatcherBufferSize` is not validated.* `newCache` (72-77) checks `HistoryWindowSize`
     and `BTreeDegree` only; `WithPerWatcherBufferSize(-1)` makes `newWatcher`'s
     `make(chan, -1)` panic in `Watch` (138) and in the watch loop's goroutine (351), which
     crashes the process. The proofs take `0 ≤ PerWatcherBufferSize` (`isCacheFields`).
  6. The demux's earlier finding, that `validateRevisions` alone accepts after `Init(m)` events
     below `m - 1` when `maxRev = 0`, is now excluded by the certificates (`respCert`): an
     accepted batch is above the stream's last batch, hence above `base`.
- **Not reached**: no `sorry` of this work; the observed flakiness: `Proof/go_etcd_io/raft/
  v3/stepLeader.lean` failed twice in full rebuilds after a Perennial re-pin ("not pure" at
  239, "ambiguous `decide_true`" at 277) and built alone, unchanged, right after; not
  investigated.
- **Gates** (2026-10-09, Perennial `099c2a08b`): `lake build` passes (1397 jobs);
  `etc/tcb-report.py --check` (after `--update`): 10 axioms, 2 sorries — new `EtcdStep`,
  `etcdStep_transfer`, `etcdStep_compose`, and (the `clientv3` commit) `rpctypes.Error.wp_proof`,
  `status.Error.wp_proof` (grpc is not translated); `etc/goose.py --check` passes;
  `etc/gen-link.py --cache` reproduces `Link.lean`; `etc/verified-code.py --reuse`: the cache
  package 71 of 107 functions verified (8 unfinished: the documented `sorry`s), 776 of 1204
  lines (64.5%); `clientv3` 35 functions.

### The whole package (2026-10-09)

Every function of etcd's `cache` package has a `Spec`/`Proof` pair and a linked result: 107 of
107 (`etc/verified-code.py --reuse`: 97 verified, 10 unfinished, 943 of 1206 Go lines verified,
78.2%). This stage added the rest: the ten `Config` options (`InvConfig.lean`), `Prefix.Match`,
the real clock (`realClock.NewTimer`, `realTimer.Chan/Stop/Reset`), the progress requestor
(`newConditionalProgressRequestor`, `run`), the demux's `NewDemux`, `resyncLoop` and
`WaitForNextResync`, and `Cache`'s `WaitForNextResync`, `Close`, `newCache` and `New`
(`InvNew.lean`). `Results.lean` restates the exported results and prints their trust base.
Design: `decisions.md`, "`New` and the client: translating `Client`, timers as the trust
boundary".

- **The client is translated** (Perennial's Goose, no fork change): `clientv3.Client` is listed
  in `client/v3.toml`, and the packages of its fields' types are names-only (`.toml`s with
  `translate = ["!*"]`, `translate_types`): `google.golang.org/grpc`, `grpc/credentials`,
  `client/v3/credentials`, `client/v3/internal/resolver`, `go.uber.org/zap` (five packages;
  `-lean-root go.uber.org=` in `etc/goose.py`). zap's two axiomatized generic types hit a Lean
  backend bug of Goose (Rocq's `∀ (T : go.type), go.type` printed verbatim), fixed in Perennial
  `f35530719` (`GenericTypeExpr`; Rocq output and Perennial's std-lib translations unchanged).
  `Client.cfg` (`clientv3.Config`, with a `*tls.Config`) and four other field types stay
  axiomatized; their `sorry -- axiomatized type` instances are kept out of the trust base by
  high-priority `TypeRepr` instances for `Client` (`InvNew.lean`, as `InvStore.lean` does for
  the protobuf messages).
- **The client's assumption** `isEtcdClient client pfx` (`InvNew.lean`, a definition): the
  `KV` and `Watcher` fields point for good to a `KV` with `isEtcdKV` and a `Watcher` with
  `isEtcdWatcher` and `isEtcdProgressNotifier` (`RequestProgress` returns some error, no
  logical effect; new in `InvEtcd.lean`). Nothing about caches: etcd's linearizability is a
  property of the client's `Get` against the model fact `etcdReached` (what a caller knows etcd
  has reached), which the client's responses produce and the store and demux carry (top
  section; it replaced the quantification over every cache built over the client).
- **Timers are the trust boundary** (Perennial `8c7000190`, axioms like `wp_Now`):
  `time.wp_NewTimer` returns a `*Timer` with `time.isTimer t ch γ` (its `C` field holds for
  good a channel on which a receive yields some time, `isChanBag`, no logical content);
  `Timer.wp_Stop` and `Timer.wp_Reset` (for such a timer) return some `bool`. `realClock`'s
  `NewTimer` proves the cache's `isTimer` from them, so the real clock is an `isClock`
  (`isClock_realClock`, `Proof/.../New.lean`). `resyncLoop` uses `time.NewTimer` directly.
- **`New`'s theorem in words** (`Spec/go_etcd_io/etcd/cache/v3/New.lean`, `newCacheResult`):
  for a client of etcd for the prefix `pfx` (`isEtcdClient`) and options with model
  transformers `gs` (`cfgOptsAt`), the configuration is `defaultConfig()` with the options
  applied in order; if it has `HistoryWindowSize ≤ 0` or `BTreeDegree < 2`, `New` returns `nil`
  and a non-nil error; otherwise, provided the configuration is `CfgBounded`
  (`HistoryWindowSize ≤ 2^61`, `BTreeDegree ≤ 2^62`, `PerWatcherBufferSize ≥ 0`: finding 5's
  premise and two overflow bounds the code does not check), it returns a cache `c` with
  `isCacheFields` (every field, for that prefix and configuration) and its handles: `2^30 - 2`
  readers of the store (`Get`, `WaitForRevision`), `2^30 - 3` watch slots (a demux token and a
  wait-group slot each, `Watch`), `2^30 - 2` handles on the demux's resync notifier
  (`WaitForNextResync`) with its lower bound `0`, and the whole "open" token (`cacheOpen`,
  `Watch` takes a fraction, `Close` all of it); its resync loop, watch loop (with both writers)
  and progress requestor run on its wait group.
- **The other new specs**: `NewDemux` takes the caller's wait group as `wgSlotProtocol` (the
  triples of its `Add(1)`/`Done()`), returns `newDemux`'s resources less the resync loop's demux
  token and notifier handle; `resyncLoop` returns its two tokens once the context is done;
  `WaitForNextResync` (demux's and `Cache`'s) is the notifier's `wait`: `nil` only after a
  notification beyond the caller's lower bound, or the context's error; `run` returns `()`
  (everything it uses is persistent; `isProgressRequestor` now fixes the `cond`'s locker to
  `&p.mux`, `isPrRun` its other fields); `Close` takes `cacheOpen cf 1` and gives it back
  (nothing comes back through the wait group); each `With*` returns a closure with
  `cfgOptSpec f (fun c => {c with X := n})`; `defaultConfig` now returns `defaultConfigVal`.
- **Changed statements**: `isCacheFields` gained `stop` (the cancel function, with its triple);
  `cacheWgInv` admits one waiter, which has deposited `cacheOpen cf 1`, so `Cache.Watch` takes
  and gives back `cacheOpen cf q` (its `Add(1)` must not happen while `Close` waits:
  Perennial's `WaitGroup.Add` from zero needs no registered waiter); `newDemux` returns the
  notifier's handles (`demuxResyncHandle`) and its lower bound.
- **Perennial** (`f8b35ddbf`, on `f35530719`, on `8c7000190`; push Perennial first):
  `context.wp_Background` (proved: `backgroundCtxVal`) and `context.wp_WithCancel_Background`
  (a `sorry`, as `wp_WithCancel`: `Background()`'s `Done()` is `nil`, so it is not an
  `isContext` and `wp_WithCancel` does not apply); the timer axioms; the Goose fix.
- **Perennial gaps found**: `wp_apply` loses track of an `IProp`-typed variable introduced
  by `intro` inside the proof when the applied spec mentions it (here `NewDemux`'s `Pslot`,
  `Prun`): "unknown free variable", or a silent stop reported as unsolved goals at `by`; a
  workaround is to bind the spec's variables with `fun … => by`. A side goal of `wp_apply` (a
  pure premise) may lack the Lean hypotheses `wp_start` introduced (`%H`): frame them from an
  Iris pure hypothesis instead. `wp_for`'s `cleanup_bool_decide` (`try simp`) can silently
  fail on a large context (`Cache.Watch` after `isCacheFields` grew): clearing two unused
  hypotheses fixed it.
- **What the cache's results rest on, since the cache as shipped** (2026-10-09): as below, plus
  the model axiom `etcdStep_delete_present` (`cache_New`), and (superseded 2026-10-10 by the
  thread-token bound and `New`'s thread-bound premise, see "The wait-group counter and thread
  tokens") Perennial's model assumption that
  `WaitGroup.Add`'s `int32` counter does not overflow (trusted code, `TrustedCode/sync.lean`, not
  an axiom: every result using the cache's wait group, `cache_New`, `cache_Watch`, `cache_Close`).
- **What the cache's results rest on** (closed 2026-10-09: the four `sorry`s below are gone,
  see "Sorry-free"; `Results.lean`'s `#print axioms`, by `etc/tcb-report.py`;
  besides Lean's `propext`, `Classical.choice`, `Quot.sound` and Perennial's names-only Go
  declarations, about 855 opaque types of the translation):
  - (since the `etcdReached` change, all of these also rest on `etcdReachedAt` and
    `etcdReachedAt_timeless`, `cache_Watch_delivery` included: the cache's demux certificate
    mentions `etcdReached`.)
  - `cache_New`: the model axioms `etcdState`, `EtcdStep`, `etcdStep_compose`,
    `etcdStep_transfer`; this repository's `rpctypes.Error.wp_proof`, `status.Error.wp_proof`
    (grpc's `status` is not translated); Perennial's `time.wp_NewTimer`, `Timer.wp_Stop`,
    `Timer.wp_Reset`; the `sorry`s `wp_map_for_range_mut_keys` (the demux's map iteration,
    Perennial gap), `fmt.wp_Errorf`, `context.wp_WithCancel`, `context.wp_WithCancel_Background`.
  - `cache_Get`: `etcdState`, `EtcdStep`; Perennial's `time.wp_Now`, `time.wp_Since`; the
    `sorry` `fmt.wp_Errorf`.
  - `cache_Watch`: `etcdState`, `EtcdStep`; the `sorry` `fmt.wp_Errorf`.
  - `cache_Watch_delivery` (the delivery theorem for a received log): `EtcdStep` only.
  - `cache_WaitForRevision`, `cache_WaitForNextResync`, `cache_Close`: `etcdState`,
    `EtcdStep`, no `sorry`.
  The 10 unfinished functions are those whose own proof reaches a `sorry`: `newCache`
  (`wp_WithCancel_Background`, `fmt.wp_Errorf`), `watchEvents` (`wp_WithCancel`),
  `validateGet`, `validateWatch`, `validateRevisions`, `store.applyEventsLocked`,
  `store.getSnapshot` (`fmt.wp_Errorf`), `demux.broadcastEventsLocked`,
  `broadcastProgressLocked`, `resyncLaggingWatchers` (`wp_map_for_range_mut_keys`).
- **Gates** (2026-10-09, Perennial `f8b35ddbf`): `lake build` passes (1472 jobs);
  `etc/tcb-report.py --check` (after `--update`): 10 axioms, 4 sorries (new:
  `sorry Perennial.context.wp_WithCancel_Background`; the roots now include
  `Proof.go_etcd_io.etcd.cache.v3.Results`, 389 root theorems); `etc/goose.py --check` passes;
  `etc/gen-link.py --cache` reproduces `Link.lean`.

## etcd's server: the consistent index and the apply thread (`server/v3/etcdserver`): proved (2026-10-09)

Toward ruling out etcd's consistent-index bugs (manual-notes.txt bullets 3-4). Lean-first; the
shared definitions (`Base`, `BaseApply`, `InvCindex`, `InvApply`, `InvServer`, `InvApplier`,
`InvRaftpb`) and `Link.lean` in `Proof/go_etcd_io/etcd/server/v3/etcdserver/`, every spec and
proof in its package (`.../etcdserver/cindex/`, `storage/schema/`, `go_uber_org/zap/`,
`encoding/binary/`, ...), raft v3.7's getters in `EtcdDeps/{Spec,Proof}/go_etcd_io/raft/v3/raftpb/`;
linked by `etc/gen-link.py --server` (`etc/link-lean-first-server.txt`, 47 results). Design
and rejected alternatives: `decisions.md`, "The consistent index and the apply thread".
Done on branch `apply-thread` on the old layout (`EtcdGrove/Server/`, `EtcdCache/`), and
merged into the layout by kind and Go package path (2026-10-09): every file a module, nothing
in the proofs changed but deprecated `if_pos`/`if_neg`.

- **Translation** (`etc/goose.py`'s etcd project): `etcdserver/cindex` in full;
  `storage/schema`'s `cindex.go`; in `etcdserver` the post-lock hook, `apply`,
  `applyEntryNormal`, `applyEntries`, `setAppliedIndex`, `setTerm` and the types they use
  (`EtcdServer`, `raftNode`, `etcdProgress`, `toApply`). The packages their types name are
  translated names-only or types-only (zap, `net/http`, bbolt, config, membership, apply,
  lease, ...). **etcd's own raft dependency, v3.7** (protobuf-go v2 raftpb: pointer fields,
  getters with bodies) is translated into `EtcdDeps/` (a `Part` of the etcd project). It is not
  the gogoproto fork in `Code/go_etcd_io/raft/`, and both define
  `Perennial.go_etcd_io.raft.v3.*`, so no module imports both, and `etc/tcb-report.py` runs
  `tcb-report.lean` twice. The etcd pin (`6ab61a1c7`) needs Go 1.27 (`GOTOOLCHAIN=go1.27.1`
  where the default Go is older).
- **cindex** (`InvCindex.lean`): `NewConsistentIndex` and the 7 methods of
  `*consistentIndex`, plus schema's `UnsafeReadConsistentIndex`, `ReadConsistentIndex`,
  `unsafeUpdateConsistentIndex` and its two wrappers. The index is mirrored by a ghost
  variable; the specs that read or store it are logically atomic, and the backend's meta keys
  are a client-chosen view, read and written through client-supplied triples.
  `unsafeUpdateConsistentIndex`'s `verify.Verify` assertion is proved never to fire.
- **The protocol** (`InvApply.lean`): ghost `(ci, processed-through p, last entry with writes
  eff, pending)`, with `eff ≤ ci ≤ p` out of flight; a commit saves `ci`, so it persists no
  effects above the saved index and no unprocessed entry at or below it (`commit_save_au`).
- **The apply thread** (`InvServer.lean`, `InvApplier.lean`), proved:
  - the post-lock hook (`getTxPostLockInsideApplyHook`, server.go:2448): under the batch lock,
    `ci := i` for the entry `i = p + 1`;
  - `applyEntryNormal`: the applier's contract with the hook, the writes update; a no-write
    entry gets the deferred `ci` update;
  - `apply`: the loop; entries at or below `ci` are replayed with no backend writes, those above
    are applied in order;
  - `applyEntries`: keeps `loopOk` (processed through the larger of `ci` and `ep.appliedi`)
    and advances `appliedi`; the "unexpected committed entry index" panic is ruled out.
- **Trust boundary** (`etc/tcb-report.py --check`, whole repository: 36 axioms, 3 sorries;
  the server adds the 26 axioms below and no sorry):
  - the applier's contracts `apply.Apply` and `applyConfChange`, with `applierFor` (and
    `applierFor_persistent`): one locked critical section with the hook first, or no writes;
    (2026-10-12, the apply package's unit 3: `apply.Apply` is proved and `applierFor` the apply
    package's definition; only `applyConfChange`'s contract stays: "Unit 3: the server bridge");
  - `pbutil.MustUnmarshalMessage`;
  - names-only callees: zap (`Error`, `Int'`, `Int64`, `String`, `Stringer`, `Uint64`,
    `Logger.Debug`, `Logger.Warn`), `isLeader`, `Logger`, `GoAttach`, `stopWithDelay`,
    `Notify`, `ElectionTimeout`, `AlarmStore.Get`, `Members`, `errors.Is`, `humanize.Bytes`;
  - `BigEndian.Uint64`/`PutUint64` (Perennial translates only `LittleEndian`) and
    `verify.Verify`.

  The only `sorry` the server's results reach is Perennial's `fmt.wp_Errorf`
  (`applyEntries`): with `MessageState` translated as a struct, the `impl.MessageState`
  sorries that `var cc raftpb.ConfChange` reached before the merge are gone.
- **Findings**: `SetConsistentIndex` stores index then term, so a commit concurrent with
  `applyEntryNormal`'s deferred update (outside the lock) can persist the new index with the
  previous entry's term. That entry is a term's first, empty entry, so it is the previous term.
  The term is only read for schema detection and `verify`. Details in `decisions.md`.
- **Not done**: `applyAll`/`applySnapshot` (the snapshot path: `SetBackend` before the lessor's
  `Recover`, the comment at server.go:1055) and the backend side (`BackendHooks.
  OnPreCommitUnsafe`, the commit that calls `UnsafeSave`), whose specs would close the loop
  from the commit's side; establishing the protocol at bootstrap; `applyConfChange` itself.
- **Build** (at the merge): `lake build` passes (1591 jobs); `etc/goose.py --check` passes;
  `etc/gen-link.py --cache` and `--server` reproduce the two `Link.lean`s. One full build
  failed in `Proof/go_etcd_io/etcd/cache/v3/InvDemux.lean:1911` (`slots_take_all`: the
  `iframe` closing `IH`'s premise left `Hrest`, unfolded by `unfold slotRes`, unsolved); the
  unchanged file then built alone and in the next full build. Not understood: watch for it.
