# Requirements on `go.etcd.io/etcd/server/v3/storage/mvcc` (3e mvcc core, 3f watchable store)

## from 2b

Batch 2b (the member's gRPC watch handler, `v3rpc/watch.go`) drives one mvcc watch stream per gRPC
stream. What its sketches (`recvLoop`, `sendLoop`, `close`, `watchServer.Watch`;
`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/`) assume of mvcc's watch API, in plain terms.
The facts are stated against **the cluster's history** (`etcdLb γ σ`, W0's `State.lean`): the
member's store applies the committed log, so its history is a prefix of the cluster's; the bridge
from mvcc's own vocabulary to `γ` is the server's (2d), `req/go_etcd_io_etcd_server_v3_etcdserver.md`,
`## from 2b` (`s.Watchable()`). Model names are 1b's (`client/v3/ApiWatch.lean`: `watchEvents`,
`WatchPos`, `WEv`).

1. **`NewWatchStream()`** (`watchableStore`, through the `WatchableKV` interface): a stream with no
   watcher; its control side (one goroutine: `Watch`, `Cancel`, `RequestProgressAll`, `Rev`), its
   channel's consumer (`Chan()`), `RequestProgress(id)` usable concurrently (from the send loop,
   under v3rpc's lock), its `Close`. No thread token.
2. **`Watch(ctx, 0, key, end, startRev, fcs...)`** (`AutoWatchID`), `end` normalized (`nil`: the
   key; `[]byte{}`: from the key; else `[key, end)`), `startRev ≥ 0`, each filter a function meeting
   mvcc's filter contract (it reads the event struct's `Type` at any fraction and returns whether to
   drop it: v3rpc's `filterNoPut.spec`, `filterNoDelete.spec` are field-level for that). Returns an
   error with a **non-empty** message (an empty range, the stream closed), or an id **fresh on the
   stream** (never returned before by its `Watch`) and **not `-1`**: a lifetime counter (the bounds
   plan: its bound at its owner). The watcher is registered at revision `R` (the store's at
   registration): from `startRev > 0` its position is `startRev - 1`; from `0` the floor `R`
   (events from `R + 1`). Thread token (the store's reader lock).
   ```go
   id, err := sws.watchStream.Watch(ctx, mvcc.WatchID(creq.WatchId), creq.Key, creq.RangeEnd, creq.StartRevision, filters...)
   ```
3. **The channel's responses** (`<-Chan()`), in the order produced, each `WatchResponse` with its
   events as fresh `*mvccpb.Event` structs **owned in full** (v3rpc writes `PrevKv`), their `Kv`s
   read-only (shared among watchers), `PrevKv` `nil`, `Type` `PUT`/`DELETE` and `Kv` as 1b's
   `WEv.ofEvent` (a delete: the key and `ModRevision` only); for a watcher `W` (range, filters,
   start) at its position (its earlier responses):
   * **events**: exactly the range's events not dropped by the filters of the revisions after its
     position (from some revision at most the floor `+ 1` if unknown) up to the last event's `c'`,
     **whole revisions**, in order; `c' ≤ Revision`, `Revision` reached (`etcdLb γ σ` with
     `σ.kv.rev ≥ Revision`); a batch whose events were all dropped is not sent;
   * **progress** (`WatchID = W`, no events, `RequestProgress(W)`): only if `W` is synced and the
     store's revision is not below its start: no event of `W` in `(position, Revision]`;
   * **compaction** (`CompactRevision = cr ≠ 0`, no events): `cr` above `position + 1`
     (`minRev < compactRev`) and at most the cluster's compaction at a reached state; after it no
     event response of `W` (a resend of the compaction is allowed:
     `issues/etcd-watch-compacted-resent.md`);
   * **id `-1`** (`RequestProgressAll`): a progress at `Revision = P` of **every watcher live
     (registered by `Watch`, not yet canceled by `Cancel`) when it was produced** (all synced, `P`
     not below any start), after all their earlier responses;
   * after `Cancel(W)` returns `nil`, no response of `W` is produced (those queued stay).
   The responses produced by `RequestProgressAll`/`RequestProgress`/`Watch` are in the channel
   (or dropped: the channel full) **when the call returns** (v3rpc's drain before a `Created`
   relies on it: `issues/etcd-watch-progress-before-created.md`'s fix).
4. **`Cancel(id)`**: `nil` only for a live watcher (then canceled, as above); else an error. No
   thread token. **`RequestProgress(id)`**, **`RequestProgressAll()`**, **`Rev()`** (a revision the
   member applied: reached): thread token. **`Close()`**: every watcher canceled, the channel closed;
   afterwards `Watch` and `Cancel` fail and `RequestProgress*` send nothing (**no send on the closed
   channel**: v3rpc's receive loop may still call them, `watchServer.Watch`'s context branch). No
   thread token.
5. **`Range(ctx, key, nil, RangeOptions{Rev: r})`** on the watchable KV, `0 < r` below the store's
   revision (`ModRevision - 1` of an event the stream delivered): the key's record at revision `r`
   of the history (`KVHist.storeAt r`), or an error only if `r` is below the member's compaction (at
   most the cluster's at a reached state). Thread token. (v3rpc's `prevKV`, 1b's `WatchReq.prevOk`.)
6. `ReportEventReceived(n)` (metrics): no panic.

Used by: `serverWatchStream.recvLoop.spec`, `sendLoop.spec`, `close.spec`, `watchServer.Watch.spec`
(the run's invariant, `WatchInternal.lean`'s `swsAt`); hence every `srvWireStep` fact of the watch
protocol (1b's `wireStep`), and the snippets `examples/specreq/v3rpcwatch/`.

## from 2d

1. **`KV().Commit()`** (`snapshot`, `createMergedSnapshotMessage`): forces a backend commit (the
   consistent index saved with the state machine's image).
2. **`kv.Restore(newbe)`** (`applySnapshot`): over a backend opened from a snapshot's image (the state
   machine at `histAt γ c`), no error; the store at that image's history.
3. **The member's applied state for readers** (2c's item 6 in `req/..._etcdserver.md`): the store's
   state predicate (`mvccState`) that 2d's invariant can tie to `histAt γ k` for the member's applied
   point (reads see the backend, at or past every `srvApplied`). 2d states the law once 3e names the
   predicate.

## from 2e

1. `V3compactor.revGetter rg` of the store's interface value (`mvcc.New`'s): `Rev()` safe from any
   goroutine at any time, **also after `Close`** (the compactor's loop may run after `Cleanup` closed
   the store: `Stop` only cancels its context). Used by `V3compactor.New.spec`, `NewServer`'s sketch.
2. `EtcdServer.mvccBootCfg cfg` (provisional slot of `NewServer`: `CompactionBatchLimit`).
3. `kv.Close` gives back what `Cleanup` needs to close the backend (its readers: `srvClosers`).

## 3e ↔ 3f: the split (from 3e, for 3f)

3e's vocabulary is up and builds: `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/{Model,ApiStorage,Api}.lean`
(namespace `Mvcc`). What 3f builds on, and what is whose:

1. **The state** `Mvcc.MvccState = {kv : EtcdModel.KVHist, pending : List EtcdModel.Event}` (W0's history,
   so the watch guarantee can be stated in 1b's/W0's terms directly); `σ.notified` (the history the
   watchers were sent: `kv` with `pending` committed), `σ.notify pend`, `σ.commitPending`,
   `σ.compactTo r`, `σ.rev`, `σ.crev` (`-1` before any compaction), `MvccReachable`. `mvccState γ σ`
   (exclusive, the client's) is 3e's; 3f's watch laws take it (as the frozen API's `wsRecv_ok`).
2. **The `KV` contracts at a receiver** (`KV.Read.contract ty v`, ..., `KV.Close.contract`, `isKV`) and the
   transaction contracts (`Txn.*.contract`, `isTxn`) are 3e's. **3f states the canonical specs at
   `*watchableStore`** (every `KV` method, promoted ones included: `watchableStore.Read.spec := ∀ s,
   KV.Read.contract PW #s`, ..., and `watchableStore.Write`, `Restore`, `Close` with their own bodies) and at
   `*watchableStoreTxnWrite` (`Txn.*.contract PT`; its `End` meets `Txn.End.contract`: it fires the first
   update at the notify, the second through the inner `storeTxnWrite.End`), plus `New`/`newWatchableStore`
   (same shape as 3e's `NewStore.spec`, over `mvccStorageFor`, returning `isMvcc (mkOk PW #ws) γ` and the
   stream vocabulary's start), `NewWatchStream` and the stream's methods (`ApiWatch.lean`, 3f's).
3. **Internal specs 3f's proofs use** (3e writes them; internal vocabulary in `Internal.lean`):
   `store.Write` (the plain store's), `storeTxnWrite.End` (the bump, `End`'s second step), `storeTxnWrite.Changes`
   (the change records, `keyValueOwn` of each, for building events), `store.Read`/`rangeKeys` (the
   catch-up read of `syncWatchers` goes through `s.store.kvindex`/`UnsafeRange`: 3e's `Internal.lean` has
   `isStore` with the index and the storage), `store.Restore`, `store.Close`, `store.Compact`.
4. `ReportEventReceived` (metrics.go) is 3e's; `kvsToEvents`, `rangeEvents`, `resyncDelay`, `ChanBufLen`,
   `eventBatch.add` are in 3f's files (3f's).
5. `isMvcc kv γ` is one predicate for both stores (persistent); 3f's `New` gives it at `PW`.

## from 2d (round 1)

4. **The read slot** (2d's completeness F1): mvcc's read specs (`Rev`, `Range`, the `txn` reads) at a
   member's store answer at a history point at or past `k` given 2d's `srvReadAt s γ k`
   (`ApiApply.lean`): state them so that the server's invariant can realize the slot (the store's
   state at `histAt γ k'`, `k' ≥ k`). `ReqReadAfterApplyWait` reads `Rev()` after the wait.

## from 3c

The lessor's API is `Spec/go_etcd_io/etcd/server/v3/lease/Api.lean` (namespace `Lease`). mvcc holds
the lessor as a `lease.Lessor` interface value (`Lease.lessorIface le`, `NewLessor`'s) and calls it
on the apply thread, the lessor's only writer, holding the writer's token `Lease.lessorState γl n
ls` (the lessor's state `LessorState`: live leases, `items` = `itemMap`, `keys` = each `*Lease`'s
item set, the bucket, the backend, the deleter). What 3c needs of mvcc:

1. **Thread the writer's token through the write path.** `put`/`delete` call `GetLease`, `Attach`,
   `Detach` (`lessor.GetLease.spec`, `.Attach.spec`, `.Detach.spec`: `Attach`/`Detach` take
   `lessorState` and return it at `n + 1` with `LessorState.attach`/`.detach`; `GetLease` at the
   writer's own `lessorAt γl n ls` answers `ls.items k`), so mvcc's write specs (and `Restore`'s
   re-attachment, `kvstore.go:398`) take and return `lessorState γl n ls` with the steps they make.
   `Attach` returns `ErrLeaseNotFound` for a lease not live and mvcc then panics
   (`kvstore_txn.go:290`), so a put's lease must be live in `ls` (the txn layer's `checkLease`,
   `Lookup` at the same writer state, 3b).
   ```go
   oldLease = tw.s.le.GetLease(lease.LeaseItem{Key: string(key)})          // kvstore_txn.go:233
   err = tw.s.le.Attach(leaseID, []lease.LeaseItem{{Key: string(key)}})   // :285, panics on err
   ```
2. **The attachment invariant is the store's caller's.** The lessor keeps `items` and each
   object's `keys` as Go does, two maps it does not keep in agreement. A revocation deletes the
   object's `keys`; W0's `State.revoke` deletes the keys whose record names the lease. Whoever holds
   both mvcc's state and `lessorState` (mvcc's writer, or the applier, 3a) keeps
   `∀ k, ls.items k = the lease of k's record (0 if none)` and, for each live `id ↦ e`,
   `ls.keys e.obj k ↔ ls.items k = id`. mvcc's put (detach the old lease, attach the new) and delete
   (detach) keep it; `Restore` re-establishes it after `Recover` (which empties `items` and gives
   fresh objects with empty sets).
3. **The range deleter's contract.** `SetRangeDeleter(rd)` (`lessor.SetRangeDeleter.spec`: takes
   `lessorState`; mvcc's `NewStore` and `newWatchableStore` call it, so their specs take and return
   the token, with `ls.rd` set) and later `Revoke` takes, from its caller,
   `Lease.rdOk γl rd n ls P D Q` for the store's deleter `func() TxnDelete { return
   s.Write(traceutil.TODO()) }`. mvcc's API should export a law or spec giving it, for mvcc's own
   `P` (the store's writer state, inside an apply), `D td ks n' ls'` (the open write transaction
   having deleted `ks`, the lessor at `n'`, `ls'`) and `Q ks n' ls'` (the store's state once the
   transaction committed the deletes at one revision): `rd()` opens a write transaction (`Write`
   locks the batch transaction: `beTxHeld` while it is open, lent by `D`); `DeleteRange(key, nil)`
   deletes the key if present (its delete calls `GetLease`, `Detach` with the borrowed
   `lessorState`); `End()` commits without calling the lessor (the lessor holds `le.mu` then). The
   watchable store's deleter notifies its watchers in `End` (3f). Used by: `lessor.Revoke.spec`,
   3a's `LeaseRevoke` (which combines `Q` with the lessor's post into W0's `State.revoke`).
   ```go
   s.le.SetRangeDeleter(func() lease.TxnDelete { return s.Write(traceutil.TODO()) }) // kvstore.go:117
   ```

## from 3b

What the txn package (3b: `Spec/go_etcd_io/etcd/server/v3/etcdserver/txn/`, namespace `Txn`) needs of
mvcc's API. Its `Api.lean` declares these provisionally, to be replaced by 3e's names: `MvccName`,
`mvccN`, `mvccKV kv γ` (persistent: `kv` is a store, an `mvcc.KV` value: `*store` or
`*watchableStore`), `mvccState γ h` (client-owned, exclusive), `mvccWriter γ` (exclusive), `mvccTxn tx
γ k h evs` (an open transaction), `mvccLessor γ γl` (persistent: the store's lessor is 3c's `γl`).
**The state is W0's `KVHist`** (the events of every revision and the compaction revision, `Model.lean`):
txn's answers are W0's functions of it (`Txn.putAns`, `Txn.run`, `Txn.rangeOut`), so 3e's state
should be it, or project to it by a function.

1. **`Read(mode, trace)`** (either mode, `ConcurrentReadTxMode` or `SharedBufReadTxMode`): with a
   thread token (the store's reader lock), the caller's update `AU <{ ∃∃ h, mvccState γ h }> @ ⊤ \
   ↑mvccN, ∅ <{ mvccState γ h, COMM R h }>` fired at the begin; returns `R h` and `mvccTxn tx γ .read
   h []` (the revision and the compaction are fixed for the transaction: `Compact` waits on `s.mu`).
   Used by: `Range.spec`, `Count.spec`, `Txn.spec`.
   ```go
   txnRead := kv.Read(mvcc.ConcurrentReadTxMode, trace)   // txn/range.go:53, txn.go:43
   ```
2. **`Write(trace)`**: with `mvccWriter γ` (whatever a write transaction needs: the backend's share,
   the post-lock hook's contract that sets the consistent index, 2d) and a thread token; the state
   `h` learned by a peek at the caller's update (opened and closed unchanged); returns `mvccTxn tw γ
   .write h []`, and **no other write commits until its `End`** (the batch transaction's lock and
   `s.mu`). Used by: `Put.spec`, `DeleteRange.spec`, `Txn.spec` (a write).
3. **A transaction's view** (`Txn.viewRev`, `viewStore`, `viewErr` in txn's `Api.lean`): on `mvccTxn
   tx γ k h evs` (any kind), `Rev()` is `h.rev`, `FirstRev()` the compaction revision (`-1` before
   any: W0's `txnRevErr`), `Changes()` has `evs.length` entries; **`Range(ctx, key, end, ro)`**:
   `viewErr h evs ro.Rev`'s error (mvcc's `ErrCompacted`/`ErrFutureRev`, `Txn.errIs`), or an owned
   `*RangeResult` (`Txn.rrOwn rr kvs (viewRev h evs) count`: each `KeyValue` fresh and owned, the key
   bytes read-only (`↦*□`: the index's on the keys-only path), its numbers fitting `int64`,
   `Txn.kvFits`) of the present keys of `viewStore h evs ro.Rev` in the range (`end == nil`: the key
   alone; `[]byte{}`: from the key on; else `[key, end)`), in key order, cut at a positive
   `ro.Limit`; `FastKeysOnly`: lease `0` and no value; `Count` every key of the range if `CountOnly`,
   `WithTotalCount` or no limit, else at most the limit; **at most `2 ^ 62` key-values** (Perennial's
   `sort.Sort` limit, local to the sort: `sortRangeResults.spec`); or, only once the context is done
   and not for `CountOnly`, `fmt.Errorf`'s error (`Txn.ctxErr`, with `Context.ctxDone ctx`). Used by:
   `executeRange.spec`, `getPrevKV.spec`, `applyCompare.spec`, `deleteRange.spec`, `checkRange.spec`.
   ```go
   rr, err := txnRead.Range(ctx, r.Key, mkGteRange(r.RangeEnd), ro)   // txn/range.go:71
   ```
4. **`Put(key, value, lease)` on a `.write` transaction**: appends `.put key (record)` with W0's
   `PutReq.record` at revision `h.rev + 1` over the key's record in the pending store
   (`h.store.applyEvents evs`), returns `h.rev + 1`; with the lessor's writer token `Lease.lessorState
   γl n ls` (3c), the lease `0` or live in `ls` (else `Attach` errs and mvcc panics), returning it
   with only the attachments changed (`Txn.sameLeases`) and **`Txn.attached` kept** for the new pending
   store. **`DeleteRange(key, end)`**: the present keys `l` of the pending store deleted
   (`Txn.delEvents l`), returns `(len l, viewRev h (evs ++ delEvents l))`, the lessor's token likewise
   (detaching). Used by: `put.spec`, `deleteRange.spec`.
5. **`End()`**: a read transaction's gives the thread token back; a write's commits `evs` at one
   revision (`h.commit evs`), firing the caller's update there (txn passes the update its caller
   gave: `AU <{ ∃∃ h, … mvccState γ h }> … <{ mvccState γ (h.commit evs), COMM … }>`; with nothing
   pending, the update may be closed unfired), and gives back `mvccWriter γ` and the thread token.
6. **`NewReadOnlyTxnWrite(tr)`**: from `mvccTxn tr γ .read h []` to `mvccTxn tw γ .roWrite h []` (the
   same view; its `End` ends the read; its `Put`/`DeleteRange` panic, never called on a read-only
   transaction). The view's methods take the transaction at any interface type (`TxnRead`,
   `ReadView`, `TxnWrite`: the same dynamic value).
7. **Revisions fit**: `mvccState γ h ⊢ ⌜h.rev + 1 < 2 ^ 63⌝` (as W0's `etcdState_revFits`, from the
   same budget at the owner), so a write's revision and every record's numbers fit `int64`.


## from 3a

The apply layer (3a) holds mvcc's store exclusively on the apply thread: `Apply.kvSt kv h` (the
store at W0's history `h`) and `Apply.kvOk kv R` (persistent: writes run the backend's post-lock hook
with the apply thread's lent `R`). Needed, besides 3b's `txn` package over it:
1. **`Compact(trace, rev)`**: `ErrCompacted` at or below the compaction revision, `ErrFutureRev`
   above the current one, else the compaction revision moved (W0's `kvStep` compact) and a channel
   closed once the physical compaction is done (`Read.recvAny`, 2c's).
2. **`Range(ctx, key, nil, RangeOptions{})`** at the current revision: no error (`Compaction`'s header).
3. **`Rev()`**: the store's current revision (`newHeader`).
Used by: `applierV3backend.{Compaction,newHeader}.spec`.

## from 2c (round 1)

`mvcc`'s sentinels (`ErrCompacted`, `ErrFutureRev`) hold `srvErrVal e` (`errors/Api.lean`; a law of
the package's initialization).
