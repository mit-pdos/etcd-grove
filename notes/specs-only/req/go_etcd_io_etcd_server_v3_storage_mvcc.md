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
