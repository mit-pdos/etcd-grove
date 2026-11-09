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

(Round 1: rewritten against 3e's written API, `storage/mvcc/{Model,Api}.lean`, which txn's specs now
cite: `isMvcc`, `mvccState`/`MvccState`, `mvccReaders`, `mvccTxn`/`MTxn`, `mvccLessorIs`,
`mvccBackend` with `hookIs`/`hookRun`, `KV.Read`/`KV.Write`/`Txn.*` contracts, `putLs`/`delLs`/
`delsLs`, `txnStore`, `storeItems`, `kvsFit`, `keysOnlyM`.) What txn (3b) still needs:

1. **A context error is none of the sentinels**: `rangeResOwn`'s `.ctxErr` case gives only
   `err ≠ nil`; txn's `ctxErr err` (and 2c's `srvIndef`) need it to be neither `ErrCompacted`'s nor
   `ErrFutureRev`'s value (it is `fmt.Errorf`'s fresh value, `kvstore_txn.go:122`). Used by:
   `Range.spec`, `executeRange.spec` (`ctxErr_not_errIs`).
2. **A record's lease fits `int64`**: `kvsFit`/`kvSortOk` bound the revisions and the version; txn's
   `compareKV` compares `Lease` as an `int64` (`kvFits`). A law of reachable states (every record's
   lease is some `sint.Z lid`) suffices. Used by: `compareKV.spec`, `rrOwn`.
3. **The trace**: txn passes the trace `EnsureTrace` returned (4b's `TraceUtil.traceOwn`) as mvcc's
   `traceOwn`; identify 3e's provisional `Mvcc.traceOwn` with 4b's.
4. **The write's pin** (noted, no change asked): `Txn.End.contract`'s `⌜σ = σ₀⌝` makes every write
   through `Write`/`End` pinned at the state its transaction began at; txn's `Put`, `DeleteRange` and
   writing `Txn` take their caller's update pinned there (`AU <{ mvccState γ σ₀ }> …`). If 3e gives
   a way to discharge it from the open transaction instead (the writer's lock keeps the state), the
   two single-transaction writes could take an unpinned update, as `KV.Put.contract` does.

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

## from 2e, round 1

`mvccBootCfg_intro`: `0 ≤ CompactionBatchLimit`. `V3compactor.revGetter_intro` is the law your store
proves for `Rev` (with a `threadTok`, at any time, also after `Close`).


## from 3f

Batch 3f (the watchable store and the watch stream: `ApiWatch.lean`, `WatchInternal.lean`, the
`watchableStore*`/`watchStream*`/`watcher*` files, `New`, `newWatchableStore`) builds on 3e's
`Model.lean`, `ApiStorage.lean`, `Api.lean` and `NewStore.lean` as they stood on 2026-11-09. Per the
split above, 3f states the canonical specs at `*watchableStore` (`watchableStore.<M>.spec := ∀ s,
KV.<M>.contract PW #s` for every `KV` method) and at `*watchableStoreTxnWrite` (`Txn.<M>.contract
PT`), `New`/`newWatchableStore` (3e's `NewStore.spec` statement with the handle `watchableAt (mkOk PW
#s) γ`, which implies `isMvcc`: `watchableAt_isMvcc`), and the stream's methods. What 3f's sketches
need of 3e, in plain terms:

1. **Two reader slots parked for a watchable store's loops.** `syncWatchersLoop` and
   `syncVictimsLoop` read under `s.mu`'s and `revMu`'s read sides and through the storage
   (`rangeEvents`'s `ReadTx`) for the store's whole life, outside any client call: `NewStore` must
   keep two of the store's reader slots out of the client's `mvccReaders γ mvccTokN` (parked, for a
   plain store, with its open token, as the frozen API did), and a watchable store's `mvccClosed γ`
   must include them back (`Close` takes them after `wg.Wait()`), so that `mvccClosed_rest` holds as
   stated for both stores. Used by: `New.spec`, `newWatchableStore.spec`, `watchableStore.Close.spec`
   (`oneshot-close.md`).
2. **`mvccReaders` carries a slot of the watchable store's `s.mu`** (its read side): the stream's
   `Watch` (`revMu`), `Rev` (`revMu`), `RequestProgress`/`RequestProgressAll` (`s.mu`'s read side)
   take one reader token and give it back (3e's tokens, not a thread token, for consistency with the
   store's own reads). Used by: `watchStream.{Watch,Rev,RequestProgress,RequestProgressAll}.spec`.
3. **The change records `End` builds events from.** `watchableStoreTxnWrite.End` calls `Changes()`
   and turns each `*mvccpb.KeyValue` into an event: a put's (its `CreateRevision` non-zero, its
   `ModRevision` the transaction's revision `σ.rev + 1`) as is; a delete's (`CreateRevision` `0`,
   only the key set) with `ModRevision` **written** to the revision. Then the records are shared
   read-only by every watcher's event copy (`keyValueOwn kv DFrac.discard`). `Txn.Changes.contract`
   gives only their count: the inner transaction's `Changes` (3e's `storeTxnWrite.Changes`, the
   internal spec) must give the slice's records, each `keyValueOwn` of the `KeyValueM` of the
   transaction's event (`evOf (σ.rev + 1)` of `pend`'s, `ApiWatch.lean`; a delete's with
   `ModRevision` `0` and write access to it), so that the end's events are `evOf` of `pend`.
   ```go
   changes := tw.Changes(); rev := tw.Rev() + 1
   for i, change := range changes { evs[i] = &mvccpb.Event{Kv: changes[i]}
     if change.CreateRevision == 0 { evs[i].Type = DELETE; evs[i].Kv.ModRevision = rev } ... }
   ```
   Used by: `watchableStoreTxnWrite.End.spec`.
4. **The notified history's lower bound `mvccLb γ h` is 3f's** (`ApiWatch.lean`, persistent: the
   store's notified history extends `h`), with two laws against your `mvccState`: `mvccLb_le`
   (`mvccState γ σ ∗ mvccLb γ h ⊢ ⌜histLe h σ.notified⌝`) and `mvccLb_get` (`mvccState γ σ ⊢ |==>
   mvccState γ σ ∗ mvccLb γ σ.notified`). Its realization is one more ghost resource in the store's
   invariant beside your half of `mvccState` (a monotone, prefix-ordered authority of `σ.notified`):
   it grows at a commit's first step (`notify`) and at `Restore`, whose update's premise (`σ.kv.revs
   <+: σ'.kv.revs`, compaction not lowered) is exactly what keeps it monotone (under the watchable
   store's `s.mu` nothing is pending, so `σ.kv = σ.notified`). Please keep `Restore`'s premise as
   it is; no change to your statements otherwise. Used by: every watch fact (`wsRespOk`), the
   stream's `Rev`, `Watch`'s registration revision.
5. **The storage's image keeps whole revisions above the compaction.** `rangeEvents` reads the `Key`
   bucket between two revisions (`UnsafeRange(Key, rev(min), rev(max), 0)`) and turns each entry into
   an event: 3f's sketch needs that the image of a history (`mvccImage D h u`) holds, in revision
   order, every event of every revision above `h.compacted` and, at or below it, each key's last
   change at or below it (a tombstone kept for a delete), and nothing else; with `revEnc`/`kvEnc`
   (`WatchInternal.lean`: the revision key's encoding and tombstone mark, the key-value's protobuf
   encoding) the meaning of an entry. A law of `ApiStorage.lean` over `kbRead`/`rangeOk` at an image
   would serve. Used by: `rangeEvents.spec`, `kvsToEvents.spec` (hence `syncWatchers.spec`).
6. **`NewStore.spec`'s statement** is copied into `New.spec` and `newWatchableStore.spec` (with the
   handle `watchableAt`, and the loops' shares for the latter). If you change it, say so here (or
   factor it as an `abbrev` over the constructor value and a handle, so that both are instances).
   The lessor's deleter is set twice (`NewStore`'s, then `newWatchableStore`'s, to the watchable
   store's `Write`); 3f assumes `RestoreLs` keeps the deleter field as given (`{ls with rd := rd}`
   restored is `{(RestoreLs ...) with rd := rd}`), so the post's form stays with the final deleter.
7. `ReportEventReceived` (2b's item 6) is yours (`metrics.go`).

## from 3f, to 2b (the watch stream's statements, for item 1-4 of "from 2b")

What `ApiWatch.lean` gives, against 2b's request: the stream's facts (`wsRespOk`, through
`wsCons_recv`: a plain receive, a `select` case, and the drain's non-blocking receive whose empty case
bounds the stamp `wsSentLb` a `Watch` gave), the registration (`wsReg ι id W`: range, filters, start,
position, stamp), cancellation (`wsCanceled ι id c`), ids fresh and not `-1` (`wsCtl ι n`: every id so
far below `n`), the store's revision (`Rev`, `mvccLb`), `Close` (`wsOpen` spent, `wsClosed`). Three
departures from the request, for 2b to check: (a) the calls that read take **one of 3e's reader tokens**
(`mvccReaders γ 1`), not a thread token: the run must hold reader tokens of the member's store (2d's
`srvWatchable` realization hands them out); (b) **the events and progress facts are exact under the
compaction condition** (`exactFrom h (p + 1)`: every revision from the watcher's next one up to the
store's compaction revision changes each key at most once; the user's mvcc API round 11 and
`watch-compaction.md`): 1b's `watchStep` claims exactness unconditionally, which a compaction at a
revision that put and deleted a key (`issues/etcd-txn-check-intervals-sibling.md`) breaks
(`nonissues/etcd-mvcc-watch-compact-rev-subrev-lost.md`); (c) `Watch`'s id argument is `0` (a scope
restriction: 2b's `watchReqOwn_unfold` gives `WatchId = 0`). The filters' contract is `filterOk f d`
over `evOwn` (the event struct owned: `filterNoPut.spec`'s field-level triple implies it); the events
are `evOwn` (struct owned, `Kv` read-only at `DFrac.discard`, `PrevKv` `nil`).

## from 3c (round 1)

1. **`rdOk`'s delete is constrained** (`lease/Api.lean`): `DeleteRange`'s post gives the token back at
   a state with the same `leases`, `bkt`, `be` and `rd` (only `items` and `keys` move): `delsLs`
   meets it. Please give `rdOk` itself (or a law turning `mvccDeleter rd γ` with your `D`/`Q` into
   it), with `beTxHeld (storageVal B)` lent from the open write transaction (your `kbHeld B`,
   which 4a identifies with `beTxHeld`).
2. **For any closure calling `Write`**: the server's `func() lease.TxnDelete { return
   s.kv.Write(traceutil.TODO()) }` (`server.go:1087`, installed by `Recover`) needs the same
   `rdOk` (2d's to state, from your contract): a law of yours over `isMvcc` handles would serve both.
3. **Reader tokens**: `GetLease` (and `Lookup`, `Keys`) take `Lease.lessorReaders γl 1`; your write
   path holds `lessorState`, which lends one (`Lease.lessorState_reader`).

## from 3f, round 1

1. (to 3e; review S1) `mvccLb`'s laws (`mvccLb_le`, `mvccLb_get`) are plain entailments over
   `mvccState γ σ` alone: the monotone authority of `σ.notified` (or a fractional half of it) must be
   part of `mvccState`'s own realization, not only of the store's invariant.
2. (to 3e) `watchStream.Watch`/`Rev` now fire a read update in your `KV.Rev.contract` form (round 1,
   F2); the watch errors are the package's `ErrEmptyWatcherRange`/`ErrWatcherNotExist` values
   (`globalAddr … ↦□ err`, as your `Compact`).
3. (to 2b) Item (b) of "from 3f, to 2b" is stale: 1b's `watchStep` now takes `exactFrom`. New: a
   compaction response is stated against the watcher's events position (`posEvOf`), since a progress
   does not protect a watcher from a compaction after a snapshot `Restore`
   (`nonissues/etcd-mvcc-watch-compacted-after-progress-restore.md`); reader tokens stay (the
   coordinator's decision): `req/..._etcdserver_api_v3rpc.md`, "from 3f".

## 3e → 3f (round 1 repairs)

Changes 3f's `New`/`newWatchableStore`/watchable instances must follow (all in `Api.lean`/`ApiStorage.lean`):
`NewStore` gives also `mvccRevLent γ 0 ∗ mvccRestoreGate γ 1` and no longer takes `MvccReachable`
(`mvccImage_reachable`); `KV.Rev`/`KV.FirstRev` take `revRd γ rt` (a reader or a `Rev` token);
`KV.Restore` takes `mvccRestoreGate γ 1` and gives `storageRest B mvccReaderN`; `KV.Compact` takes
`rev ≠ 0`, its channel is `(ch : Loc)` with `compactChanOk ch` (`isChan` + `recvAu`) and `ch ≠ null`
on success and `ErrCompacted`; the write updates carry no receipt; `rangeOk` takes the range relation
(`KeyData.range` for the batch, `KeyData.rtRange` for a read transaction; `nil` empty ends). 3f's need 5
(what an image holds above its compaction, for `rangeEvents`): `Internal.lean`'s
`mvccImage_above.spec` (with `kvBytes`, `evM`).

## from 4b

1. **`traceOwn`** is `TraceUtil.traceOwn` (`Spec/go_etcd_io/etcd/pkg/v3/traceutil/Api.lean`,
   exclusive, non-nil); `TraceUtil.TODO.spec` gives `traceOwn t ∗ traceEmpty t true`;
   `TraceUtil.Trace.Step.spec` takes `traceOwn t ∗ fieldsOwn fields` (a variadic call without fields
   passes `nil`: `fieldsOwn` of the nil slice holds).
2. **`Mvcc.bucketVal b` (an opaque constant per bucket) is not provable** of the schema's variables:
   their values hold name slices allocated at the package's initialization. State the storage
   contract's bucket arguments as any `bv` with `Schema.bucketAt .key bv` / `Schema.bucketAt .metaB
   bv` (persistent; `Schema.bucketVars_init.spec` gives the package variable's), or keep `bucketVal`
   as a parameter of the storage's names fixed at the opener. The compaction key names are
   `Schema.keyNames_init.spec` (`schedKey`, `finKey`).
3. `UnsafeCreateMetaBucket(tx)`: `Schema.UnsafeCreateMetaBucket.spec` over `Schema.txWr tx S R` with
   `S.whole .metaB`: mvcc's storage contract's `UnsafeCreateBucket` row is an instance (4a proves
   `txWr` of the batch transaction at mvcc's part).
4. `KeyData.range` of `.metaB` answers every key but the compaction keys with nothing, so the
   contract claims `UnsafeRange(Meta, "consistent_index")` returns nothing, which etcd's backend does
   not satisfy; mvcc only asks its own keys: restrict the row to `k ∈ {sched, fin}` (as the schema's
   `Scope.has`).

## from 4a

4a proves mvcc's storage contract of etcd's backend through `Backend.keyBackend_intro.spec`
(`Spec/go_etcd_io/etcd/server/v3/storage/backend/MvccStorage.lean`; realization in its header). Two
rows of the contract (`ApiStorage.lean`, as of 2026-11-09) are **not true of etcd's backend**; the
law is blocked until they change:

1. **F1: `Unlock` publishes in two steps.** `batchTxBuffered.Unlock` writes the session's puts back
   into the read buffer (`batch_tx.go:330-333`) and only then, if the session deleted, commits
   (`:355-357`): between the two a read transaction (`ConcurrentReadTx`, or `ReadTx().RLock()` from
   the apply thread's `checkPrevCompactionCompleted`) sees the session's puts and **not its
   deletes**. mvcc's compaction's last batch does both (`kvstore_compaction.go:58-71`: the deletes,
   then `UnsafeSetFinishedCompact`), so a reader can see `finishedCompactRev = c` with the batch's
   deleted `key` entries still there. One update (`kbData B D0 → kbData B D`) cannot be fired at a
   single point. 4a's `batchTxBuffered.Unlock.spec` fires two: the visible image to `Sess.mid` (the
   puts over the session's base) at the write-back, then to `Sess.fin` (the batch's) at the commit.
   Options for the row: (a) take two updates, `kbData B D0 → kbData B mid` then `→ kbData B D`, with
   `mid` the session's puts over its base (`kbLocked` would carry the base and the puts); (b) keep one
   update, fired at the write-back, and let a read transaction's `key` range return, besides `D`'s
   entries, entries the session deleted under the safe-range lock (a persistent "deleted" mark minted
   by the delete row; mvcc's reads by revision never ask for a compacted revision; `restore` and
   `hashByRev` would need the marks). (a) is exact; (b) keeps the client's statements smaller.
2. **F3: a `key` put must also be above the keys the session deleted.** The put row's premise is
   "above every key of `D`" (the batch's data); a key deleted earlier in the same session (`D` no
   longer has it) is still in bbolt's read transaction and maybe the read buffer until the commit,
   so a put below it interleaves the read buffer's keys with bbolt's (`rtRange`'s `cs ++ bs`
   unsorted; a non-blocking defragmentation's catch-up skips it). 4a's premise (`Sess.fresh`) is
   "above every key the session began with or sees". mvcc never puts and deletes `key` in one session
   (a write transaction only puts, a compaction batch only deletes), so either premise is met by its
   code; the row needs `kbLocked` to know the session's starting keys, or a "no `key` delete in this
   session" flag.
3. **The lent lock**: `kbHeld B` is realized as the session (`∃ q F S, Backend.beSess γ q F S`); the
   lessor's lease delete under it writes an untracked cell (`beNoVis`), which leaves mvcc's cells
   alone (`beSess_cur` with mvcc's `beCur` in `kbLocked`).
4. **The bucket values** (4b's item 2 above): 4a's law takes `Backend.bucketOk bv bi` of the values
   it is handed; whichever form 3e chooses for `bucketVal`, 4a's law follows.
5. **The snapshot's image** (item 3 of "from 3e"): 4a's `backend.Snapshot.spec` gives `beCommitted γ
   I` (the image is in the client's commit history), not an observation fired under the batch lock:
   between the snapshot's `Commit()` and its bbolt `Begin(false)` another commit can land (a
   compaction batch commits on its own), so no point under the lock pins the image. The server's
   invariant attaches the meaning at each commit (its `commitOk` step, under the batch lock, where
   the visible data is the batch's and `mvccImage_obs` can be fired).
6. **Readers after the close**: the backend's `Close` takes every visible tracker (mvcc's `kbData`,
   through `storageRest`), not the reader slots: in-flight readers finish before bbolt closes
   (`mmaplock`), and a lock-only `RLock` (`kbBare`) is fine at any time, so `kbBareSlot` is just a
   slot (`beRdToks γ 1`).
