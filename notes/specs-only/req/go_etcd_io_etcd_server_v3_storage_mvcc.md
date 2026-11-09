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
