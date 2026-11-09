# Batch 3f: mvcc's watchable store and etcd's interval tree

Author's report (round 0, before review). Every file builds: `etc/specs-build.sh --dir
Spec/go_etcd_io/etcd/pkg/v3/adt` (18 modules) and 3f's 64 modules of
`Spec/go_etcd_io/etcd/server/v3/storage/mvcc` (the directory is shared with 3e; 3f's modules are listed
below; the whole directory's build depends on 3e's work in progress). The snippets vet (`cd examples &&
go vet ./specreq/mvccwatch/ ./specreq/adt/`) and, run once against a real store (a scratch test, not
committed: a backend from `backend.NewDefaultBackend`, `mvcc.New` with a `FakeLessor`), every snippet
but `ReqRestore` passes; the adt snippets pass too.

## Files

### `pkg/v3/adt` (namespace `Adt`)

| file | what |
|---|---|
| `Spec/go_etcd_io/etcd/pkg/v3/adt/Api.lean` | the vocabulary: the affine order and intervals (pure), the tree's contents as an ordered entry list, the key kinds (`Cmp`), `keyAt`, `ivAt`, the opaque `ivt`, the visitor contract, laws |
| exported specs (16) | `NewIntervalTree`, `NewStringAffineInterval`, `NewStringAffinePoint`, `NewBytesAffineInterval`, `NewBytesAffinePoint`, `StringAffineComparable__Compare`, `BytesAffineComparable__Compare`, `Interval__Compare`, `intervalTree__{Insert,Delete,Len,Find,Intersects,Contains,Stab,Visit,Union}` |
| `examples/specreq/adt/` | `watchers.go` (`ReqRangeWatchers`: the watcher groups' pattern), `perms.go` (`ReqPermCover`: the auth cache's), `dups.go` (`ReqNestedDeletes`: `checkIntervals`') |

### `server/v3/storage/mvcc`, the watch half (namespace `Mvcc`)

| file | what |
|---|---|
| `ApiWatch.lean` | the watch vocabulary (pure model of a watch, the stream's resources, `mvccLb`, the receive law, laws) |
| `WatchInternal.lean` | internal: the store's invariant and lock (`wsInv`, `wsMu`), the loops' shares, the watcher records, sets, groups, batches (models mirror the code) |
| client-facing specs (8) | `watchableStore__NewWatchStream`, `watchStream__{Watch,Chan,Cancel,Close,Rev,RequestProgress,RequestProgressAll}` |
| the store's canonical instances (20) | `New`; `watchableStore__{Read,Write,Rev,FirstRev,Range,Put,DeleteRange,Compact,Commit,Restore,HashStorage,Close}` (`KV.<M>.contract` at `*watchableStore`); `watchableStoreTxnWrite__{Rev,FirstRev,Range,Put,DeleteRange,Changes,End}` (`Txn.<M>.contract` at `*watchableStoreTxnWrite`); `ChanBufLen` |
| internal specs (32) | `newWatchableStore`, `watchableStore__{watch,cancelWatcher,syncWatchersLoop,syncVictimsLoop,moveVictims,syncWatchers,notify,addVictim,rev,progress,progressAll,progressIfSync}`, `resyncDelay`, `rangeEvents`, `kvsToEvents`, `watcher__send`, `eventBatch__add`, `watcherBatch__add`, `newWatcherBatch`, `watcherSet__{add,union,delete}`, `watcherSetByKey__{add,delete}`, `newWatcherGroup`, `watcherGroup__{add,contains,size,delete,watcherSetByKey,choose,chooseAll}` |
| `examples/specreq/mvccwatch/` | `history.go` (`ReqFromStart`, `ReqFromCurrent`, `ReqWholeRevision`, `ReqFilters`, `ReqCompaction`), `progress.go` (`ReqProgressOne`, `ReqProgressAll`, `ReqDrainBeforeCreated`), `lifecycle.go` (`ReqFreshIds`, `ReqEmptyRange`, `ReqCancel`, `ReqClose`), `store.go` (`ReqStoreWrites`, `ReqRestore`, `ReqCloseStore`) |

## Exported vocabulary

### `Adt` (`pkg/v3/adt/Api.lean`)

Pure (transparent): `affCmp` (the affine order, `""` the top), `affLt`, `IvlS` (an interval
`(begin, end)`), `ivlCmp` (`Interval.Compare`), `ivlLt` (the tree's order), `ivlMem` (a key in an
interval), `pointOf` (`[k, k ++ "\x00")`), `IvlS.queryOk` (a query `Visit`/`Stab` answer exactly),
`ivtCountMax` (`2 ^ 63 - 1`), `Entry` (interval and `any` value), `ivtInsert` (the list after an
`Insert`: after the equal intervals), `stab`, `IvSorted`; `Cmp` (`str`, `bytes`), `Cmp.ty`,
`Cmp.ivl`, `strIvl`, `keyAt c dq v k` (a key value: a string `#k`, or a slice's contents),
`ivAt c p dq z` (an `IntervalValue` holding an entry), `ivVisitorOk` (a `Visit` callback's contract).

Resources: `ivt c t L dq` (opaque, fractional): the `*intervalTree` `t` holds the entries `L` over
keys of kind `c`.

Laws: `ivt_fractional` (split, join, agree), `ivt_persist` (made read-only, persistent),
`ivt_sorted` (in the tree's order, at most `ivtCountMax`), `keyAt_persistent`.

### `Mvcc`, the watch half (`ApiWatch.lean`)

Pure: `evKey`, `MRange.watchMem` (3e's `MRange` read as the watcher groups do: a key, or an affine
interval), `EvM` (an event as delivered: delete flag, `KeyValueM`), `evOf` (a history event as
delivered), `WatcherM` (range, filters' drop predicates, start revision, position at registration,
stamp), `WatcherM.keeps`, `wEvents W h lo hi` (the watcher's events of revisions `lo..hi`),
`exactFrom h lo` (**the compaction condition**), `WResp` (a response), `posOf W id rs` (a watcher's
position after the responses received), `respShape`, `progStep`, `wStep` (what a response of a
watcher says), `histLe` (a history extends another).

Resources (opaque): `mvccLb γ h` (persistent: the store's notified history extends `h`),
`watchableAt kv γ` (persistent: a watchable store), `WsNames`, `wsChanOf ι`, `wsAt w γ ι`
(persistent: a stream), `wsCtl ι n` (the control side: ids so far below `n`), `wsOpen ι` (the close
right), `wsCons ι rs` (the consumer: `rs` received), `wsReg ι id W` (persistent: a registration),
`wsCanceled ι id c` (persistent: no response of `id` after the first `c`), `wsClosed ι`
(persistent), `wsSentLb ι n` (persistent: at least `n` sent).

Definitions: `evOwn` (an event message: struct owned, `Kv` read-only, `PrevKv` `nil`), `wrespAt` (a
`WatchResponse` value), `filterOk f d`, `filtersAt fcs ds`, `errMsgOk err msg`, `wsRespOk γ ι rs r`
(**what a received response says**), `wsRecvPost`.

Laws: `mvccLb_le` (with 3e's `mvccState γ σ`: `histLe h σ.notified`), `mvccLb_get`,
`watch_persistent`, `wsReg_agree`, `wsCanceled_mono`, `wsSentLb_zero`, `wsSentLb_mono`,
`watchableAt_shape` (a `*watchableStore`), `watchableAt_isMvcc` (3e's handle), `wsCons_recv` (a
receive, plain or a `select` case, and the drain's non-blocking receive), `watch_init` (the package's
watch variables and error values with their messages).

## Main changes from the old specs (`specs-ref`)

* **The watch guarantee is per response, persistent, against a reached history** (`wsRespOk`
  against `mvccLb γ h`), in the shape of 1b's `watchStep`, in place of the frozen API's whole-list
  `wsRecvOk σ S rs` law over the client-owned store and stream states. The stream's state is no
  longer client-owned under atomic updates (`wsState`): registrations and cancellations are
  persistent facts (`wsReg`, `wsCanceled`) and the control side a token (`wsCtl`), since the stream's
  control (v3rpc's receive loop) and consumer (its send loop) are different goroutines and the store's
  state (`mvccState`) is the server's, not v3rpc's. The stamp mechanism (`wsSentLb`, the frozen
  API's A1/A2) is kept: a stream-wide progress covers the watchers registered before it.
* **The compaction condition** (the user's round-11 decision) is kept, as `exactFrom` on the events
  and progress facts only (a compaction response, a response's revision and shape hold always).
* **`mvccLb`**: the one new abstraction; the facts' anchor, related to the client's `mvccState` by two
  laws (3e's state stays the client's).
* **The store's methods at `*watchableStore` are 3e's contracts' instances** (3e's split), including
  `Write`, `Restore`, `Close` and the transaction's `End` (whose two-step update is the notification
  point); `New` is `NewStore.spec`'s statement with the watchable handle.
* **Reader tokens**: the stream's reading calls take one of 3e's `mvccReaders γ 1` (was the reader
  token of the frozen API; 2b's request said a thread token, see open question 4).
* **adt**: one spec per function over a key kind `Cmp` (the old string-affine specs and their
  `_gen`/`_bytes` variants were separate specs: one spec family per comparator); `Contains`' result
  stated as its meaning (coverage of every key) rather than the scan's definition; `Union`'s inserted
  list is the stabbed list itself.
* Scope: filters and from-key ranges in scope; a negative start revision and a caller-chosen id out
  (marked, below).

## Functions left out

* **adt's internal red-black helpers**: `intervalNode.{color,height,min,successor,updateMax,visit}`,
  `intervalTree.{createIntervalNode,find,insertFixup,deleteFixup,rotateLeft,rotateRight,
  replaceParent}`. They are called (by `Insert`, `Delete`, `Visit`, ...), so the brief's rule does not
  cover leaving them out: their specs are the tree proof's own (subtrees and zipper contexts over the
  sentinel-shared node graph: `specs-ref`'s `Proof/.../adt/{Ctx,CtxAt}.lean`, with their proofs; the
  sentinel's `parent` is written by `Delete`), and restating them over opaque node predicates adds no
  client-facing fact. Proposed: port them with the tree's proof. (Open question 6.)
* `intervalTree.Height`, `StringComparable.Compare`, `NewStringInterval`, `NewStringPoint`,
  `Int64Comparable.Compare`, `NewInt64Interval`, `NewInt64Point`, `newInt64EmptyInterval`: no caller in
  the verified code, no old spec.
* `ReportEventReceived` (`metrics.go`): 3e's (the split).

## Open questions for the user

1. **1b's `watchStep` claims exact events unconditionally; mvcc delivers them exactly only under the
   compaction condition.** What the code does: a compaction at revision `c` keeps, of a key changed
   twice in `c`, only its last change; a watcher that reads `c` from the storage afterwards gets one
   event where there were two. Through gRPC such a revision exists: a put and a delete of one key in
   sibling nested transactions (`issues/etcd-txn-check-intervals-sibling.md`, accepted at the pin).
   A client then sees a watch miss the put. mvcc's statement (the user's round-11 choice) is
   conditional (`exactFrom`); 1b's `watchStep`, 2b's `srvWireStep` above it, state no condition, so
   their chain is unsound for that workload. Options: (a) the condition gated into 1b's create (the
   approved old design: the client's watch token carries "no compactor, or no revision writes a key
   twice", which the compacting example proves from its puts-only workload); (b) W0's model excludes
   such revisions (a premise on the gRPC layer that the code does not meet: the sibling bug).
2. **`Watch` with a caller-chosen id is out of scope** (the spec takes `id = 0`). A chosen id can
   reuse a cancelled watcher's id, whose queued responses then read as the new watcher's
   (`issues/etcd-watch-id-reuse-stale-events.md`); every verified caller passes `0` (2b's wire model).
   The spec is the auto-id one, marked.
3. **A negative start revision is out of scope** (`0 ≤ startRev`): the code sends a compaction
   response at revision `-1` or replays from `0` (`nonissues/etcd-mvcc-watch-negative-start-rev.md`);
   v3rpc refuses it first.
4. **Reader tokens or thread tokens for the stream's calls.** 3e's store uses counted reader tokens
   (`mvccReaders`, the user's 2026-11-06/07 decision for mvcc); 2b assumed thread tokens. 3f follows
   3e (one token per reading call, given back): 2b's run needs reader tokens of the member's store,
   which the server's `srvWatchable` slot (2c/2d) must hand out. If the bounds plan's thread tokens are
   to replace mvcc's reader tokens, that is 3e's decision first.
5. **3e's names are tracked by copy.** `New.spec`/`newWatchableStore.spec` copy `NewStore.spec`'s
   statement (3e's, changing as this was written); `req/` asks 3e to factor it or to signal changes.
6. The adt internals (above).

## `req/` sections written

* `notes/specs-only/req/go_etcd_io_etcd_server_v3_storage_mvcc.md`, **`## from 3f`** (to 3e): two
  reader slots parked for the loops and back in `mvccClosed`; `mvccReaders` covering the watchable
  store's `s.mu`; `Changes`' records owned (a delete's `ModRevision` written by `End`, then shared
  read-only); `mvccLb`'s realization beside `mvccState` (no statement change); the storage image's
  whole revisions above the compaction (for `rangeEvents`); `NewStore.spec` copied into `New`;
  `ReportEventReceived` is 3e's. And **`## from 3f, to 2b`**: the answer to 2b's request (what
  `ApiWatch.lean` gives, three departures: reader tokens, the compaction condition, id `0`).

Not written (callers' concerns, for the coordinator to relay): 2d's `srvWatchable` realization needs
`watchableAt w γm`, reader tokens for the handlers, and the bridge from `mvccLb γm h` to the
cluster's `etcdLb` (the member's notified history is a view of the cluster's at a reached point:
the apply thread fires `End`'s first update for an entry raft committed); otel's
`trace.SpanFromContext`/`span.End` (in `watchStream.Watch`/`Cancel`) on any `ctxOk` context is 4b's
boundary; 2a's `checkIntervals` and 3d's permission cache use `Adt`'s vocabulary as it stands.

## Proof-sketch notes the reviewers should check

* `wsRespOk`'s positions (`posOf`) advance only by a watcher's own responses and by stream-wide
  progress after its stamp; a stream-wide progress is sent only when every watcher of the stream's map
  is synced (`progressIfSync`), and `ws.mu` keeps the map equal to the registered, not removed
  watchers (`Watch` registers and `RequestProgressAll` reads under it; `Cancel` removes from the store
  under `s.mu` first, after which a `RequestProgressAll` finds the watcher unsynced and sends nothing).
* No send on a closed stream channel: `Close` cancels every watcher before `close(ch)`;
  `cancelWatcher` waits out a victim held by `moveVictims` (its send outside `s.mu`); progress after
  `Close` finds no synced watcher.
* `Restore` keeps every fact: its update's premise (3e's: the new history extends the committed one,
  which is the notified one under `s.mu`) keeps `mvccLb` monotone.
