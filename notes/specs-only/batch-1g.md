# Batch 1g: etcd's cache and its B-tree (report, before review)

## Files

- `Spec/go_etcd_io/etcd/cache/v3/` (109 modules, namespace `Cache`): `Api.lean` (client-facing
  vocabulary), `Internal.lean` (the internals' vocabulary, imported by no other directory), and one
  spec per Go function: the 107 functions with an old spec (all kept). Client-facing, written with
  full care: `New`, `Cache.{Get,Watch,Close,Ready,WaitReady,WaitForRevision,WaitForNextResync,
  RequestProgress}`, `defaultConfig`, the ten `With*` options, `ExactKey`, `FromKey`, `Range`,
  `KeyPredForRange`, `Prefix.Match`. Internal (specs mirror the code, short comments): the ring
  buffer (14, ported from the old specs), store and snapshots (11), demux (19), watcher (4), ready
  (7), notifier (3), progress requestor (4), clock/timer (4), the `Cache`'s unexported methods (11),
  `newCache`, `kvItemLess`, `newKVItem`, `probeItemFromKey`, `isPrefixScan`.
- `Spec/k8s_io/utils/third_party/forked/golang/btree/` (52 modules, namespace `BTree`): `Api.lean`,
  `Internal.lean` (nodes), and the 50 functions with an old spec (ported mechanically onto the new
  opaque vocabulary; the public ones' pure premises moved into the precondition).
- Snippets: `examples/specreq/cache/{get,watch,lifecycle}.go`, `examples/specreq/btree/btree.go`
  (`go vet` clean).
- Everything builds: `etc/specs-build.sh --dir` on both directories (after W0's round-1 repairs).

## Exported vocabulary

**`Cache` (`Api.lean`)**, over W0's model (`KVHist`, `etcdLb`):
- pure: `RevEvent`, `evsBetween h rng a b` (the history's events of revisions `a..b` in a range),
  `WatchRespM`, `WatchSt` (`live pos | rejected | closed`), `deliv` (an events response against the
  history), `quiet` (a progress notification), `getUnsupported`, `watchUnsupported`, `cacheRange`,
  `rangeOk` (the cache's validation), `watchStart`, `getRespM`, `defaultConfigM`, `cfgApply`,
  `CfgValid`, `CfgBounded`.
- `isCache c γ who pfx` (persistent): the cache handle.
- `cacheOpen c q` (fractional): `Watch` takes a fraction, `Close` the whole (both give it back).
- `cacheRevLb c r` (persistent): the cache's latest revision has been `≥ r`.
- `cacheWatchAt ch γ rng st` (exclusive): a cache watch's consumer.
- transparent: `etcdPeek γ` (1f's body), `eventOwn`, `eventsAt`, `watchRespAt`, `getOk`, `getErr`,
  `keyPredAt`, `cfgOptAt`, `cfgOptsAt`.
- laws: `isCache_persistent`, `cacheRevLb_{persistent,zero,mono,reached}`, `cacheOpen_fractional`,
  `cacheWatchAt_recv` (the receive law: events = `evsBetween` from the position, progress quiet,
  a cancel, or closed), `init` (the error variables).

**`BTree` (`Api.lean`)**: pure `StrictOrder`, `Sorted`, `mLookup`, `mInsert`, `mDelete`, `ascRange`,
`descRange`, `Target`, `removeOp`; `ItemOrder` (`lt`, the persistent `item v k`), `orderedOrder`;
`ownBTree o t dq s` (fractional, persistent at `discard`), `isFreeList`; transparent `isLess`,
`iterProtocol`, `iterDone`, `allItems`; laws `ownBTree_{sorted,items,fractional,agree,persist,
discard_persistent}`, `isFreeList_persistent`.

## The client-facing statements, in short

- `Get`: the answer is `Store.rangeKVs (σ.kv.storeAt tgt) (cacheRange key o)` for the revision
  asked for (`tgt = L`, the header's, for `0`), `L ≤ σ.kv.rev` for an `etcdLb γ σ`; linearizable:
  `σ0.kv.rev ≤ L` for the caller's anchor `etcdLb γ σ0`; always `r0 ≤ L` for `cacheRevLb c r0`;
  errors: `ErrKeyRangeInvalid` (or the context) for a served request outside the prefix, else
  `err ≠ nil`.
- `Watch`: the consumer at `watchStart` (or closed); each response a persistent fact
  `etcdLb γ σ ∗ ⌜deliv/quiet σ.kv …⌝`.

## Main changes from the old specs

- Stated over W0's model instead of the old `EtcdModel` class and `isEtcdClient` trust boundary:
  `New` takes `isClient` (W0) and the read permission `etcdPeek γ`.
- The delivery theorem (`cache_Watch_delivery`, a log-level `cacheWatchLog` with `certChain`s)
  became a per-receive law over a position (`cacheWatchAt_recv`); it composes with every other reply
  through the history.
- `Get`'s reader token (`cacheReader`) dropped; freshness anchors are client-facing (`etcdLb γ σ0`,
  `cacheRevLb c r0`).
- Relaxed: the prefix-length bound (`≤ 2^28`, a grpc scope restriction of the old proof) and the
  thread bound (`ThreadBoundLe`) on `New`; `Close` gives its token back (a `Watch` after `Close`
  returned is fine in Go).
- Not relaxed (the code needs them): `CfgBounded` at `New` (a negative `PerWatcherBufferSize`
  panics in `make(chan)`, a huge degree overflows the B-tree's `maxItems`, a huge window the ring's
  arithmetic; `< 2^32` for the buffer is Perennial's channel model, kept at the one producer);
  the B-tree's degree `∈ [2, 2^62]`.
- The stale-progress bug (`issues/cache-stale-progress-compacts-newest-watch.md`, "blocks-proof:
  yes" before) no longer blocks: the position-based statement admits its effect (a spurious
  compaction cancel), and 1b's `watchStep` already keeps progress notifications at or above the
  position.

## Functions left out

- btree's `initialize` (package init: covered by the generated `Spec/PkgInit` and the cache's `init`
  law). No other.

## Findings in the Go code (filed in round 1: `nonissues/etcd-cache-get-keys-only-ignored.md`,
`nonissues/etcd-cache-waittillrevision-goroutine-outlives-close.md`)

- `Cache.Get` ignores `WithKeysOnly` (`validateGet` neither rejects nor honours it): a keys-only Get
  returns values, unlike the client's `Get` (documentation/behaviour mismatch; `nonissues/`
  candidate, blocks-proof: no; the spec states the full key-values).
- `Cache.waitTillRevision` leaves a goroutine per waiting `Get` running up to `WaitTimeout` (not in
  the wait group): `Close` returns while they run. Liveness/resource only; blocks-proof: no.
- Known: `nonissues/etcd-cache-watch-during-close-waitgroup.md` (the `cacheOpen` token),
  `issues/cache-ready-after-retry.md` (liveness, not stated).

## Decisions and open questions for the user

1. **The cache's watch vocabulary vs 1b's** (`watchChAt`, `watchStep`, `ClientV3.WatchRespM`,
   `eventOwn` landed after mine): the cache's `Watch` returns a `clientv3.WatchChan` with its own
   consumer predicate `cacheWatchAt` and its own `Cache.WatchRespM`/`eventOwn`. Unifying (the cache's
   channel meeting 1b's `watchChAt` at 1b's `WatchPos`) would make the cache a drop-in `Watcher`
   for clients (Kubernetes' pattern), at the cost of restating `cacheWatchAt_recv` in 1b's terms
   (the cache never sends `Created`; its cancel is a compaction of *its* window, not the cluster's,
   so 1b's `cr ≤ σ.kv.compacted` would be false: a cache cancel needs its own arm). Recommended:
   integrate, with a cache-specific cancel arm. Integration step, not done here.
2. **Linearizable freshness as an anchor** (`etcdLb γ σ0` in `Get`'s pre) rather than the caller's
   atomic update: the same choice as 1f's waiting calls; a caller anchors at the call by taking
   `etcdLb` from its invariant just before. Equivalent for reads; please confirm.
3. **`New` takes `etcdPeek γ`** (the program's read permission over the cluster's state): new
   premise on a client-facing spec, needed because the cache's background list is a client `Get`
   that needs an update. Any owner of `etcdState` can give it.
4. **Errors of `Get`** (round 1b, the coordinator: a completeness requirement, not a decision):
   `ErrUnsupportedRequest`, `ErrKeyRangeInvalid` and `ErrFutureRev` are stated (`getErr`). The
   `ErrFutureRev` clause: for a served request, `err = errVal .futureRev` unless the context is done,
   the revision was reached by the cluster, or the request is linearizable (the client's `Get` and
   the timeout may fail first): the serializable cases of `testGet` follow exactly, the
   linearizable ones only when the client's own `Get` succeeds (margin). Snippet `ReqGetFutureRev`.
5. `isCache` carries the client's principal `who` (W0's round 1: `Get` passes the caller's context
   to the client's `Get`, which needs `ctxPrin ctx who`).

## `req/` sections written

- `req/go_etcd_io_etcd_client_v3.md`, `## from 1g`: the watch's facts (covered by 1b as written),
  read-only events (`eventOwn` persist law), `IsProgressNotify`'s spec, `RequestProgress`, the
  vocabulary question.
- `req/go_etcd_io_etcd_api_v3.md`, `## from 1g`: `etcdPeek` in `State.lean` (shared with 1f).

## Margins (where posts are weaker than the code)

Header fields besides the revision, `Count`/`More` stated; `CompactRevision`/`CancelReason` of a
cancel; that `Close` stops every watch; readiness's liveness; `WaitForNextResync`'s meaning;
internal specs of the demux's locked helpers keep only the lock invariant's phase.

## Round 1 repairs (2026-11-09)

Reviews: `reviews/1g-completeness-1.md` (C), `reviews/1g-provability-1.md` (P). Rebuilt (161
modules) and re-vetted.

**First tier, fixed.**
- P-F1: `threadTok` in the pre and post of `Cache.Watch` (deposited at the wait group's `Add`, a
  fresh one from `wp_fork_tok`), `Cache.Get`, `Cache.WaitForRevision`, `Cache.WaitForNextResync`,
  and the internal read-lockers (`store.LatestRev`, `store.getSnapshot`, `store.Get`,
  `Cache.waitTillRevision`, `notifier.wait`, `demux.WaitForNextResync`, `demux.LatestRev`,
  `demux.BroadcastProgressTo`). The snippets' callers hold one each (stated in no snippet: they
  thread no tokens, as W0's).
- P-F2: `respFact`'s third arm only for non-progress responses (header `0`, created, canceled, or a
  compaction).
- P-F3: law `isCache_ne_null` (cited in `New`'s docstring).
- P-F4: W0's `etcdLb_keyNonEmpty` cited in `Cache.Get`'s, `Cache.Watch`'s and `Cache.get`'s sketches
  (the root cache lists and watches from `"\x00"`).
- C-F1: `getErr` states an unsupported request's `ErrUnsupportedRequest` (`wrapsErr err e`, new
  opaque, with `wrapsErr_persistent`, `wrapsErr_refl`, `errorsIs_wraps`); `ReqRangeInvalid` checks it.
- C-F2: `WatchSt.live pos seen`: a progress notification is at least the highest revision the watch
  named before (`seen ≤ m.hdrRev`); snippet `ReqProgressAfterEvents`.
- C-F3: mvcc's key index named in `btree/Api.lean` and the Users of `New`, `Get`, `ReplaceOrInsert`,
  `Delete`, `Clone`, `Ascend`, `AscendGreaterOrEqual`, `Len`; snippets `btree/mvcc.go`
  (`ReqMutateInPlace`, `ReqFractionalReaders`, `ReqStopEarly`, `ReqCompactClone`).

**Coordinator's items.** W0's `etcdPeek` (`State.lean`) used, the cache's copy dropped; the two Go
findings filed as `nonissues/` (and P-S1's re-watch as
`nonissues/etcd-cache-rewatch-from-original-revision.md`); index regenerated.

**Second tier.**
- Done: P-S2 (`store.Get`/`getSnapshot` take `storeRevLb s r0` and return `r0 ≤ lrev`; internal
  `cacheStoreAt` and `cacheRevLb_store` link the cache's and the store's lower bounds), P-S4 (the
  tree's entries are (key, key-value pointer), via `kvItemAt`), P-S5 (the cancel arm's docstring: at
  any time), C-F5 (`watchRespAt` states `closeErr = nil`).
- Not done: P-S1's sketch (`Broadcast`'s fact taken at the demux's position: a replayed upstream
  response needs a conversion, or an error arm; the code rejects it, `validateRevisions`); P-S3
  (receive laws for `watcherConsumer`/`storeApplier`, a `cacheWatchAt_recvAu` for `select`);
  C-F4 (a floor for a watch "from now"); C-F6's snippets (multi-key revisions, header equality, a
  future revision); C-F7/P (the drop-in watch vocabulary,
  open question 1).
