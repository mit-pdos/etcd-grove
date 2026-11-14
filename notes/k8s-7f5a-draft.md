# k8s 7f-5a-D: the Draft of the etcd3 watcher's serial branch (2026-11-14; hard stop S3, for etcd-grove-81)

Branch `k8s-7f5`, worktree `/shared/etcd-grove-k8s7f`. The statements are in the unlinked
`Proof/k8s_io/apiserver/pkg/storage/etcd3/Draft7f5a.lean` (namespace `k8s.Draft`). It builds with
`lake build Proof.k8s_io.apiserver.pkg.storage.etcd3.Draft7f5a`, and nothing imports it. No proofs.
The plan is `notes/k8s-7f5-scope.md` (§5, §6 row 7f-5a-D, decisions §8) and the parent
`notes/k8s-7f-scope.md` §2.1, §5.3, §9. The Go is apiserver `9c4ec15b8038`,
`pkg/storage/etcd3/{store.go:1142-1163, watcher.go, event.go}`.

**SpecPlan convergence.** `SpecPlan/` has no spec of the apiserver's storage watcher (only the
generated `PkgInit` files), so there is nothing to converge to and no ledger entry. The client spec
used (`watcher.Watch.spec` with `isRangeWatchP` and `watchStateElemP`) was converged in 7f-3a.

## 1. The ideal stream (pure)

A store watch is stated over etcd's history as a `KVState` `σ` (`σ.at r` is the store at revision
`r`), in the store's own object type, so the statement stays in the store's package. It is not
stated over the driver's `StreamOkL`: that is over the driver's `Input` and `Obj`, which the store
must not import. 7f-6 bridges the two (D1).

- **`KWEv`**: an event as the consumer sees it. It has a type (0 Added, 1 Modified, 2 Deleted,
  3 Bookmark, 4 Error, the driver's numbering), a body, a resource version, and an
  initial-events-end annotation flag.
- **`kEvOfL dec sel emp σ ev`**: the watch event of the etcd event `ev`, as `parseEvent` then
  `transform` compute it.
  - A delete gives Deleted, with the key's previous object at the delete's revision, if that object
    passes the predicate.
  - A create (`CreateRevision = ModRevision`) gives Added with the new object, if it passes.
  - An update gives Modified when the predicate is empty. Otherwise it gives Modified, Added or
    Deleted according to which of the new and previous objects pass.
  - The previous object is the key's record at the revision before (`kPrevAt`). That is what the
    client's `prevKvOk` guarantees for a non-`nil` `PrevKv`. A `nil` one makes `parseEvent` fail,
    so the watcher sends an Error event and stops (Q5).
  - The result is none when the event is filtered out, or when a value does not decode, which
    `kvWfHist` excludes under the prefix.
- **`kInitialL dec sel inS s`**: a watch-list's initial events at the store `s`. That is one Added
  event per key in scope whose object passes, in key order, at its mod revision (`syncPaginated`,
  `parseKV`, `transform`).
- **`KTail … σ inS c es`**: the events of a watch from the cursor `c`. Each step is one of two
  things:
  - the watch events of the whole revisions `(c, r]`, with `r ≤ σ.rev`;
  - a progress bookmark at a revision `p ≥ c` when no etcd event in scope lies in `(c, p]`. Its
    object is the zero object `newFunc()` makes, at `p`, with no annotation.

  So no event is missing, none is repeated, and the order is kept.
- **`kModeOf sie allowBm n`**: what the request asks, with `WatchList` on.
  - Initial events: `SendInitialEvents` unset at resource version 0 (the legacy case), or set to
    true.
  - The initial-events-end bookmark: `SendInitialEvents` true and `AllowWatchBookmarks`.
  - The requested revision.
- **`kStreamOk … m σ evs`**: the events received, with the Error events removed wherever they occur,
  are a prefix of the ideal stream. Every event has a type of at most 4.
  - With initial events: the initial events at some `r0` (at least the requested revision, and at
    least 1, and at most `σ.rev`), then the annotated bookmark at `r0` if it was asked for, then a
    `KTail` from `r0`.
  - Without initial events: a `KTail` from some `s0`, which equals the requested revision when that
    is positive.

  This is `StreamOkL`'s shape, with two differences. It also covers the legacy case and a watch-list
  without bookmarks. Its bookmark condition is stronger: no etcd event in scope at all, not just no
  event that passes the predicate.

```lean
def kStreamOk (dec : Dec Obj) (sel : Obj → Bool) (emp : Bool) (z : Obj) (inS : GoString → Bool)
    (m : KWatchMode) (σ : KVState) (evs : List (KWEv Obj)) : Prop :=
  (∀ e ∈ evs, e.t ≤ 4) ∧
  if m.forceInit then
    ∃ r0 full, max m.req 1 ≤ r0 ∧ r0 ≤ σ.rev ∧ KTail dec sel emp z σ inS r0 full ∧
      kNonErr evs <+: kInitialL dec sel inS (σ.at r0) ++
        ((if m.bmReq then [⟨3, z, r0, true⟩] else []) ++ full)
  else ∃ s0 full, (0 < m.req → s0 = m.req) ∧ KTail dec sel emp z σ inS s0 full ∧
      kNonErr evs <+: full
```

## 2. The consumer's view: `k8sWatch`

`k8sWatch c W wi γ sel emp inS m Q` says three things:
- `wi`'s `ResultChan()` returns a channel `ch`, and `Stop()` returns. Both are persistent triples,
  callable at any time and from anywhere.
- `ch` is an SPSC channel (`isSpsc`), and the caller holds its consumer half with nothing received
  yet (`spscConsumer γ.res []`).
- The `i`-th element (`kResElem`) is a `watch.Event` `v` that is the event `e` (`wevAt`). The models
  of the first `i + 1` events are `evs ++ [e]`: each sits at its index of a ghost mono list `γ.evs`,
  so the consumer knows they are the events it received. They satisfy `kStreamOk` at a state `σ`
  at which the caller's read update fired (`□ Q lb σ`).

`wevAt S W v e` describes one event:
- An Error event has type `"ERROR"` and a `*metav1.Status` object with status `"Failure"`
  (`statusFailureAt`). That is what the driver's `WError` needs, since a foreign object is `WBad`.
- Any other event has the type string of `e.t`. The consumer gets its object owned:
  `S.objAt v.Object (annotated body if e.ann) (S.fmtRV e.rv)`.

The channel's closing carries nothing (`R := True`). Within one watch the client's resumption is
invisible: the client spec already rules out gaps and duplicates.

## 3. `store.Watch.spec` (`Draft.store.Watch.spec`)

In words: a watch of the prepared key's scope from the parsed resource version `n` returns either
an error, or `nil` and `k8sWatch` for the request's scope (`kScopeOf`: `kInScope` of the prepared
key, recursive or not) and mode (`kModeOf`). The premises:

- `isStore sp c` and **`storeWatchOk sp c W γk`**. The latter is the store invariant's growth,
  produced by `New` (a stronger post):
  - the `watcher` field's fields are the store's;
  - `newFunc` makes the zero object;
  - `getCurrentStorageRV` calls `GetCurrentResourceVersion`, and `getResourceSizeEstimator` calls
    the store's, which answers `nil`;
  - the client's watcher is over the cluster's KV `γk` (`clientWatchOk`);
  - the watch path's object contract holds (`watchContractOk`): `runtime.Decode` without a target,
    and `AnnotateInitialEventsEndBookmark`. Both are proved for the driver's codec, not trusted.
- The request:
  - the key prepares and is short;
  - the resource version parses, below `2^63`;
  - `ProgressNotify` and `RecordTimestamps` are false (D6);
  - `SendInitialEvents` is read-only (`sendInitIs`);
  - the predicate is `selPredOk` (7e's).
- The gates:
  - `watchListOn` (T5-c, landed);
  - `rangeStreamOff` (7e);
  - **`concurrentDecodeOff`**, the temporary named premise of Q6, removed by 7f-5b.
- The context: `context.isContext ci cd ∗ metadata.outgoingCtxOkC ci ∗ ctxErrClient ci cd ∗
  k8sctx.k8sCtxOk ci`. The driver's `WithTimeout(Background())` has all four. `isContext` rather
  than `watchCtx`: see D2 and T5-e.
- Three `threadTok`s, for `run`, `startWatching` and `serialProcessEvents`, kept for the watch's
  lifetime, with `threadBound GF ≤ 2^30 - 1` as in `GetList`.
- **The read updates** `Q lb σ` (D3): "a state of one history, at revision at least `lb`".
  - Laws: `Q lb σ` gives `lb ≤ σ.rev`, `kvWf`, `kvWfHist` and `kvKeysShort`. Any two firings are of
    one history (`kvSameHist`).
  - Supply: `Q 0` at every member and at `γk` (`readAus`). After a firing at `σ`, `Q σ.rev` is
    supplied (re-armed), so that a later read sees a later state. That is how `r0 ≥ n` follows:
    `getCurrentStorageRV`'s state, then `sync`'s first page.
  - This generalizes `GetList`'s `Q`/`P` pair.

The Lean statement:

```lean
abbrev store.Watch.spec : Prop :=
  ∀ [cache.v3.Assumptions] [v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] [Pos.Countable Obj] (sp : Loc) (c : StoreCfg GF Obj)
    (W : WatchSpec Obj) (γk : KVNames) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key : GoString) (opts : storage.ListOptions) (k : GoString) (n : w64)
    (sie : Option Bool) (sel : Obj → Bool) (emp : Bool) (Q : Nat → KVState → IProp GF),
  (∀ lb σ, Q lb σ ⊢ ⌜lb ≤ σ.rev ∧ kvWf c σ ∧ kvWfHist c σ ∧ kvKeysShort σ⌝) →
  (∀ lb lb' σ σ', Q lb σ ∗ Q lb' σ' ⊢ ⌜kvSameHist σ σ'⌝) →
  (∀ x ∈ c.ms, noRefusalAt x.addr) →
  {{ isPkgInit etcd3 ∗ isStore sp c ∗ storeWatchOk sp c W γk ∗
      ⌜prepareKeyM c.resourcePrefix key opts.Recursive' = some k ∧
        (c.pathPrefix ++ k).length ≤ opKeyMax ∧ c.S.parseRV opts.ResourceVersion' = some n ∧
        uint.Z n < 2 ^ 63 ∧ opts.ProgressNotify' = false ∧ opts.RecordTimestamps' = false⌝ ∗
      sendInitIs opts.SendInitialEvents' sie ∗ selPredOk c.S opts.Predicate' sel emp ∗
      watchListOn ∗ rangeStreamOff ∗ concurrentDecodeOff ∗
      context.isContext ci cd ∗ metadata.outgoingCtxOkC ci ∗ ctxErrClient ci cd ∗ k8sctx.k8sCtxOk ci ∗
      threadTok ∗ threadTok ∗ threadTok ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗
      (|==> readAus c γk (Q 0)) ∗ (□ ∀ lb σ, □ Q lb σ -∗ |==> readAus c γk (Q σ.rev)) }}
    sp.Watch(ci, key, opts)
  {{ (wi err : GoInterface), RET (wi, err);
      ⌜err ≠ nil⌝ ∨ (⌜err = nil⌝ ∗ ∃ γ, k8sWatch c W wi γ sel emp (kScopeOf c k opts.Recursive')
        (kModeOf sie opts.Predicate'.AllowWatchBookmarks' n) Q) }}
```

Errors are not identified: the driver records any `Watch` error as `WFailed`. **Many concurrent
watches** on one client watcher are allowed, since `clientWatchOk` is persistent and the client's
`watcher.Watch.spec` consumes nothing exclusive. That settles the risk in Scope §5.

## 4. The protocol (internal, in the Draft file's §4)

- **`incomingEventChan`** is an SPSC channel. Its producer is `startWatching` and its consumer is
  `serialProcessEvents`. Its `i`-th element (`kInElem`) is an `*event` holding a raw event
  (`eventAt`; `KRaw`: an initial key-value, an etcd event with its previous value's slice, or a
  bookmark with its annotation flag). The raw events queued so far are `raws ++ [r]` (a mono list
  `γ.raws`) and satisfy `kRawStreamOk` at a fired state. `kRawStreamOk` has `kStreamOk`'s shape
  before `transform`: the scope's key-values at `r0`, the bookmark, then a `KRawTail` of whole
  revisions' etcd events and progress bookmarks.
- **`resultChan`** has two producers: `sendEvent`, in order, from the processing goroutine, and
  `sendError`, an Error event from either goroutine. **`kResInv`** is an invariant that holds:
  - the SPSC's producer token;
  - the authority of `γ.evs` (the sent events' models);
  - the processing goroutine's count of raw events taken (`procd`, half);
  - the equation `kNonErr evs = raws.filterMap (kRawToEv …)`.

  A send commits through `spsc_send_au` inside the invariant. `run` closes the channel after
  `resultChanWG.Wait()` (both producers have exited), taking the token from the invariant.
- **The key pure lemma**: `kRawStreamOk σ raws → kStreamOk σ (raws.filterMap (kRawToEv σ))`, with
  Error events interleaved freely and prefixes closed, together with transport along `kvSameHist`
  to a later state. The serial goroutine sends exactly the non-`none` transforms in order, and it
  stops at its first error.

## 5. Trusted texts

| Item | Status | Text | Go evidence |
| --- | --- | --- | --- |
| **T5-e**: `WithRequireLeader.wp_proof` gains `isContext ctx s -∗ isContext c s` | **NEW, for 81's axiom review** (D2) | One more conjunct in the post: over a parent with Perennial's context model, the result has it too, with the same descriptor. Go: `c` is a `*valueCtx` at grpc's key. Its `Deadline`, `Done`, `Err` are promoted from the parent, `Value(&cancelCtxKey)` walks to the parent's, and `parentCancelCtx(c)` reads exactly those two, so it finds the parent's `*cancelCtx`. `c`'s type is not `stopCtx`. `HDoneFresh` is ghost state of the same descriptor. The repository's `WithValue.spec` already claims this for five key types; this is grpc's sixth. | `examples/premisefix/watcherctx/draft7f5a_test.go`: `TestWithRequireLeaderIsContext` (5 parent shapes × 200: `Deadline`, the same `Done` channel, `Err` and `Cause` the parent's, `Err` a context error, **`WithCancel(c)`'s child cancelled synchronously**, i.e. `parentCancelCtx(c)` succeeded); `TestIsContextCheckDetects` (a wrapper with its own `Done` fails the synchronous check, 200/200). Older: `TestWithRequireLeaderOtherKeys`, `…CancelPropagates`. All pass (GOWORK=off, go1.27.3, 32G cap). |
| **T5-f**: leaf no-op specs the watcher reaches | **NEW texts, Lean in 7f-5a-P; for 81's axiom review** | `metrics.RecordEtcdEvent(gr)`, `RecordEtcdBookmark(gr)`: return, given `utf8Valid` of `gr`'s group and resource (as `RecordEtcdRequest`'s; the store has it in `storeListOk`). `mvccpb.Event_EventType.String(t)`: returns some string, for any `t` (reached on `parseEvent`'s nil-`PrevKv` path, Q5). `klog.Warningf(fmt, err)`: returns (`logWatchChannelErr`'s compaction branch; `Errorf`'s spec exists). | same file: `TestRecordEtcdEventBookmarkLabels` (valid labels return; invalid UTF-8 panics once registered, so the premise is needed), `TestEventTypeStringReturns` (0, 1, 2, 7, -1), `TestKlogWarningfReturns`. |
| T5-d: `wait.Jitter(d, f)` returns some duration | reviewed in S1; Lean in 7f-5a-P | `notes/k8s-7f5-freeze.md` T5-d | `TestJitter` |
| T5-b, T5-c, T5-a | landed | - | - |

Not trusted: `watchContractOk` (a premise the driver's codec proves), `storeWatchOk` (`New` proves
it), `statusFailureAt` (proved of every error path), `concurrentDecodeOff` (a gate fact from the
landed table, whose producer is the driver's `Set`).

Expected to need **no** new text, though 7f-5a-P checks each one and stops if a spec is missing:
- `isCancelError`'s type assertions and the `Code()` and `GRPCStatus()` methods on the client's
  error types (`clientErrTys`, 7e-1);
- `interpretWatchError` (`errors.As` over the client's errors, `NewResourceExpired`),
  `apierrors.NewInternalError`, `APIStatus.Status`, `storage.NewTooLargeResourceVersionError`
  (translations);
- `fmt.Errorf` (`%q`/`%d`/`%s`/`%w`), `strings.Contains`;
- `time.Now`/`Since`, `clock.RealClock`, and `newBlockLogger`/`recordWait` (translated, over
  `sync.Mutex`);
- `runtime.Decode`'s translation (it calls the codec, hence `watchContractOk`);
- `utilflowcontrol.WatchInitialized` (T5-b, translated).

## 6. Proof plan (7f-5a-P) and estimate

Order, with the internal specs (watcher.go's functions; one Spec/Proof file each):

1. **Configuration** (Goose): drop the G1 exclusions (`parseEvent`, `startWatching`); add
   `runtime.Decode`, `wait.Jitter`. The T5-d/T5-f axioms are written in Lean then. ~0 Lean lines.
2. **Pure** (`WatchDefs.lean`, ~600-900 lines):
   - `kRawToEv` filtered equals `kStreamOk` (raw to cooked);
   - prefix closure and transport along `kvSameHist`;
   - `inRange (pfx) (prefixEnd pfx) ↔ kInScope` (the client watch's range is the scope);
   - a client response (`watchStateRespOkP`) gives a `KRawTail` chunk, and its `PrevKv` gives
     `kPrevAt`;
   - the initial events from `syncPaginated`'s pages at one revision.
3. **Leaves** (~700-1000), each with its spec:
   - `parseKV`, `parseEvent`, `progressNotifyEvent`;
   - `decodeObj`, `prepareObjs`, `transformIfCorruptObjectError`, `filter`, `acceptAll`,
     `transform`;
   - `isCancelError`, `logWatchChannelErr`, `interpretWatchError`, `transformErrorToEvent` (its
     result `statusFailureAt`);
   - `newBlockLogger`, `blockLogger.recordWait`;
   - `getStartWatchResourceVersion`, `isInitialEventsEndBookmarkRequired`,
     `areInitialEventsRequired`;
   - `flowcontrol.WatchInitialized`/`initializationSignalFrom`;
   - `watchContext`.
   - Checkpoint.
4. **Channel operations** (~400-600): `queueEvent` (`kInElem`), `sendEvent` and `sendError` (in
   `kResInv`).
5. **Producer** (~900-1300): `sync`/`syncPaginated` (pages via the client's `Get` chain at the
   first page's revision; `EtcdRangeStream` off), `startWatching` (the client's `Watch` with
   `WithRev(r0+1)`, `WithPrevKV`, `[WithPrefix]`, and the response loop). Checkpoint.
6. **Consumer and wiring** (~600-900):
   - `serialProcessEvents`, `processEvents` (the serial branch under `concurrentDecodeOff`);
   - `run` (`resultChanWG`, close), `Stop`, `ResultChan`;
   - `createWatchChan` (`WithCancel` of the require-leader context: T5-e gives `isContext`);
   - `watcher.Watch` (T5-b's key), `store.Watch`.
7. **`New`'s stronger post** (`storeWatchOk`; the closures; ~150-300); the etcd3 `Link`/`Results`
   with `#print axioms`; STATUS lists `concurrentDecodeOff` as temporary.

**Estimate: 3350-5000 Lean lines** (the Scope said 3200-4800), in **4-6 agent contexts**.

Risks:
- **The context chain** (D2): `ctxOk`/`ctxErrClient`/`k8sCtxOk` of `WithRequireLeader(ctx)` and of
  its `WithCancel` child.
- **`statusFailureAt`** on every error path. An error that is itself an `APIStatus` with another
  status would break it; none is expected, since the constructors used all set `Failure`.
- **`prevValue` empty for an update when the predicate is not empty.** `filter(nil)` would call
  `Matches` on a `nil` object. Stored values are never empty (`encode_ne_nil`, `toS`), but the
  proof must carry that from `kvWfHist`.
- **`watchContractOk`'s `runtime.Decode`** must hold of the driver's codec without a target (7e's
  Go has it; the Lean is new in 7f-5a-P or 7f-6).

## 7. Decisions needed (each with a recommendation)

- **D1. State the spec generically (`kStreamOk` over `KVState` and the store's `Obj`), not over
  the driver's `StreamOkL` by name.** The parent Scope §5.3 said "by name". That is impossible
  without the store importing the driver. 7f-6 proves `kStreamOk → StreamOkL` under 7e's
  `hist[R] = absK (stateAt L R)`, one key per revision and the stronger bookmark condition.
  **Recommended: yes.**
- **D2. The context route: premise `isContext` of the caller's context, plus T5-e.** `getCurrentStorageRV`
  (on `WithRequireLeader(ctx)`) and `syncPaginated`'s `Get` (on its `WithCancel` child) need grpc's
  `ctxOk`, whose only fitting case is `isContext`. The restated T5-a gives only `watchCtx`-level
  transfers. The alternatives are: (b) a local `WithCancel` axiom over a `watchCtx` parent giving
  `isContext` of the child, plus another route for `ctxOk(WithRequireLeader(ctx))`, which makes
  two texts; (c) widening grpc's `ctxOk` to `watchCtx`, which re-opens grpc's reviewed contracts.
  **Recommended: (a) T5-e**: one conjunct, true in Go for the reason stated, with its test.
- **D3. The read updates `Q lb σ`, re-armed at `Q σ.rev`.** This generalizes `GetList`'s `Q`/`P`.
  7f-6's producer is the driver's history ghost with a lower bound. **Recommended: yes.**
- **D4. `[Pos.Countable Obj]`** (the models' ghost list) **and the not-trusted premises
  `watchContractOk`/`storeWatchOk`** (`WatchSpec.annotate`; `New` gets a stronger post).
  **Recommended: yes** (forms).
- **D5. Claim Error events carry a `Failure` `*metav1.Status`** (`statusFailureAt`). Without it the
  driver's `WBad` rule fails the check. **Recommended: claim it.** The risk is listed in §6.
- **D6. Premises `ProgressNotify = false` and `RecordTimestamps = false`.** The driver never sets
  them; the cacher's `ProgressNotify` is out of scope. They keep `WithProgressNotify` and
  `WithWatchBufLog` out of the client watch's options (`isRangeWatchP`). **Recommended: yes.**
- **D7. T5-f's texts reviewed now with T5-e** (their Lean lands in 7f-5a-P, unchanged).
  **Recommended: yes**, so that 7f-5a-P needs no stop for them.
