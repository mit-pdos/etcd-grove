# k8s 7f-5, the etcd3 watcher: Scope (2026-11-13, branch `k8s-7f5`; to etcd-grove-81)

Notes only. No Lean is edited and nothing lands until 81 approves. The parent plan is
`notes/k8s-7f-scope.md` (revision 2, approved), §9's rows 7f-5a and 7f-5b. That Scope's §2 (the
watcher's structure), §4 (watches as porcupine operations) and §5.3 (the store's watch) still hold.
This file records what changed since then (7f-4 landed; what it taught), the dependency check, and
the plan for 7f-5.

## 1. The goal, in plain words

7f-5 proves that **the Kubernetes API server's etcd3 watcher delivers a correct watch stream**. A
watch opened through `store.Watch` returns a channel. Whatever the consumer has received from it
so far, with the Error events removed, is a prefix of the ideal stream:
- for a watch-list, the matching objects at some revision `r0` (at least the requested one), then
  the end-of-initial-events bookmark;
- then every change in scope after that revision, in order, none missing, none duplicated;
- with progress bookmarks only where no change in scope is skipped.

Error events may come anywhere (the watcher's own race,
`nonissues/k8s-etcd3-watcher-events-after-error.md`), and the channel closes after `Stop` or the end
of the context. This is the `ResultChan` contract of `notes/k8s-7f-scope.md` §2.1. It is stated over
etcd's real history, which `KWatchStream.lean`'s `StreamOkL` (7f-2, landed) already reads.

**Closed theorems.** 7f-5 changes no closed theorem's statement. Its results are:
- `store.Watch.spec`, a linked, exported result (the etcd3 `Link`/`Results`, with
  `#print axioms`);
- with 7f-3, which 7f-5a needs (§2), the client's `watcher.Watch.spec` generalized to `WithPrevKV`.
  That generalization is a strengthening, and every current user keeps its instance (`prevKV`
  false).

7f-6 then uses `store.Watch.spec` to extend the three closed theorems `k8s_etcd3_safe`,
`k8s_etcd3_cluster_safe` and `k8s_etcd3_partition_safe` with watchers: the driver checks the watch
traffic of Kubernetes' `TestCorrectness` (16 watchers, with slow, hiccup and stalled consumers)
against each configuration's history. 7f-5 is the part of that coverage which is about etcd as
Kubernetes uses it:
- `WithPrevKV` and `WithRequireLeader` on every watch;
- the server cancelling a require-leader stream when its member has no leader;
- the client resuming on another member after a cut;
- the paginated initial list.

**Strength (the user's goal).** Every trusted text 7f-5 adds must constrain each `ctx.Value` key,
and each method of a value read from the context, that the modelled Go code reaches (§4.1). Each
text comes with a Go test under `examples/premisefix/` and goes through an axiom review before any
proof relies on it (§6, hard stop S1). Every premise of `store.Watch.spec` must have a producer in
the driver (§5).

## 2. Dependency check (2026-11-13, lean `222c3fcff7`)

| Dependency | State | Evidence |
| --- | --- | --- |
| **7f-3** (`WithPrevKV` through the watch stack; the `WithRequireLeader` triple F2) | **missing**, not started | No commit or STATUS/status-history/decisions entry names it (`git log lean \| grep -i '7f-3\|prevkv'`: only unrelated txn/auth commits and two issue files). In Lean, the client still pins `prevKV = false`: `OpFull.isRangeWatch` (`Proof/go_etcd_io/etcd/cache/v3/InvEtcdTxn.lean:1231-1233`) and `wrRO`'s `prevKV ↦□ false` (`Proof/go_etcd_io/etcd/client/v3/InvWatch.lean:846,859`). The server keeps its `prevKV` map empty (`swsMu`, `Proof/.../api/v3rpc/InvWatch.lean:260,466`). F2: 7f-4's freeze defers T-d (F2) to 7f-3 (`notes/k8s-7f4-freeze.md:54`). The only `WithRequireLeader` spec is still `Background()`'s (`Spec/go_etcd_io/etcd/client/v3/WithRequireLeader.lean`). |
| **7c-3** (`Client.Get` at a revision; the client error's identity) | **landed**, folded into 7e-1 | `notes/k8s-7e-1-draft.md:5` ("It includes what was 7c-3"), §2 there. Landed with the 7e Freeze (lean `8809f94d74`, an ancestor of `lean`). `Calls.lean:62-73` (`clientErrPlain_holds`, no longer a premise); `notes/k8s-7e-freeze.md` §1: the pending `Hpl`/`HGetAt`/`HList` are gone. |
| **7e-1** (`Client.List`, the range with a limit, read errors' identity) | **landed** | The same Freeze (`notes/k8s-7e-freeze.md:1`, "7e-1 with 7e-4, 7e-2, 7e-3b"); status-history 2026-11-10, "k8s 7e, the Freeze package". The client chain `kv.Get.specM`/`client_range_any` with `WithRange`/`WithLimit`/`WithRev` is what `syncPaginated` calls, on `clientv3.KV` directly. |
| **Sweep repairs B5** (the feature-gate interface) | **landed, half**: `featureOff` only | `Proof/k8s_io/apiserver/pkg/util/feature/Gate.lean`: `featureGateOk`'s `Set` triple covers only `Set(s ++ "=false")`. `WatchList` and `ConcurrentWatchObjectDecode` are already in `k8sQueriedFeatures` (`:47-49`). The file header's environment assumption *excludes* `Set` with `true` (`:17-21`). So the `featureOn` half that 7f-5a needs is a restatement of landed trusted text (§4, T5-c). |
| 7f-4 (require-leader streams, the weak handler context) | **landed** | lean `edd43a9b44` (step 5), step 6 in `222c3fcff7`'s history: `runsNoRequireLeader` deleted (STATUS, first entry). |
| 7f-2 (the pure watch check, `watchOkL_of_stream`) | **landed** | status-history 2026-11-12; `examples/k8s/etcd3/KWatch.lean`, `KWatchStream.lean`. |
| 7f-1 (`lintest.RunLin2`) | **landed** | status-history 2026-11-08. |
| 7f-0 (the driver's watch traffic in Go) | **partial** | `Input`'s watch fields, `Output.WEvents`/`WFailed` and the codec's decode without a target and `Obj.Annotated` are in `examples/k8s/etcd3/k8setcd3.go` (`:496-551`, `:83`, `:226`). `watch.go` (`genWatch`, `runWatch`, `watchOk` in Go), the `KWatch` step, `Gen`/`Apply`/`Check` through `RunLin2` and `Main*` with watchers are **not**. That is 7f-6's input, not 7f-5's. |
| 7e's object layer and codec contract (decode without a target, `Obj.Annotated`) | **landed** | In 7e (`90b6252aa5` folded in), above. |
| Per-type landing; grpc serve pool stage B (the thread bound) | **landed** | STATUS "Soundness bugs: `grpc.serve`'s handler pool ...": stage A `de9c19e020`, stage B `51e51adb99`. |

**Consequence.** 7f-5a cannot be linked until 7f-3 is done. 7f-3 is 2000-3500 lines by the parent
Scope, and includes the re-proof of `watchGRPCStream.run` (3368 lines), the slowest proof in the
repository. §6 makes 7f-3 the first Lean stage of this plan (Q1).

## 3. The Go code involved

The pins: Kubernetes apiserver `9c4ec15b8038` (`examples/k8s/etcd3/go.mod:28`, project `k8s-apiserver` of
`etc/goose.py`; source in the module cache, `k8s.io/apiserver@v0.0.0-20261021221356-9c4ec15b8038`),
apimachinery `0b7d352f711c`, and the etcd fork `0b50f0426` (`etc/goose.py:288`; the examples'
`go.mod` replaces etcd by it).

**apiserver `pkg/storage/etcd3`:**
- `store.go:1142-1152` `store.Watch`: `prepareKey`, `ParseResourceVersion`, then
  `watcher.Watch(watchContext(ctx), ...)`;
- `store.go:1154-1163` `watchContext` = `clientv3.WithRequireLeader(ctx)`;
- `store.go:239-242`: the watcher's `getResourceSizeEstimator` and `getCurrentStorageRV` closures,
  set by `New`;
- `store.go:279-283`: `getResourceSizeEstimator` (an `RLock` of `collectorMux`).

**`watcher.go`:**
- `:139-161` `watcher.Watch` (`go wc.run(...)`; `utilflowcontrol.WatchInitialized(ctx)` at `:158`);
- `:163-186` `createWatchChan` (`WithCancel(ctx)` at `:180`; two `newBlockLogger`s);
- `:193-243`: `getStartWatchResourceVersion`, `isInitialEventsEndBookmarkRequired`,
  `areInitialEventsRequired` (three `Enabled(WatchList)` calls);
- `:253-267` `isCancelError` (type assertions to `etcdError`/`grpcError`, with their `Code()` and
  `GRPCStatus()` called);
- `:269-292` `run` (`resultChanWG`, `close(resultChan)`); `:294-300` `Stop`, `ResultChan`;
- `:309-323` `sync` (the `EtcdRangeStream` gate: off, 7e's `featureOff`);
- `:325-380` `syncPaginated` (`client.KV.Get(wc.ctx, ...)` at `:347`, `WithLimit`/`WithRange`,
  then `WithRev`);
- `:428-437` `logWatchChannelErr` (`err.Error()`, `strings.Contains`);
- `:455-544` `startWatching` (`getCurrentStorageRV(wc.ctx)` at `:457`; `wait.Jitter` at `:463`;
  `client.Watch(wc.ctx, key, WithRev(initialRev+1), WithPrevKV(), [WithPrefix])` at `:493`);
- `:546-575` `processEvents`, `serialProcessEvents` (7f-5a);
- `:577-662` `concurrentProcessEvents`, `scheduleEventProcessing`, `collectEventProcessing`
  (7f-5b);
- `:664-758`: `filter`, `acceptAll`, `transform`;
- `:779-834`: `transformErrorToEvent`, `sendError`, `sendEvent`, `queueEvent`;
- `:836-873` `prepareObjs` (`transformer.TransformFromStorage(wc.ctx, ...)`);
- `:881-891` `transformIfCorruptObjectError` (`errors.As`);
- `:894-910` `decodeObj` (`runtime.Decode`; the `fatalOnDecodeError` panic branch);
- `:68-80`: the package `init` (`KUBE_PANIC_WATCH_DECODE_ERROR`).

**Other apiserver and apimachinery files:**
- `event.go:54-92`: `parseKV`, `parseEvent` (the nil-`PrevKv` error at `:67-70`),
  `progressNotifyEvent`;
- `errors.go:31-50` `interpretWatchError` (`errors.As`, `NewResourceExpired`);
- `block_logger.go:44` `newBlockLogger`, and `recordWait`;
- `pkg/util/flowcontrol/apf_context.go:42-53`: `initializationSignalFrom` and `WatchInitialized`.
  These read `ctx.Value(priorityAndFairnessInitializationSignalKey)` and call `Signal()` on what
  they find;
- `pkg/util/feature` / `pkg/features/kube_features.go`:
  - `:539-545` `WatchList`: Beta, default true since 1.34;
  - `:394-397` `ConcurrentWatchObjectDecode`: default true since 1.37;
- apimachinery `pkg/util/wait/wait.go:92` `Jitter`.

**etcd fork `0b50f0426`** (7f-3's part):
- `client/v3/ctx.go:28-38` `WithRequireLeader` (`metadata.FromOutgoingContext`, `Pairs`, `MD.Copy`,
  `Set`, `NewOutgoingContext`);
- `client/v3/op.go:542` `WithPrevKV`; `:380` `WithRev`;
- `client/v3/watch.go:1088` (`toPB`'s `PrevKv: wr.prevKV`) and `:1102` `streamKeyFromCtx`;
- `api/v3/mvccpb/extension.go:18` `(*Event).IsCreate`;
- `server/etcdserver/api/v3rpc/watch.go`:
  - `:251` `recvLoop` (`sws.prevKV[id] = true` at `:349`);
  - `:413` `sendLoop` (the `prevKV` branch at `:444-454`: `watchable.Range` at `ModRevision - 1`,
    whose `KVs[0]` becomes the event's `PrevKv`);
  - `:607` `IsCreateEvent`.
- Ownership checked: mvcc's `newWatcherBatch` (`storage/mvcc/watcher_group.go:79-98`) builds a fresh
  `*mvccpb.Event` per watcher. So the send loop's write of `PrevKv` touches no event that another
  watcher shares, and no data race arises there.

## 4. New trusted texts expected, each with its Go evidence plan

### 4.1 The context enumeration, done first (7f-4's lesson)

The refutations T-h..T-k (`notes/k8s-7f4-freeze.md`; `notes/ctx-sweep-fixes.md`) all had the same
shape: a premise left open a `ctx.Value` key, or the context's `Cause`, that the modelled Go code
reads. So before any text is written, stage S0 (§6) lists, by file:line, **every read of the
watcher's contexts**. There are two contexts:
- the caller's `ctx`;
- `wc.ctx = WithCancel(WithRequireLeader(ctx))`.

The reads, through their callees. A first pass of this Scope:

| Read | Where | Covered today by |
| --- | --- | --- |
| `Value(mdOutgoingKey{})` | `WithRequireLeader` (`ctx.go:29`); the client's `streamKeyFromCtx` and the gRPC stream's metadata | `libCtxOk` / `metadata.outgoingCtxOkC` |
| `Value(&cancelCtxKey)` (and a `*cancelCtx` it returns) | `WithCancel` in `createWatchChan` (`watcher.go:180`); the client's `WithCancel(&valCtx{ctx})` | `watchCtx`'s `#HCC` (the context sweep) |
| `Done()`, `Err()` | the selects of `run`, `queueEvent`, `sendEvent`, `sendError`, `serialProcessEvents`; the client's calls | `watchCtx`, `ctxOk`/`ctxErrClient` |
| **`Value(priorityAndFairnessInitializationSignalKey)` and then `Signal()` on the stored value** | `WatchInitialized(ctx)` (`watcher.go:158`, `apf_context.go:43,50-51`) | **nothing**: a new key (T5-b) |
| the keys of `GetCurrentResourceVersion`'s and `KV.Get`'s premises (audit, utiltrace, runtime/trace, grpc's three keys) | `getCurrentStorageRV(wc.ctx)`, `syncPaginated` | `k8sCtxOk ∗ ctxOk ∗ ctxErrClient` of the *caller's* context. Over `wc.ctx` they need preservation through `WithRequireLeader` and `WithCancel` (T5-a; Perennial's `WithCancel` keeps `Values`) |
| `TransformFromStorage(wc.ctx, ...)` | `prepareObjs` (`watcher.go:843,858`) | `transformerOk` takes any context. The driver's identity transformer reads none; a KMS transformer is out of scope, as in 7e |
| `context.Cause` | none found on the watcher's path in the first pass; S0 confirms it, including the client's watch | - |
| methods of error values: `Code()`, `GRPCStatus()`, `Error()`, `errors.As` targets | `isCancelError`, `logWatchChannelErr`, `interpretWatchError`, `transformIfCorruptObjectError` | `clientErr`'s four types (`clientErrTys`, 7e-1), `S.trErr`, `fmt.Errorf`'s `errStrOk`; S0 checks that each method called has a spec on every type that can reach it |

### 4.2 The texts

Each text below is TRUSTED unless marked. Each gets a test in a new
`examples/premisefix/watcherctx/` (go1.27.3, at the pins, `GOWORK=off`). A soundness text gets the
standard pair of tests: a context or gate that violates the text and makes the Go code panic, and
a control that meets the text and does not panic.

- **T5-a. `clientv3.WithRequireLeader` over a caller's context (7f-4's F2, deferred to 7f-3).**
  - **Recommended form: no trusted triple** (Q2). Translate `WithRequireLeader` with its body
    (`client/v3.toml`). Translate grpc `metadata.NewOutgoingContext` (one line,
    `context.WithValue(ctx, mdOutgoingKey{}, rawMD{md: md})`), `Pairs`, `MD.Copy` and `MD.Set`
    with bodies (`Code/google_golang_org/grpc/metadata.toml`). `FromOutgoingContext` already has a
    spec (`Proof/google_golang_org/grpc/metadata/FromOutgoingContext.lean`). Then the context's
    `Value` at every key other than grpc's outgoing one is the parent's, by Perennial's `WithValue`
    spec, so every key fact (`k8sCtxOk`, `#HCC`, the new T5-b key) carries over with no new axiom.
  - **The fallback**, if Goose or the metadata model blocks the translation: F2's triple as
    `notes/k8s-7f4-draft.md:144-160` states it, **restated** to give, for every key `k` other than
    `mdOutgoingKey{}`, `WP c.Value(k) {Φ} ⊣⊢ WP ctx.Value(k) {Φ}`. Without that clause the triple
    would repeat the T-h..T-k mistake: the derived context's keys would be unconstrained.
  - **Go evidence:**
    - `TestWithRequireLeaderValues`: the result answers every probed key as the parent does, and the
      outgoing key with the parent's metadata plus `hasleader`;
    - `TestWithRequireLeaderNoAlias`: the parent's `MD` is not mutated (the `Copy`).
- **T5-b. The APF initialization-signal key.**
  - A fact `context.valueAt ctx flowcontrol.initSignalKeyAny flowcontrol.initSignalRes` in
    `k8sctx.k8sCtxOk` (`Proof/k8s_io/apiserver/pkg/audit/CtxKeys.lean`, the fourth Kubernetes key,
    in the pattern of the context sweep's runtime/trace key). The producers (`k8sCtxOk_of_nil`,
    `_background`, `_todo`, `_bgFrom`, `_of_ctxValueNil`) are re-proved.
  - **Recommended `initSignalRes v`: `v` is not an `InitializationSignal`, or is a nil one** (Q3).
    That is what the driver passes (a `WithTimeout` of `Background()`), and what the cacher's
    reflector passes in kube-apiserver. The alternative also admits APF's own
    `*initializationSignal` (`apf_context.go:75-89`, `once.Do(close(done))`), with
    `initializationSignal.Signal` translated over Perennial's `sync.Once`. It covers watches that
    bypass the cache under APF, at more cost.
  - Without T5-b, a context whose `Value` panics at that key, or which stores a foreign
    `InitializationSignal` whose `Signal` panics, meets `k8sCtxOk` and makes `store.Watch` panic.
  - **Go evidence:**
    - `TestWatchInitializedKeyPanics`: a fake `clientv3` and a context panicking at the key;
      `store.Watch` panics;
    - `TestWatchInitializedForeignSignal`: a foreign `Signal` that panics;
    - `TestWatchInitializedControl`: the key's value nil, every other key except the covered ones
      panicking; `Watch` returns.
  - Translation: `flowcontrol`'s `WatchInitialized`, `initializationSignalFrom` and the key's type
    with bodies (now names-only, `Code/k8s_io/apiserver/pkg/util/flowcontrol.toml`).
- **T5-c. `featureOn`: the gate's `Set(s ++ "=true")`** (sweep repairs B5's other half).
  - The text: a persistent opaque `featureOn g s`, with `Set(s ++ "=true")` returning nil and
    giving it, or an error. `Enabled(s)` returns `true` once `featureOn g s` holds. `featureOn`
    and `featureOff` exclude each other for one `s`: a `Set` of the other value is excluded by the
    header's environment assumption, which is **restated** as "no code changes a set value
    except one `Set(s=b)` per feature, before any `Enabled(s)`".
  - The driver calls `Set("WatchList=true")` (7f-0).
  - The alternative to `Set` is the default at the emulated version (`WatchList` true since 1.34).
    That needs a model of the emulated version, more trusted text. **Not recommended** (Q4).
  - **Go evidence:**
    - `TestSetWatchListTrue`: after `Set("WatchList=true")`, `Enabled` is true;
    - `TestSetTrueThenFalse`: the excluded sequence, to show what the assumption rules out;
    - `TestSetLockedFails`: `Set` of a locked-to-default feature errs and changes nothing.
  - The B5 no-other-mutator check (`/shared/tmp/sweep-repairs-1/b5-r1.md`) is rerun over the
    examples' compiled closure with the new driver.
- **T5-d. `wait.Jitter(d, f)` returns some duration.** A local trust-boundary spec, or a
  translation of `Jitter` over `rand.Float64` if Perennial's `math/rand` has one (S0 decides; a
  translation is preferred). It is reached only on the too-large-RV error path.
- **No trusted text needed** (translations or no-op specs, as `notes/k8s-7f-scope.md` §3 lists):
  - `Event.IsCreate`, `WithPrevKV` (7f-3), `runtime.Decode` (into `runtime.toml`'s list);
  - `getResourceSizeEstimator` (a reader slot of `collectorMux`, with a store invariant that the
    estimator stays nil, and an entry in `etc/bounds-*`);
  - `errors.As` (Perennial's), `fmt.Errorf` (`%q`/`%d`/`%s`), `Event_EventType.String`;
  - `apierrors.NewInternalError`/`NewResourceExpired`/`APIStatus.Status`;
  - klog and metrics no-ops in the existing patterns; `clock.RealClock`.
  - S0 lists each one. A spec found missing is either the obvious one, decided as a form, or else a
    stop.
- **7f-3's texts.**
  - **The client spec's `prevKv`** is proved, not trusted: none for a create, otherwise none or the
    key's kv at `rev - 1`.
  - **"None" must stay admitted even without compaction:** `issues/etcd-watch-prevkv-before-created.md`
    reproduces a `PrevKv` watch whose first events arrive without `PrevKv` (the send loop reads
    `sws.prevKV` before `recvLoop` records it, `watch.go:349` against `:444`). So `parseEvent`'s
    nil-`PrevKv` error is reachable, and `store.Watch.spec` must allow the Error event it causes.
    The safety statement is unaffected: Error events are dropped anywhere.
  - The parent Scope said "none only if that read failed, which is impossible without compaction".
    The issue shows that is false, and this Scope corrects it.

## 5. `store.Watch.spec` and its premises' producers

The triple as sketched in `notes/k8s-7f-scope.md` §5.3. What changes after 7f-4:
- the context premise:
  - `watchCtx ctx cd ∗ ctxOk ∗ ctxErrClient ∗ k8sCtxOk ctx` of the caller's context (no
    `ctxNeverDone`: the watcher never reaches `processListItem`);
  - `k8sCtxOk` carrying T5-b's key;
  - the driver produces all of it from `WithTimeout(Background())`, by the existing
    `_bgFrom`-style producers;
- `featureOn g "WatchList" ∗ featureOff g "EtcdRangeStream"`. No fact on
  `ConcurrentWatchObjectDecode`: both values are proved (7f-5b), and before 7f-5b the spec carries
  `featureOff g "ConcurrentWatchObjectDecode"` as a **temporary, named premise** (Q6);
- the thread bound: `threadTok`s for the watch's goroutines (`run`, `startWatching`,
  `serialProcessEvents`, and the client's per-watch substream). They come from adequacy's bound,
  with stage B's pool;
- the post: `k8sWatch c wi γ req`, the consumer's view, `□ StreamOkL`-shaped facts over a persistent
  lower bound of etcd's log, and `Stop` callable. The Draft states it over `KWatchStream.lean`'s
  `StreamOkL`, so that 7f-6's link to `watchOkL_of_stream` is by name.

**The store invariant grows:**
- the watcher's fields (`getCurrentStorageRV`, the closure over `GetCurrentResourceVersion`;
  `getResourceSizeEstimator`);
- the estimator stays nil.

`New`'s proof is extended. **Many concurrent watches on one client watcher** (parent §2.3 item 4):
S0 checks that `isClientWatcher` is persistent and that `watcher.Watch.spec` can be called again
while earlier watches run. That is a risk to settle before the Draft.

## 6. Stages, hard stops, estimate

| Stage | Contents | Lean lines | Stop |
| --- | --- | --- | --- |
| **S0** | Notes and Go only: the context and error-method enumeration of §4.1 (file:line, with the client's watch path); the Goose dry run of the configuration (drop `!parseEvent`/`!watchChan.startWatching`; add `IsCreate`, `WithPrevKV`, `WithRequireLeader` and grpc metadata's four functions, `runtime.Decode`, `flowcontrol`'s two functions, `Jitter`), with elaboration checked by a targeted build; the `examples/premisefix/watcherctx` tests; the many-watches check (§5) | 0 (Go ~400) | **S1: the trusted package (T5-a fallback if needed, T5-b, T5-c, T5-d) for 81's axiom review** |
| **7f-3a** | statements: `isRangeWatch` with `prevKV`, `watchStateRespOk`'s `prevKv` (none admitted, §4.2), the server's `rawRespOk`; `WithRequireLeader` translated (or F2 restated) | 300-600 | **S2: 7f-3's statements** (the parent's checkpoint 3) |
| **7f-3b** | the server: `swsMu` with `prevKV` entries, `recvLoop`, `sendLoop`'s branch over mvcc's range at `rev - 1` | 700-1200 | - |
| **7f-3c** | the client: `watchGRPCStream.run` and `serveSubstream` re-proved, and the other users of the spec (watchkv, cachekv, linkv3p, the compactor, `etcdstart.Collect`) at `prevKV` false | 1000-1700 | checkpoint: 7f-3 built, tcb unchanged; land (81's go) |
| **7f-5a-D** | the Draft: `store.Watch.spec`, `k8sWatch`, the internal specs' list, the protocol (`incomingEventChan` SPSC, `resultChan` with two producers) | 400-700 | **S3: the Draft** (the parent's checkpoint 5) |
| **7f-5a-P** | the proofs: the trusted texts in Lean (after S1); the configuration; `parseKV`, `parseEvent`, `progressNotifyEvent`, `prepareObjs`, `decodeObj`, `transform`, `filter`; the error path; `blockLogger`; `queueEvent`/`sendEvent`/`sendError`; `serialProcessEvents`, `sync`/`syncPaginated`, `startWatching`, `run`, `createWatchChan`, `watcher.Watch`, `store.Watch`; `getResourceSizeEstimator`; `New`'s invariant; the etcd3 `Link`/`Results` | 3200-4800 | checkpoints after the leaf functions and after `startWatching`; land (81's go) |
| **7f-5b** | the concurrent branch (scheduler, collector, per-event goroutines); the risk of `WaitGroup.Add` during `Wait` at a positive count, checked against Perennial's thread-token `WaitGroup` spec **first** (a limitation there is recorded, not patched) | 1000-1600 | a stop if the `WaitGroup` spec cannot express it; drop Q6's temporary premise |

**Estimate.**
- Lines:
  - 7f-3: 2000-3500;
  - 7f-5a: 3600-5500;
  - 7f-5b: 1000-1600;
  - **6600-10600 Lean lines** in all, plus ~400 Go.
- 7f-4 ran over its estimate: one stage in plan, but ten agent contexts and five trusted addenda
  (T-g..T-k), each with a refutation and a review. Expect the same here:
  - one or two addenda in S1, mostly the T5-a/T5-b context work;
  - 7f-3c's re-proof of `run` (230 s per check with `--fast`; use `--split`).
- In agent contexts:
  - S0: 1;
  - 7f-3: 3-5;
  - 7f-5a: 4-6;
  - 7f-5b: 2-3.

**Order.** S0 and S1 first. Then 7f-3a/S2. After that, 7f-5a-D (the Draft, against 7f-3a's
statements) can run in parallel with 7f-3b/3c, in a second worktree. 7f-5a-P links only after
7f-3 lands. 7f-5b comes before 7f-6's Freeze.

## 7. Open questions for 81 (each with a recommendation)

- **Q1. Order: 7f-3 first, inside this plan.** (a) 7f-3a (statements) before 7f-5a's Draft, then
  7f-5a's Draft in parallel with 7f-3's proofs; (b) 7f-3 completely, then 7f-5a; (c) 7f-5a against
  an unproved client spec (a `sorry` in the link until 7f-3). **Recommended: (a).** It costs one
  extra worktree. (c) would put a `sorry` under a linked result.
- **Q2. `WithRequireLeader`: translate it, or the trusted F2 triple.** **Recommended: translate**
  `WithRequireLeader` and grpc metadata's `NewOutgoingContext`/`Pairs`/`MD.Copy`/`MD.Set`, and use
  Perennial's `WithValue`. That needs no new axiom, and every key carries over. The fallback is F2
  restated with the all-keys clause (§4.2 T5-a), never F2 as the 7f-4 Draft wrote it.
- **Q3. The APF signal key's admitted values.** (a) nil or not an `InitializationSignal`; (b) also
  APF's own `*initializationSignal`, with `Signal` translated. **Recommended: (a) now**, as a scope
  restriction stated in the docstring (the driver and the cacher pass no signal). (b) belongs to a
  later stage that covers APF's handler chain.
- **Q4. `WatchList` on: by `Set("WatchList=true")` (`featureOn`), or by the default at the
  emulated version.** **Recommended: `Set`**, with B5's environment assumption restated (one `Set`
  per feature, before any `Enabled`). It is one joint restatement, as 7e's `featureOff` was, and the
  default route needs a model of the emulated version.
- **Q5. `prevKv` "none" admitted without compaction** (the parent Scope said that was impossible).
  **Recommended: yes**, since `issues/etcd-watch-prevkv-before-created.md` reproduces it. So
  `parseEvent`'s error path is proved reachable-and-handled, not ruled out. No closed theorem
  weakens, because Error events are dropped.
- **Q6. Before 7f-5b: a temporary `featureOff g "ConcurrentWatchObjectDecode"` premise on
  `store.Watch.spec`.** The driver would `Set(...=false)` until 7f-5b. Or `store.Watch.spec` waits
  for 7f-5b before it is exported. **Recommended: the temporary premise**, named in Results and
  STATUS and removed by 7f-5b. 7f-6's Freeze still requires 7f-5b, since Kubernetes runs with the
  default on (Q7f-3 stands).
- **Q7. The parent Scope's `Q7f-6` (when 7f-0's driver change lands).** The record fields went in
  with 7e. What is left (`watch.go`, `KWatch`'s step, `Check` through `RunLin2`, `Main*` with
  watchers) **is recommended to go with 7f-6**, not 7f-5, except `Set("WatchList=true")`. That call
  goes in S0, so that T5-c's evidence runs on the real driver.

## 8. Decisions (etcd-grove-81, 2026-11-13: every recommendation of §7)

- **Q1** (a): 7f-3's statements first. Then 7f-5a's Draft in parallel with 7f-3's proofs, in a
  second worktree. No `sorry` under a linked result.
- **Q2**: translate `WithRequireLeader` and grpc metadata's helpers. The restated F2 triple is
  only a fallback.
- **Q3** (a): the APF signal key holds nil, or a value that is not a signal, for now.
- **Q4**: `Set("WatchList=true")`. B5's assumption is restated to one `Set` per feature, before
  any `Enabled`, with Go evidence for the restatement.
- **Q5**: accepted. `PrevKv` may be missing without compaction
  (`issues/etcd-watch-prevkv-before-created.md`).
- **Q6**: accepted. A temporary, named premise (`ConcurrentWatchObjectDecode` off) on
  `store.Watch.spec`, listed in STATUS as temporary. 7f-6's Freeze requires 7f-5b.
- **Q7**: accepted. The rest of 7f-0 goes with 7f-6. `Set("WatchList=true")` goes into the driver
  in S0.
- **Next:**
  - S0: the enumeration, `examples/premisefix/watcherctx`, and `Set("WatchList=true")` in the
    driver;
  - then S1's trusted package, written in Lean and built;
  - STOP for 81's axiom review before any proof uses it.
