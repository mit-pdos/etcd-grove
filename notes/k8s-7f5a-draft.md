# k8s 7f-5a-D: the Draft of the etcd3 watcher's serial branch (2026-11-14; hard stop S3, for etcd-grove-81)

**Revised 2026-11-14 after etcd-grove-81's review** (decisions D1-D7 accepted as recommended; the
review's findings fixed as 81 decided): §8 lists each change, old → new. The sections below
describe the revised Draft.

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
- **`kStreamOk … m σ st evs`** and **`kStreamSub … m σ st evs`**: the events received, with the
  Error events removed wherever they occur, are a prefix (`kStreamOk`), or a subsequence
  (`kStreamSub`: in order, none invented, none repeated, some possibly missing), of the ideal
  stream from the start point `st` (`kIdealL`). Every event has a type of at most 4. Both are
  `kStreamRel R` for the relation `R`.
  - With initial events: the initial events at `st` (a revision of `σ`), then the annotated
    bookmark at `st` if it was asked for, then a `KTail` from `st`.
  - Without initial events: a `KTail` from `st`.
- **`kStartOk m σ0 st`**: where the start point comes from, at a state `σ0` the caller's read
  update fired at.
  - With initial events: `st = σ0.rev`, the revision of the first page's linearizable `Get`
    (`syncPaginated` overwrites `wc.initialRev` with it, even for a requested revision), and
    `st ≥ max req 1` (`startWatching` checked the request against `getCurrentStorageRV` first).
  - Without: the requested revision when positive, else `st = σ0.rev`, the revision of
    `getCurrentStorageRV`'s quorum `Get`.

  So a watch from "now" starts at a state the caller's `Q` saw during the call: the caller's `Q`
  gives its freshness.

  This is `StreamOkL`'s shape, with two differences. It also covers the legacy case and a watch-list
  without bookmarks. Its bookmark condition is stronger: no etcd event in scope at all, not just no
  event that passes the predicate.

```lean
def kStreamRel (R : List (KWEv Obj) → List (KWEv Obj) → Prop) (dec : Dec Obj) (sel : Obj → Bool)
    (emp : Bool) (z : Obj) (inS : GoString → Bool) (m : KWatchMode) (σ : KVState) (st : Nat)
    (evs : List (KWEv Obj)) : Prop :=
  (∀ e ∈ evs, e.t ≤ 4) ∧ (m.forceInit = true → st ≤ σ.rev) ∧
  ∃ full, KTail dec sel emp z σ inS st full ∧ R (kNonErr evs) (kIdealL dec sel inS z m σ st full)

def kStartOk (m : KWatchMode) (σ0 : KVState) (st : Nat) : Prop :=
  if m.forceInit then st = σ0.rev ∧ max m.req 1 ≤ st
  else if 0 < m.req then st = m.req else st = σ0.rev
```

## 2. The consumer's view: `k8sWatch`

`k8sWatch c W wi γ cd sel emp inS m Q` says four things:
- `wi`'s `ResultChan()` returns a channel `ch`: a persistent triple, callable at any time and from
  anywhere.
- `Stop()` takes `kLive γ` (the first call) or `kStopped γ` (a later one), and gives `kStopped γ`
  (persistent). The caller holds `kLive γ` (exclusive), which excludes `kStopped γ`.
- `ch` is an SPSC channel (`isSpsc`), and the caller holds its consumer half with nothing received
  yet (`spscConsumer γ.res []`).
- The `i`-th element (`kResElem`) is a `watch.Event` `v` that is the event `e` (`wevAt`). The models
  of the first `i + 1` events are `evs ++ [e]`: each sits at its index of a ghost mono list `γ.evs`,
  so the consumer knows they are the events it received. Unless they are all Error events, there are
  a start point `st` and states `σ0`, `σ` at which the caller's read update fired (`□ Q lb0 σ0`,
  `□ Q lb σ`) with `kStartOk m σ0 st`, and:
  - `kStreamSub σ st (evs ++ [e])`, always;
  - `kStreamOk σ st (evs ++ [e])`, unless the watch is no longer live: **`kCancelled γ cd`**, i.e.
    `kStopped γ ∨ □ cd.PDone` (the consumer stopped it, or the caller's context is done, which is
    what Perennial's context model gives of a done context).

  So a consumer that has not called `Stop` (it holds `kLive γ`) and whose context's `PDone` it can
  refute reads the no-gap prefix of every event it received. That is the form the driver (7f-6)
  uses: it checks the events received before it stops the watch, under a context whose `PDone` it
  owns (`WithCancel(Background())` with its own `PDone'`). Under `WithTimeout`'s context
  (`PDone := True`) only the subsequence is promised: a watch past its deadline can skip events, and
  Perennial's `Err()` returning `nil` does not tell the model the context is not done.

`wevAt S W v e` describes one event:
- An Error event has type `"ERROR"` and a `*metav1.Status` object with status `"Failure"`
  (`statusFailureAt`). That is what the driver's `WError` needs, since a foreign object is `WBad`.
- Any other event has the type string of `e.t`. The consumer gets its object owned:
  `S.objAt v.Object (annotated body if e.ann) (S.fmtRV e.rv)`.

The channel's closing carries nothing (`R := True`), and no thread token is owed: the watch's three
goroutines (`run`, `startWatching`, `serialProcessEvents`) get a token at their `go` statements
(`wp_fork_tok`) and give it back when they exit (`wp_ThreadExit`), so the spec takes none (§8).
Within one watch the client's resumption is invisible: the client spec already rules out gaps and
duplicates; the gaps after cancellation are the etcd3 watcher's own (`queueEvent`).

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
- No `threadTok` (the goroutines' come from their `go` statements); `threadBound GF ≤ 2^30 - 1` as
  in `GetList` (kept from the first Draft; whether a callee needs it is checked in 7f-5a-P, and the
  bounds gate counts it when the triple moves to `Spec/`).
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
      ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗
      (|==> readAus c γk (Q 0)) ∗ (□ ∀ lb σ, □ Q lb σ -∗ |==> readAus c γk (Q σ.rev)) }}
    sp.Watch(ci, key, opts)
  {{ (wi err : GoInterface), RET (wi, err);
      ⌜err ≠ nil⌝ ∨ (⌜err = nil⌝ ∗ ∃ γ, k8sWatch c W wi γ cd sel emp (kScopeOf c k opts.Recursive')
        (kModeOf sie opts.Predicate'.AllowWatchBookmarks' n) Q) }}
```

Errors are not identified: the driver records any `Watch` error as `WFailed`. **Many concurrent
watches** on one client watcher are allowed, since `clientWatchOk` is persistent and the client's
`watcher.Watch.spec` consumes nothing exclusive. That settles the risk in Scope §5.

## 4. The protocol (internal, in the Draft file's §4)

- **`incomingEventChan`** is an SPSC channel. Its producer is `startWatching` and its consumer is
  `serialProcessEvents`. Its `i`-th element (`kInElem`) is an `*event` holding a raw event at a
  fired state `σ` (`eventAt σ`; `KRaw`: an initial key-value, an etcd event, or a bookmark with its
  annotation flag). An etcd event's previous value is `nil` for a create, and for any other event
  the value of `kPrevAt σ e` (the client's `prevKvOk`; `parseEvent` let the event through, so its
  `PrevKv` is not `nil`). The raw events queued so far are `raws ++ [r]` (a mono list `γ.raws`),
  from a start point `st` with `kStartOk` at a fired `σ0`: `kRawStreamSub` always, and
  `kRawStreamOk` unless `kCancelled γ cd`. `kRawStreamRel` has `kStreamRel`'s shape before
  `transform`.
- **`resultChan`** has two producers: `sendEvent`, in order, from the processing goroutine, and
  `sendError`, an Error event from either goroutine. **`kResInv`** is an invariant that holds:
  - the SPSC's producer token;
  - the authority of `γ.evs` (the sent events' models);
  - the processing goroutine's count of raw events taken and sent or filtered out (`procd`, half):
    a `sendEvent` that gives up on the done context makes the goroutine return, so that raw event
    is not counted and the equation below stays an equation;
  - the equation `kNonErr evs = raws.filterMap (kRawToEv …)`;
  - unless `raws = []`, the facts of `raws` (fired `σ`, `σ0`, `kStartOk`, `kRawStreamSub`, and
    `kRawStreamOk` or `kCancelled`), so that a `sendError` from the producer can state its element's
    facts (its `kNonErr` part is unchanged). An all-errors stream claims nothing (no read update may
    have fired before an early `sendError`).

  A send commits through `spsc_send_au` inside the invariant. `run` closes the channel after
  `resultChanWG.Wait()` (both producers have exited), taking the token from the invariant.
- **The cancellation witness.** `wc.cancel` is `WithCancel`'s cancel with the Done proposition
  **`kCancelPD γ cd := kStopped γ ∨ kProdExited γ ∨ □ cd.PDone`**: `Stop` has `kStopped`, `run`'s
  cancel after `watchClosedCh` has `kProdExited` (set by `startWatching` before it closes the
  channel, after its last `queueEvent`), and `run`'s cancel after `wc.ctx.Done()` has the closed
  channel's proposition. A `queueEvent` that drops an event sees `wc.ctx`'s Done closed, hence
  `□ (cd.PDone ∨ kCancelPD γ cd)`; the producer is still running (it owns the right to set
  `kProdExited`), so that is `kCancelled γ cd`, which every later element carries. Only the
  producer drops-and-continues, so the processing goroutine's sends keep the equation.
- **The key pure lemma**: `kRawStreamRel R σ st raws → kStreamRel R σ st (raws.filterMap (kRawToEv
  σ))` for both relations (filterMap is monotone for prefix and sublist), with Error events
  interleaved freely and prefixes closed, together with transport along `kvSameHist` to a later
  state. The serial goroutine sends exactly the non-`none` transforms in order, and it stops at its
  first error or give-up.

## 5. Trusted texts

| Item | Status | Text | Go evidence |
| --- | --- | --- | --- |
| **T5-e**: `WithRequireLeader.wp_proof` gains `□ ∀ cd, isContext ctx cd -∗ isContext c cd` | **NEW, for 81's axiom review** (D2, accepted) | One more conjunct in the post, persistent and generic in the descriptor (as `WithValue.spec`'s): over a parent with Perennial's context model, the result has it too, with the same descriptor. Go: `c` is a `*valueCtx` at grpc's key (in both of `WithRequireLeader`'s branches: the parent with or without outgoing metadata). Its `Deadline`, `Done`, `Err` are promoted from the parent, `Value(&cancelCtxKey)` walks to the parent's, and `parentCancelCtx(c)` reads exactly those two, so it succeeds, finding the parent's `*cancelCtx` (`HParentCC`). `c`'s type is not `stopCtx`. `HDoneFresh` is ghost state of the same descriptor. The repository's `WithValue.spec` already claims this for five key types; this is grpc's sixth. isContext claims nothing about cancellation reaching children. | `examples/premisefix/watcherctx/draft7f5a_test.go`: `TestWithRequireLeaderIsContext` (7 parent shapes × 200, including two with outgoing metadata already: `Deadline`, the same `Done` channel, `Err` and `Cause` the parent's, `Err` a context error, and `parentCancelCtx(c)` succeeding, observed through a stand-in: `WithCancel(c)`'s child is done as soon as the parent's cancel returns); `TestWithRequireLeaderIsContextDone` (3 already-done parents × 200: cancelled, cancelled with metadata, past the deadline; the same `Done`, `Err`, `Cause`; `WithCancel(c)`'s child done at once); `TestIsContextCheckDetects` (the stand-in fails on a wrapper with its own `Done`, 200/200). Older: `TestWithRequireLeaderOtherKeys`, `…CancelPropagates`. The reviewer's adversarial parents: `/shared/tmp/coord-81/7f5a-review/t5e_test.go`. All pass (GOWORK=off, go1.27.3, 32G cap). |
| **T5-f**: leaf no-op specs the watcher reaches | **NEW texts, for 81's axiom review** (D7, accepted); Lean statements in the Draft's §5 (`def … .spec`, no axiom), axioms in 7f-5a-P | `metrics.RecordEtcdEvent(gr)`, `RecordEtcdBookmark(gr)`: return, given `utf8Valid` of `gr`'s group and resource (as `RecordEtcdRequest`'s; the store has it in `storeListOk`). **`mvccpb.Event_EventType.String(t)`**: returns some string, for any `t`, given **mvccpb's `isPkgInit`** (`String` reads the enum descriptor `file_kv_proto_init` fills; reached on `parseEvent`'s nil-`PrevKv` path, Q5). **`klog.Warningf(f, args)`**, restricted (decision 3): `f = pre ++ "%v" ++ post` with no `%` in `pre`, `post` (one bare `%v`: no `GoString()`, no reflection printing), `args ↦*□ [err]` (one error, read-only; an owned slice is made read-only by the caller) with `errStrOk err` (`Error()` returns, no `Format` method); post `True`. Docstring names the assumed configuration: klog's default flags (stderr output), no `SetLogger`/`SetOutput` (otherwise klog may `os.Exit(2)` on an unwritable log file or a full disk, die of `SIGPIPE`, or run a foreign logger). `notes/klog-args-fix.md` did not exist when this was written: **to be aligned** with the form adopted there for `klog.Errorf.spec`. | same file: `TestRecordEtcdEventBookmarkLabels` (valid labels return; invalid UTF-8 panics once registered, **now asserted**: the test fails if either call does not panic), `TestEventTypeStringReturns` (0, 1, 2, 7, -1), `TestKlogWarningfReturns` (the watcher's call shape). The reviewer's counterexamples to the unrestricted form: `/shared/tmp/coord-81/7f5a-review/klogt/klog_test.go`. |
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
   - `kRawToEv` filtered maps `kRawStreamRel R` to `kStreamRel R`, for the prefix and the sublist
     relations (raw to cooked);
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
4. **Channel operations** (~400-600): `queueEvent` (`kInElem`; on the done context, the
   cancellation witness `kCancelled` from `kCancelPD`), `sendEvent` and `sendError` (in `kResInv`).
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
- **`WithCancel` keeping the parent's `PDone`** (the cancellation witness, §4). `wc.ctx` is
  `WithCancel(WithRequireLeader(ctx))`, an `isContext` parent that is not a `*cancelCtx`. Perennial's
  `context.WithCancel.spec` gives the child `PDone := parent.PDone ∨ PDone'` only for an
  `isCancelCtxCtx` parent; `wp_WithCancel_any` (any `isContext` parent) gives `PDone := True`, which
  makes a dropped event's witness unprovable. True in Go: the child is closed by its own cancel, by
  `propagateCancel`'s already-done arm (the parent's Done closed: `□ parent.PDone`), or by the
  `*cancelCtx` `parentCancelCtx(parent)` found, whose Done channel is the parent's (the check
  `pdone == done`), closed before it cancels its children. The model loses the last link:
  `HParentCC` gives `isCancelCtx p` with an unknown Done proposition. The general fix is a Perennial
  change (`HParentCC` saying `p`'s Done channel is `ch`, or that `p`'s proposition gives
  `s.PDone`; then a `wp_WithCancel` over `isContext` keeping `PDone`), proposed on its own
  (CLAUDE.md, "Changes to Perennial"); until then 7f-5a-P would need a marked local axiom (a stop for
  81). To be decided before step 4.
- **The start point's firing** (`kStartOk`): `getCurrentStorageRV` is `GetCurrentResourceVersion`,
  whose `Q R m σ` is instantiated with the watch's `Q`'s re-armed reads; `syncPaginated`'s first
  page fires through `Client.Get`. Both give `□ Q lb σ0` with `σ0.rev` the header revision.
- **`statusFailureAt`** on every error path. An error that is itself an `APIStatus` with another
  status would break it; none is expected, since the constructors used all set `Failure`.
- **`prevValue` empty for an update when the predicate is not empty.** `filter(nil)` would call
  `Matches` on a `nil` object. Stored values are never empty (`encode_ne_nil`, `toS`), but the
  proof must carry that from `kvWfHist`.
- **`watchContractOk`'s `runtime.Decode`** must hold of the driver's codec without a target (7e's
  Go has it; the Lean is new in 7f-5a-P or 7f-6).

## 7. Decisions (all accepted as recommended by etcd-grove-81, 2026-11-14)

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

## 8. Review fixes (2026-11-14), old → new

The review: `/root/.claude-csail/projects/-shared-etcd-grove/c04a65b0-a272-4ae4-94c7-91aa4a20ea30/subagents/workflows/wf_78063c5e-d6c/journal.jsonl`;
81's decisions 1-4 in `questions.md` (2026-11-14).

1. **BLOCKER, the no-gap prefix after cancellation** (decision 1).
   - Old: every `resultChan` element carried `kStreamOk` (a prefix of the ideal stream), and so did
     every `incomingEventChan` element (`kRawStreamOk`) and `kResInv`; false once `wc.ctx` is done
     (`queueEvent` drops an event and the producer goes on; Go test: 13 of 400 stopped watches with a
     gap).
   - New: `kStreamSub` (subsequence) always, and `kStreamOk` unless `kCancelled γ cd :=
     kStopped γ ∨ □ cd.PDone`. `k8sWatch` gives the caller `kLive γ` (exclusive); `Stop` takes
     `kLive γ ∨ kStopped γ` and gives `kStopped γ` (old: `Stop` took nothing). The protocol carries
     it: `kInElem` and `kResInv` hold `kRawStreamSub` and `kRawStreamOk ∨ kCancelled`; `kCancelPD`
     (`wc.cancel`'s Done proposition) and `kProdExited` are new; `KWatchNames` gains `stop` and
     `prodEx`. An all-Error-events prefix claims nothing (old: it claimed a fired state too, which an
     early `sendError` cannot give). The risk the proof carries (Perennial's `WithCancel` over an
     `isContext` parent): §6.
   - Non-issue recorded: `nonissues/k8s-etcd3-watcher-gap-after-cancel.md`, test
     `nonissues/k8s-etcd3-watcher-gap-after-cancel/gap_test.go` (the reviewer's, rerun: 13 of 400
     trials with a gap). `watch.Interface`: after `Stop` the producer "should stop sending events";
     nothing is promised about events after it.
2. **Start-point freshness** (decision 2).
   - Old: `kStreamOk`'s cursor `s0` was free at `RV 0`, `SendInitialEvents=false` (`0 < req → s0 =
     req` only), a watch-list's `r0` only `max req 1 ≤ r0 ≤ σ.rev`; the docstring claimed "the
     store's current revision when the watch started".
   - New: the start point `st` is an argument of `kStreamOk`/`kStreamSub`, and the element carries
     `∃ σ0, □ Q lb0 σ0 ∗ ⌜kStartOk m σ0 st⌝`: `st = σ0.rev` for a watch-list (the first page's
     `Get`) and for `RV 0` without initial events (`getCurrentStorageRV`), `st = req` for a positive
     request without initial events. Docstrings say exactly that.
3. **`klog.Warningf`** (decision 3).
   - Old: "returns" for `(fmt, err)`, modelled on `klog.Errorf.spec`'s any `args`.
   - New: `klog.Warningf.spec` in the Draft's §5: one bare `%v` in the format, `args ↦*□ [err]`,
     `errStrOk err`; the assumed logging configuration in the docstring. `notes/klog-args-fix.md` did
     not exist yet; to be aligned with it.
4. **Minors** (decision 4).
   - T5-e: old `isContext ctx s -∗ isContext c s` at the spec's `s`; new
     `□ ∀ cd, isContext ctx cd -∗ isContext c cd`.
   - Go test: added the existing-metadata parents (`metadata-over-cancel`, `metadata-over-timeout`)
     and `TestWithRequireLeaderIsContextDone` (precancelled, precancelled with metadata, expired
     deadline).
   - Wording: old "`WithCancel(c)`'s child cancelled synchronously"; new "`parentCancelCtx(c)`
     succeeds", with the synchronous check named as the test's stand-in (test header, §5).
   - `Event_EventType.String`: old "for any `t`"; new with mvccpb's `isPkgInit` (Lean statement in
     the Draft's §5).
   - `TestRecordEtcdEventBookmarkLabels`: old logged the invalid-UTF-8 panics; new fails unless both
     panic.
   - `eventAt`: old `∃ pv, prevValue ↦*□ pv`; new `eventAt σ`: `nil` for a create, else the value of
     `kPrevAt σ e`.
   - Thread tokens: old three `threadTok`s taken and never returned (`R := True`); new **none
     taken**: a goroutine gets its token at its `go` statement (`wp_fork_tok`) and gives it back at
     its exit (`wp_ThreadExit`), and `Watch`'s own thread calls nothing that borrows one
     (`GetCurrentResourceVersion.spec`, the client's `Get` and `Watch` take none; `startWatching`
     lends its own to `getResourceSizeEstimator`). So there is nothing to return at close.
     `threadBound GF ≤ 2^30 - 1` stays (GetList's), to be dropped in 7f-5a-P if no callee needs it.
   - klog's exit paths: the configuration assumed is named in `klog.Warningf.spec`'s docstring.

## 9. For the re-review

- The cancellation witness's form (`kLive`/`kStopped`, `□ cd.PDone`), and that 7f-6's driver needs a
  context whose `PDone` it can refute (not `WithTimeout`'s `True`) to read the prefix. Recommended:
  as drafted; 7f-6 switches the driver to `WithCancel(Background())` with its own `PDone'`.
- The Perennial gap for `WithCancel` over an `isContext` parent (§6 risks). Recommended: propose the
  Perennial change (an entry in `notes/perennial-changes.md` when 7f-5a-P starts), and a marked
  local axiom only if it is not in before step 4.
- `klog.Warningf.spec`'s restriction, to align with `notes/klog-args-fix.md`.

**Re-review (etcd-grove-81, 2026-11-14): accepted.** (1) The witness form stays; the 7f-6 plan
(`notes/k8s-7f-scope.md`, after §9's table) records the driver's move to `WithCancel(Background())`
with its own `PDone'`. (2) The `WithCancel` gap is an entry in `notes/perennial-changes.md`; a local
axiom is a stop for 81 if Perennial does not have it by 7f-5a-P's step 4. (3) `klog.Warningf.spec`
stays restricted until `notes/klog-args-fix.md` lands, then aligns. T5-e lands on its own first.

**T5-e as landed (form decided by the agent, 2026-11-14, for 81's checkpoint):** the axiom states
parts, not the wand: `Deadline()`'s and `parentCancelCtx`'s WP transfers from the parent and
`⌜c.ty ≠ stopCtx.ty⌝`, beside the existing `Done`/`Err`/`Value(&cancelCtxKey)` transfers; the proved
law `WithRequireLeader.isContext_of_post` (`WithRequireLeaderLaws.lean`) gives
`isContext ctx cd -∗ isContext c cd` for every `cd`. Reason: the wand form made the axiom-tok gate's
walk stop at `isContextDone` (a truncation, and the allow file adds no new `trunc` line), as for
T5-a's `watchCtx`. Same meaning. **`klog.Warningf.spec`** now takes `klog.Errorf.spec`'s form
(`args ↦*{dq} xs ∗ klog.argsOk f xs`, given back), as `notes/klog-args-fix.md` asks.


## 10. Independent re-review (2026-11-15), old → new

81's decisions in `questions.md` (2026-11-15); ledger entry of 2026-11-15 in `notes/specs-only/ledger.md`.

- **M1, the start progress notification: decided by 81 (2026-11-15): the client spec strengthened (ledger 2026-11-15; `watchStateRespOk`'s progress arm now always `hdrRev ≤ σ.rev`), so `KTail.bm` holds the start notification unchanged.** The analysis that led there: The client's `watchStateRespOk`
  admits a progress notification at the watch's start (`hdrRev = c`, `c + 1 = rev`) with no
  `σ.rev` bound (`WatchStateDefs.lean:125-128`); `startWatching` queues it as `KRaw.bm hdrRev
  false`, which `KRawTail.bm`/`KTail.bm` (`p ≤ σ.rev`) cannot hold. The Draft-local fix (`bm`
  admits `p = c` without the bound) would serve 7f-5a's own proof but not its consumer: 7f-6's
  bridge to the driver's `TailOk` needs `p ≤ hs.length`, and the driver's check rejects any event
  above the configuration's revision (`watchOkL`, `KWatch.lean:209`), while 7f-6's traffic (as the
  upstream test's) draws future resource versions for legacy watches (`notes/k8s-7f-scope.md` §1):
  a start bookmark at a future `req` would fail the check. etcd never sends one (`progressIfSync`
  returns unless `rev ≥ w.startRev`, `watchable_store.go:539` at the pin): the client spec is
  looser than etcd. Not changed in the Draft; the alternative, `hdrRev ≤ σ.rev` in the client's
  start disjunct (an exported client spec), waits on 81.
- **M2, the processor's cancel.** Old: `kCancelPD := kStopped ∨ kProdExited ∨ □ cd.PDone`, and the
  docstring derived `kCancelled` for the producer from it. New: `KWatchNames.procEx`,
  `kProcExited γ` (persistent; set by the processing goroutine before its `sendError`, whose
  deferred `wc.cancel()` follows), `kCancelPD := kStopped ∨ kProdExited ∨ kProcExited ∨ □ cd.PDone`;
  the producer's own `sendError` sets `kProdExited` before it; the producer, which refutes only
  `kProdExited`, keeps `kProcExited` as a third disjunct of `kInElem`'s no-gap fact
  (`kRawStreamOk ∨ kCancelled ∨ kProcExited`), refuted by the processor at each receipt.
- **m1, the error arm.** Old: `⌜err ≠ nil⌝`. New: `⌜err ≠ nil ∧ sie = some false ∧ uint.nat n = 0⌝`
  (under the premises the only error is `getStartWatchResourceVersion`'s `getCurrentStorageRV`,
  `watcher.go:193-217`: prepareKey, ParseResourceVersion, the recursive suffix and
  `ProgressNotify` are excluded by premises).
- **m2, `1 ≤ st`.** `kvWf` does not give `1 ≤ σ.rev`, nor does a firing (`kvAu` tells `kvRoom`).
  Old: `kStartOk`'s watch-list arm `st = σ0.rev ∧ max m.req 1 ≤ st`. New: `st = σ0.rev ∧ m.req ≤ st`;
  a consumer whose `Q` gives `1 ≤ σ.rev` reads `1 ≤ st` from the element's `□ Q lb0 σ0`.
- **The `WithCancel` gap.** Option (a): `notes/perennial-changes.md`'s entry now has the decision and
  a design sketch (`HParentCC` gives `□ (Pp -∗ s.PDone)` of the `*cancelCtx` it finds; a new
  `wp_WithCancel_ctx`). Steps 4-5 take `isContext wc.ctx { cd with PDone := cd.PDone ∨ kCancelPD γ cd }`
  as a premise; step 6 waits on (a).

## 11. The error leaves (7f-5a-P step 3, decided by etcd-grove-81 2026-11-15)

§5 expected the watcher's error leaves to need no new text over `clientErrTys`; that was wrong
(questions.md, thirteenth agent). 81 decided the route:

- **An internal predicate `kErrOk err`** (`WatchDefs.lean`): the error's calls on the error paths
  behave, stated over its own dynamic type and methods: `==` with any error returns (a comparable
  dynamic type); `Error()` returns and no `Format` method; as an `etcdError`, `Code()` returns; as a
  `grpcError`, `GRPCStatus()` returns some `s` and `s.Code()` returns; `errors.As(err,
  &(*corruptObjectDeletedError))` returns `false`; as an `APIStatus`, `Status()` returns a `Failure`
  status. `isCancelError`, `interpretWatchError`, `transformErrorToEvent`, `logWatchChannelErr` (step 3)
  and `sendError` (step 4) are proved over it, with no new text. (`(*StatusError).Status`, a one-line
  getter, is now translated with its body, `Code/k8s_io/apimachinery/pkg/api/errors.toml`: less
  trusted text, no spec added.)
- **The producers prove `kErrOk`** of each error they hand to `sendError` (step 5): `startWatching`'s
  (the client watch's close error `wres.Err()`, `GetCurrentResourceVersion`'s via
  `getStartWatchResourceVersion`, `parseEvent`'s `fmt.Errorf`, `sync`'s), `syncPaginated`'s
  (`interpretListError(err, true, …)` of the client's `Get` error, its own `fmt.Errorf`), and
  `transform`'s (none reachable under `kvWfHist`, `prepareObjs`' spec).
- **The candidate texts E1-E6**, drafted here for review when step 5 needs them. None is in Lean;
  none is an axiom. Each says what `kErrOk` needs of it.

**E1. `(*grpc/status.Status).Code()` returns** (trusted text; grpc's `internal/status` is names
only). Candidate: `∀ s : Loc, {{ True }} methods (*Status) "Code" #s #() {{ (c : codes.Code), RET #c;
True }}`. Go (`internal/status/status.go`): `if s == nil || s.s == nil { return codes.OK }; return
codes.Code(s.s.Code)`, a read of an immutable proto field (grpc never writes a `*Status` after
`New`; `Proto()` clones). Stronger form, if a consumer wants the code: `RET #(statusCode s)` over the
cache's `grpcErrMethodsOk` status. Go check to write: `Code()` of `nil`, of `status.New(c, m)` for
every code, of `FromError`'s results. Needed by `kErrOk`'s `grpcError` conjunct for a `*status.Error`.

**E2. The client watch's close error has a known dynamic type** (a proved spec strengthened, no
trusted text): `WatchResponse.Err()`'s post gives only nil-iff and `errStrOk`, and the watch state
keeps only `statusErrOk closeErr`. Candidate: `watchStateDefs`' close error carries `clientErr
closeErr` (exported client vocabulary: ledger entry first, interface regenerated), and `Err()`'s
post returns it, or one of `ErrCompacted`/`ErrFutureRev` (`EtcdError` values, `rpctypesInit`).
`kErrOk` of a `clientErr` error then follows per type: `*status.Error` (E1; `GRPCStatus` from
`grpcErrMethodsOk`; comparable pointer; `errors.As` false by a leaf-error `As` spec for this type,
see E3's note), `EtcdError` (its `Code()` translated or specified: rpctypes' `Code` is a field read;
comparable struct, needs `AsTypeTyped`), the context errors (`*errorString`: `errors.AsLeaf.spec`;
`deadlineExceededError`: a struct with no fields, comparable; neither is an `etcdError`,
`grpcError` or `APIStatus` by method sets).

**E3. `fmt.Errorf` without `%w` returns an `errors.New` error** (trusted-text strengthening of
EtcdGrove's `fmt.Errorf.spec`): its post says only `kFmtErr` (Error, no Format, a pointer error).
Candidate: for a format with no `%w`, the result is `interface.mkOk (*errors.errorString) #x` (Go:
`fmt.Errorf` returns `errors.New(s)` unless a `%w` verb is present, `fmt/errors.go`). Then
`kErrOk` follows: `*errorString`'s method set is `{Error}` (no `Code`, `GRPCStatus`, `Status`,
`Format`), a comparable pointer, and `errors.AsLeaf.spec` (exists) gives `As` false. The watcher's
two are `parseEvent`'s (`%q %d %s`) and `syncPaginated`'s (no verb). Go check: `reflect.TypeOf` of
both is `*errors.errorString`.

**E4. `GetCurrentResourceVersion`'s error is the client's** (a proved spec strengthened): its error
arm is a bare `err ≠ nil`. Candidate: the error is the client `Get`'s (`clientErr err ∗ statusErrOk
err`), as the proof already has it inside. `startWatching` sends it when `initialRev > 0 ∧
forceInitialEvents` (through `getStartWatchResourceVersion` in `Watch`, before the goroutines: then
it is `Watch`'s error, not `sendError`'s; check in step 5 which path reaches `sendError`).

**E5. `interpretListError(err, true, k, p)`** (a new proved spec; translated): the `paging = true`
branch calls `handleCompactedErrorForPaging` (`storage.EncodeContinue`, `utilruntime.HandleError`,
`NewResourceExpired`, a write of `ListMeta.Continue`) for `ErrCompacted`, else returns `err`.
Candidate post: `err' = err` (when `err ≠ ErrCompacted`) or a `*StatusError` held with a `Failure`
status (`NewResourceExpired`). Needs specs of `EncodeContinue` (translated? check) and `HandleError`
(names only: a no-op text, trusted, if reached).

**E6. `storage.NewTooLargeResourceVersionError`** (a spec of a translated function, or a text if
not translated): reached only by `validateMinimumResourceVersion`'s callers, not by the watcher's
`sendError` under 7f-5a's premises (the watch path has no minimum RV check); listed because §5 did.
Candidate post: `tooLargeErrIs err` with a `Failure` status (`NewTimeoutError` is translated).
Drop it if step 5 confirms it unreachable.

### 11.1 The review of E1-E6 and 81's decisions (2026-11-15)

Review: `/shared/tmp/claude-0/-shared-etcd-grove/c04a65b0-a272-4ae4-94c7-91aa4a20ea30/tasks/ae2c182bd754ca744.output`
(final report). E1 refuted as written (`{{True}} Code #s` over any `Loc`: `*s = *status.New(...)` races
with the read); E2 fine with two gaps; E3, E4, E5 fixed; E6 reachable (`watcher.go:462-464`). The
review also exposed a latent assumption of two existing axioms, `status.FromError` and `status.Code`
(`notes/axiom-review/grpc-status-immutability.md`), folded into E1's package below. Proved-spec changes
(E2, E4, E5) are made with ledger entries; trusted texts (E1's package, E3) are drafted here, one package
for 81's review, not applied; step 5 takes them as `-- pending E1`/`-- pending E3` hypotheses.

### 11.2 The E1 package (DRAFT, trusted text; not applied)

**New opaque vocabulary** (in `Proof/go_etcd_io/etcd/cache/v3/Base.lean`, beside `statusCode`):
`grpcStatusRO (s : Loc) (c : w32) : IProp GF`, persistent: "`s` is a `*Status` nobody writes, whose
code is `c`". Opaque because grpc's `Status` is an axiomatized type (no points-to can be stated).

**(a) `grpcErrMethodsOk`'s `GRPCStatus` conjunct** gains the returned status's facts:
```
(⌜methodSet e.ty !! "GRPCStatus" = some (Signature [] false [*internal/status.Status])⌝ →
  ∃ s : Loc, (□ ∀ Φ, ▷ Φ #s -∗ WP (methods e.ty "GRPCStatus" e.v) #() {{ Φ }}) ∗
    grpcStatusRO s (statusCode (GoInterface.ok e)))
```
Docstring (`Base.lean:325`) corrected: grpc's `*Status` is not immutable in Go (a whole-struct
assignment `*s = *t` from any package copies its unexported fields); the fact is a guarantee of the
producer that built `s` fresh and never handed out a way to write it.

**(b) The `Status` methods over `grpcStatusRO`** (replaces E1; an axiom in
`Proof/google_golang_org/grpc/status/StatusRO.lean`):
`∀ s c, {{ grpcStatusRO s c }} (s @!! *Status @!! "Code") #() {{ RET #c; True }}` (Go:
`if s == nil || s.s == nil { return codes.OK }; return codes.Code(s.s.Code)`: a read of a status
nobody writes; for `s = nil` the producer states `c = OK`). `Proto()`, `Message()` as needed by
(c) only (not exported unless a proof needs them).

**(c) `status.FromError.spec` and `status.Code.spec`**: statements unchanged (they take `statusErrOk
err`, which now carries `grpcStatusRO s (statusCode e)` for an error with `GRPCStatus`); the
docstrings say that `FromError`/`Code` read the returned `*s` through `Proto()`/`Code()`, justified by
`grpcStatusRO`, and the pointer added today to the axiom-review note goes away.

**(d) The producers that build a status fresh** (each trusted text whose post gives `statusErrOk` of
an error with a `GRPCStatus` method now also promises `grpcStatusRO` of its status, through (a); no
statement changes, the meaning of `statusErrOk` does):
- `status.Error.spec`, `status.Errorf.spec` (`Proof/google_golang_org/grpc/status/Error.lean`,
  `Errorf.lean`): `&Error{s: New(c, msg)}`, `s` fresh, `*Error.GRPCStatus` returns `e.s` (never
  written after); the code is `c`, so the post may also say `statusCode err = c` (optional).
- grpc's invoker and stream texts (`Proof/google_golang_org/grpc/InvGrpc.lean`: `grpcInvokerOk`'s
  attempt error, `grpcDecOk` (`toRPCErr`'s `*status.Error`), `ctxErrsErr` (context errors: no
  `GRPCStatus`, unaffected); `InvGrpcStream.lean`: `cliStreamErr`, the `RecvMsg`/`SendMsg`/`Send`
  error arms at lines 434, 477, 543): grpc builds each `*status.Error` with `status.New`/`Err()` or
  `FromContextError`, fresh per error; `io.EOF`, `io.ErrUnexpectedEOF` have no `GRPCStatus`.
- rpctypes' and v3rpc's package-initializer axioms for the `ErrGRPC*` values
  (`Proof/go_etcd_io/etcd/api/v3/v3rpc/rpctypes/Init.lean`, `.../etcdserver/api/v3rpc/Init.lean`):
  `status.Error(...)` at init, never written.
**Go evidence (written 2026-11-15, sixteenth agent): `examples/premisefix/grpcstatusro/`** (main examples
module, the etcd fork at the etcd pin, grpc v1.84.0; `GOWORK=off GOTOOLCHAIN=go1.27.3 go test -race`, 32G
cap, all pass, `/shared/tmp/k8s7f5a-p3/e1.log`):
- `nowrite_test.go` (static): type-checks from source every non-standard package depending on
  `internal/status` in the closures of etcd's client, `etcdserver`, `v3rpc`, `rpctypes` and `cache` (37
  packages) and of `k8s.io/apiserver/pkg/storage/etcd3` (11 k8s packages, the watcherctx module), and finds
  no write to a `Status`, its `*spb.Status`, or an `Error`'s `*Status`: no assignment, `++`, range
  assignment or `&` reaching the field `s`, no whole-struct write `*p = *q` of a `Status`/`Error`, no `&`
  of an existing one, no `unsafe.Pointer` of one; the field `s` read only inside `internal/status`, in
  `Code`, `Message`, `Proto` (clone), `Details`, `Error.Is` (`proto.Equal`), `RawStatusProto`,
  `Error.Error`, `Error.GRPCStatus`; `RawStatusProto` called only twice, in the server's
  `http2_server.go` (`writeEarlyAbort`, `writeStatus`), its result used only as `p.GetDetails()`,
  `proto.Marshal(p)`, `pretty.ToJSON(p)`. `TestScannerDetects` is the negative control (a whole-struct
  write, `&*s`, `unsafe.Pointer(s)` are reported). Not covered statically: generic code over a `*T`,
  reflection (the race test below observes the running code).
- `TestStatusErrorProducers`: `status.Error`/`Errorf`/`New(c, m).Err()` for every code: `nil` for OK,
  else a `*status.Error` whose `GRPCStatus()` is one pointer, fresh per call, `Code() = c`, `Message() =
  m`, unchanged after every read API (`FromError` (which returns the same pointer), `Code`, `Convert`, a
  mutated `Proto()` clone, `Details`, `WithDetails`, `errors.Is`, `Error`, `rpctypes.Error`/`ErrorDesc`).
  `TestNilStatusCode`: a nil `*Status`'s `Code()` is OK.
- `TestErrGRPCInitializers`: rpctypes' `error.go` parsed: each of its 63 `ErrGRPC*` initializers is
  `status.Error(codes.X, "lit")` (one more variable is an alias), the test's explicit list is the file's,
  each status has that code and message, pairwise distinct pointers; the 57 values of `errStringToError`
  are those variables; the 53 values of v3rpc's `toGRPCErrorMap` are those variables or
  `ErrMemberNotEnoughStarted`/`ErrTooManyRequests` (EtcdErrors, no `GRPCStatus`).
- `TestInvokerAndStreamErrors` (under `-race`): a real grpc server on `bufconn`; the errors of
  `ClientConn.Invoke` and of a client stream's `RecvMsg`/`SendMsg` for every code, with details, for the
  server's shared `ErrGRPC*` values, a cancelled/expired context (before and during the call), a closed
  connection (`ErrClientConnClosing`, grpc's package-level `status.Error`, shared and never written) and
  a stopped server (115 errors per run): `GRPCStatus()` fixed, `Code()` the expected code, read by four
  goroutines concurrently (~35000 reads) while grpc runs and shuts down, with no race reported and the
  codes unchanged at the end; `io.EOF` has no `GRPCStatus`.
- `TestWholeStructWriteChangesCode`, the negative (the reviewer's point, sequential form of `TestE1Race`):
  `*s = *status.New(...)` through the `GRPCStatus()` pointer changes `status.Code(err)`.

**(e) What `kErrOk` then gets**: its `grpcError` conjunct (`s.Code()` returns) follows from (a) and
(b) for any `statusErrOk` error; E1 as a separate text disappears.

### 11.3 The E3 text (DRAFT, trusted; not applied)

`fmt.Errorf.spec` gains, in its post: when `fmt.fmtDirectives format = some ds ∧ ∀ d ∈ ds, d.verb ≠
'w'`, the result is `interface.mkOk (*errors.errorString) #p` for a fresh `p` (keeping
`stringMethodSpec`). Go: `errorf` wraps whenever a directive's verb is `w`, including `%[1]w`, `%+w`,
`%-5w`, even for a non-error argument (`fmt/print.go:1052,1146`; the reviewer's run gives
`*fmt.wrapError` for all three), and otherwise returns `errors.New(s)` (`fmt/errors.go`; `Errorf` also
returns `errors.New(format)` when there is no argument and no `%`). (`%[1]w` is refused by
`fmtDirectives` (`none`, an argument index), so the text claims nothing of it; `%+w`, `%-5w` parse as `w`
directives and are excluded.) A `%w` with no argument left does not wrap (`missingArg` comes first,
`print.go:1142-1146`): the premise is conservative there.

**Go evidence (written 2026-11-15, sixteenth agent): `examples/premisefix/errorfwrap/`** (go1.27.3, all
pass, `/shared/tmp/k8s7f5a-p3/e3.log`): `TestWatcherFormats` (parseEvent's `event.go:69`, syncPaginated's
`watcher.go:354`, GetCurrentResourceVersion's `store.go:742`: `*errors.errorString`, fresh per call, and
`fmtDirectives` of each has no `w`); `TestWVerbFormsWrap` (`%w`, `%[1]w`, `%+w`, `%-5w`, `%#w`, `% w`,
`%05.2w`, `%w` of an int, two `%w`, `%[2]w`: a wrap with `Unwrap`); `TestMissingArgNoWrap`;
`TestDirectivesPortExamples` (a Go transcription of `fmt.fmtDirectivesAux` gives the Lean file's 13
examples); `TestNoWDirectiveGivesErrorString` (200000 random formats over verbs, flags, digits, `.`, `*`,
`[`, `]`, `%`, `w`, a multi-byte rune and invalid UTF-8, 0-3 arguments of mixed types: all 117672 with
`some ds` and no `w` give `*errors.errorString`; 39685 of the 54107 with a `w` directive wrap).

### 11.4 E2, E4, E5, E6 (proved specs)

- E2: `WatchResponse.Err()`'s post gives `clientErr err ∗ statusErrOk err` of a non-nil result (four
  cases: `v3rpc.Error(closeErr)`, `ErrCompacted`, `v3rpc.Error(status.Error(FailedPrecondition,
  reason))`, `ErrFutureRev`). Gaps to find or derive: `eofIs e → clientErr e`; `isLeafError` of a
  `*status.Error` (method-set fact).
- E4: `GetCurrentResourceVersion`'s error arm: `(clientErr err ∗ statusErrOk err) ∨` the E3 form (its
  own `fmt.Errorf("the current resource version must be greater than 0")`); reachable from `sendError`
  (`watcher.go:456-460`).
- E5: `interpretListError.spec` generalized over `paging` (one triple); the caller shows `encOkL`.
- E6: the existing `NewTooLargeResourceVersionError` spec (`tooLargeErrIs`); `kErrOk` proved from it.

### 11.5 T5-f's `Event_EventType.String` over the pointer receiver (DRAFT, trusted; not applied)

Decided by the user (2026-11-15, via etcd-grove-81): step 7 does not wait for the parked goose change
(`ptr_M_unfold` for an axiomatized value method, `notes/perennial-changes.md`); T5-f's axiom is restated
over the pointer receiver, the form `parseEvent.wp_proof` already takes as a callee hypothesis
(`Spec/go_etcd_io/etcd/api/v3/mvccpb/Event_EventType__StringPtr.lean`):

```
mvccpb.Event_EventType.StringPtr.spec : Prop :=
  ∀ (l : Loc) (t : w32),
  {{ isPkgInit mvccpb ∗ l ↦□ t }}
    (l @!! PointerType Event_EventType.ty @!! "String") #()
  {{ (s : GoString), RET #s; True }}
```

The change: the axiom `mvccpb.Event_EventType.StringPtr.wp_proof` in a new
`Proof/go_etcd_io/etcd/api/v3/mvccpb/Event_EventType__StringPtr.lean`, with the header's "no proof derives
this yet" replaced by the trust statement below; the value axiom `Event_EventType.String.wp_proof` (T5-f)
is removed if nothing else uses it (today only the Draft's statement mentions it; to check at step 7), so
the trust base trades one axiom for one. Why it is faithful: `String` is a value method (`kv.pb.go:50`);
the method set of `*Event_EventType` contains it by Go's method-set rule ("the method set of a pointer to
a defined type T is the set of all methods declared with receiver *T or T"), as the compiler's wrapper
that reads `*l` and calls the value method: so the call reads the value at `l` (the read-only
points-to), writes nothing, and returns what the value method returns, some string for every value
(T5-f's claim, `TestEventTypeStringReturns`); a nil `l` panics, which `l ↦□ t` excludes. When the goose
change lands, the pointer form becomes a theorem of the value axiom and this axiom goes.

**Go evidence: `examples/premisefix/eventtypestr/`** (`-race`, go1.27.3, all pass,
`/shared/tmp/k8s7f5a-p3/t5f.log`): `TestPtrStringIsValueString` (named, unknown, negative and extreme
values: `p.String()`, through a `fmt.Stringer` holding `p`, a method value, the method expression
`(*Event_EventType).String(p)`, and `(&e.Type).String()` on a `*mvccpb.Event` (parseEvent's shape) all
equal `t.String()`, the value unchanged); `TestPtrStringReadsOnly` (8 goroutines calling `String` through
one pointer while others read `*p`, no race reported); `TestPtrStringNil` (a nil pointer panics).
