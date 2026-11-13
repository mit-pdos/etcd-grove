# k8s 7f-5: S0 (enumeration, evidence) and S1 (the trusted package), for etcd-grove-81's axiom review

Branch `k8s-7f5`. The Scope is `notes/k8s-7f5-scope.md`, and its decisions are in §8 there. This
file records S0 (the context enumeration, the Go evidence, the Goose dry run and the driver's
`Set("WatchList=true")`) and S1: the trusted texts, written in Lean and built. **STOP:** nothing
relies on S1's texts until 81's axiom review.

## S0.1 The context enumeration (Scope §4.1, completed)

Pins: apiserver `9c4ec15b8038`, etcd fork `0b50f0426`, go1.27.3. The store's watch runs on two
contexts:
- the caller's `ctx`, which `store.Watch` passes on;
- `ctxRL = WithRequireLeader(ctx)`, which `watcher.Watch` and `createWatchChan` receive;
- and `wc.ctx = WithCancel(ctxRL)` (`watcher.go:180`), which the goroutines use.

Every read, through the callees, by file:line:

| Context | Read | Where | Fact that covers it |
| --- | --- | --- | --- |
| `ctx` | `Value(mdOutgoingKey{})`, then `MD.Copy` of the answer | `WithRequireLeader`, `client/v3/ctx.go:29,34` | `libCtxOk` (grpc's outgoing key: `outgoingCtxOkC`, a `rawMD`) |
| `ctxRL` | `Value(&cancelCtxKey)` (passes to `ctx`), `Done()` | `context.WithCancel`, go1.27.3 `context.go` `propagateCancel`/`parentCancelCtx` | `watchCtx`'s `#HCC`, `Done` (the context sweep); `WithValue` passes the key to `ctx` |
| `ctxRL` | **`Value(priorityAndFairnessInitializationSignalKey)`, then `Signal()` on a non-nil `InitializationSignal`** | `WatchInitialized`, `watcher.go:158`; `apf_context.go:43,50-51` | **nothing before 7f-5: T5-b** |
| `wc.ctx` | `Done()` | `run` `:282`, `serialProcessEvents` `:571`, `sendError` `:806`, `sendEvent` `:822`, `queueEvent` `:832` (7f-5b: `:615-647`) | `isContext` of the `WithCancel` child (Perennial `wp_WithCancel_any`) |
| `wc.ctx` | the client's `KV.Get` path: grpc's metadata keys, `Done`, `Err` | `getCurrentStorageRV` `:457` (via `store.GetCurrentResourceVersion`), `syncPaginated` `:347` | `ctxOk ∗ ctxErrClient` (premise of `GetCurrentResourceVersion.spec` and of the client's `Get`), over the child: `WithCancel` keeps `Values` |
| `wc.ctx` | the client's `Watch`: `Value(mdOutgoingKey{})` (`streamKeyFromCtx`, `watch.go:1102`), `Value(&cancelCtxKey)` (`WithCancel(&valCtx{ctx})`), `Done`, `Err` | `startWatching` `:493` | `watchCtx` (`examples/premisefix/watchctx`: the client's path reads no other key) |
| `wc.ctx` | none (the driver's identity transformer) | `TransformFromStorage` `:843,858` | `transformerOk` takes any context (a KMS transformer is out of scope, as in 7e) |
| any | `context.Cause` | none on the path (grep of the watcher, `event.go`, `errors.go`, `block_logger.go`, the client's `watch.go`/`ctx.go`) | - |
| errors | `Code()`, `GRPCStatus()`, `Error()`, `errors.As` targets | `isCancelError` `:253-267`, `logWatchChannelErr` `:428-437`, `interpretWatchError` (`errors.go:31-50`), `transformIfCorruptObjectError` `:881-891` | the client's errors (`clientErrTys`, 7e-1), `S.trErr`, `errStrOk`. Each method's spec on each type is the Draft's (S3) item list; none is a context read |

**The control** (`TestWatchStrictControl`): the store's `Watch` under a context that answers the
covered keys and panics at every other key does not panic, and the client's `Watch` receives the
caller's outgoing metadata plus `hasleader`. That test exercises the store's own path to the
client's `Watch` with a positive resource version. The initial-list path (`sync`) reaches the
client's `Get`, whose reads the 7e and context-sweep evidence covers.

## S0.2 The Go evidence (`examples/premisefix/watcherctx`, all passing)

Run: `cd examples/premisefix/watcherctx && GOWORK=off GOTOOLCHAIN=go1.27.3 go test -count=1 -v .`
(under `systemd-run --scope -p MemoryMax=32G`).

- **T5-b:**
  - `TestWatchInitializedKeyPanics`: `store.Watch` panics under a context panicking only at the APF
    key;
  - `TestWatchInitializedForeignSignal`: a foreign signal whose `Signal` panics makes it panic;
  - `TestWatchInitializedRealSignal`: APF's own signal is signalled, no panic. This is outside the
    narrow text (Q3);
  - `TestWatchStrictControl` (§S0.1);
  - `TestTracingStartKeepsAPFKey`: `tracing.Start`'s returned context asks its parent at the key,
    with the execution tracer on and off. This supports the stronger post of `tracing.Start.wp_proof`.
- **T5-a** (translated, Q2; for 7f-3a):
  - `TestWithRequireLeaderValues`: other keys, `Done`, `Deadline`, `Err` and `Cause` are the
    parent's, and the metadata is the parent's plus `hasleader`;
  - `TestWithRequireLeaderNoAlias`: the parent's `MD` is not written.
- **T5-c** (each scenario in its own process): `TestGateScenarios`:
  - `watchlist-true`: 800 concurrent `Enabled` calls return true after `Set("WatchList=true")`;
  - `two-features`: `Set(EtcdRangeStream=false)` then `Set(WatchList=true)`, and both values hold;
  - `true-then-false` and `enabled-then-set`: what the restated assumption excludes, shown to change
    `Enabled`;
  - `failed-set`: a locked feature's `Set` errs and changes nothing; the later `Set` errs too (a
    poisoned `enabledRaw`).
- **T5-c on the real driver:** `examples/k8s/etcd3`'s `TestWatchListOn` (`noStreaming()` then
  `watchList()`: `WatchList` on, `EtcdRangeStream` off). `TestNoStreaming` and
  `TestMainLinearizable` still pass.
- **T5-d:** `TestJitter`: `Jitter(1s, 3)` is in `[1s, 4s]`.

## S0.3 The Goose dry run

With every configuration change 7f-3/7f-5a will need (saved as
`/shared/tmp/k8s7f5/goose-dry-full.patch`):
- client/v3: `WithPrevKV`, `WithRequireLeader`;
- grpc `metadata`: `NewOutgoingContext`, `Pairs`, `MD.Copy`, `MD.Set`, `mdOutgoingKey`, `rawMD`;
- flowcontrol: `WatchInitialized`, `initializationSignalFrom`, the key;
- etcd3: the G1 exclusions dropped;
- runtime: `Decode`.

`etc/goose.py --project etcd --project k8s-apiserver` succeeds. A targeted build of the changed
`Code`/`GeneratedProof` modules elaborates (1m23s). `mvccpb`'s `Event.IsCreate` is already
translated.

**Kept in S1:** only flowcontrol's three names, which T5-b's key needs (the key is now `#(W64 0)`,
not an axiom), and the driver's `watchList`.

**Reverted, for their stages:**
- client/metadata: 7f-3a, since they rebuild the whole etcd client;
- etcd3 and runtime: 7f-5a-P.

`wait.Jitter` is not named by the current translation (its first caller is `startWatching`), so
T5-d's Lean waits for 7f-5a-P. Its text is below.

## S0.4 The no-other-mutator check, rerun (2026-11-13)

Method: as `b5-r1.md`. The compiled closure of `examples/k8s/etcd3` and `examples/k8s/compactor`
(4482 Go files, `/shared/tmp/k8s7f5/k8s-gofiles.txt`) is grepped for every feature-gate mutator
(hits: `/shared/tmp/k8s7f5/k8s-mutator-hits.txt`). Every hit is B5's (definitions, `features`'
registration in `init`, etcd's own gate, client-go's uncalled helpers, doc comments), plus the
driver's two calls:
- `k8setcd3.go:1689` `Set("EtcdRangeStream=false")`;
- `k8setcd3.go:1697` `Set("WatchList=true")`.

Both run once per process run, in `Main`/`MainCluster`/`MainPartition`
(`!ok || !noStreaming() || !watchList()`), before `etcd3.New` and so before any `Enabled` of either
feature. Nothing calls `Enabled(EtcdRangeStream)` or `Enabled(WatchList)` before them: the store
does it only from `GetList`/`Watch`. One `Set` per feature, before any `Enabled`: **the restated
assumption holds of the closure.** The driver's tests call `noStreaming`/`watchList` again in one
process, but they are not the verified `Main*`.

## S1 The trusted package (written in Lean; built: see "Checks")

### T5-b. The APF initialization-signal key in `k8sctx.k8sCtxOk`

- **Text** (`Proof/k8s_io/apiserver/pkg/audit/CtxKeys.lean`):
  - `flowcontrol.initSignalKeyAny := interface.mkOk priorityAndFairnessKeyType.ty
    priorityAndFairnessInitializationSignalKey` (translated: `#(W64 0)`);
  - `flowcontrol.initSignalRes v := v = nil ∨ ∀ vi, v = ok vi →
    go.typeSetContains vi.ty InitializationSignal.ty = false`, so that `TypeAssert2` fails and
    `WatchInitialized` calls nothing;
  - `k8sCtxOk` gains `context.valueAt ctx flowcontrol.initSignalKeyAny flowcontrol.initSignalRes`, as
    its fourth fact, before `libCtxOk`; `k8sKeys` gains the key.
- **Not trusted by itself:** a definition used as a premise. The producers are proved:
  - `k8sCtxOk_of_nil` (nil satisfies `initSignalRes`);
  - `k8sKeys_notIntPtr` (the key's type is not `*int`);
  - hence `_background`, `_todo`, `_bgFrom` and `_of_ctxValueNil`.
- **Trusted consequence:** `tracing.Start.wp_proof` (an axiom) has `k8sCtxOk ci'` in its post, so it
  now also claims that the returned context's APF key satisfies `initSignalRes`. That is true:
  - `Start` reads nothing there;
  - the returned context asks its parent;
  - the premise `k8sCtxOk ci` gives the parent's answer.

  Docstring added; evidence `TestTracingStartKeepsAPFKey`. No other axiom mentions `k8sCtxOk`.
- **Review points:**
  1. **Is the narrow `initSignalRes` (Q3) the right text?** It excludes APF's own signal, which
     kube-apiserver stores for a watch that bypasses the cache.
  2. **Is `typeSetContains … = false` the exact condition under which Go's assertion fails?** It is
     the same function Perennial's `type_assert2_interface_step` uses.
  3. **Is any other reader of the key reachable from `k8sCtxOk`'s users?** None found:
     `WatchInitialized` and APF's filter are the only readers in apiserver.

### T5-c. `featureOn` and `Set(s=true)` (Gate.lean), with the restated assumption

- **Text** (`Proof/k8s_io/apiserver/pkg/util/feature/Gate.lean`, all TRUSTED):
  - new opaque `featureOn g s` (persistent, axiom `featureOn_persistent`);
  - `featureSet g s b := if b then featureOn g s else featureOff g s`;
  - `setArg s b := s ++ (if b then "=true" else "=false")`;
  - in `featureGateOk g`:
    - the `Enabled` triple's continuation takes
      `(featureOff g s -∗ ⌜b = false⌝) ∧ (featureOn g s -∗ ⌜b = true⌝)`;
    - the `Set` triple is for `setArg s b`, with the post
      `err = nil ∗ featureSet g s b ∨ err ≠ nil`;
  - the header's environment assumption is restated: at most one `Set(s=b)` per feature, before
    any `Enabled(s)`, and nothing else changes the set values.
- **Why each is true in Go:** see S0.2:
  - `Set("WatchList=true")` stores `enabled[WatchList] = true` when it returns nil, and later
    `Enabled` returns it;
  - a later `Set` of another feature re-applies the earlier pairs;
  - an erring `Set` stores nothing `Enabled` reads.
- **Where the assumption is load-bearing, stated in the header with the Go scenarios:** `featureOn`
  and `featureOff` of one `s` are not exclusive in Lean. A program making `Set(s=true)` and then
  `Set(s=false)` would get both, and the `featureOn` law would then claim `Enabled = true` where Go
  answers false. The assumption excludes that program, and S0.4 checks the closure. This is the same
  shape as B5's original assumption.
  - An alternative without the assumption: `Set` consumes a per-feature exclusive token from
    `features`' `init`. It needs `featuresInit` to hand out non-persistent tokens, which an
    `isPkgInit` fact cannot. Not done; for the review to weigh.
- **Users changed** (proofs only):
  - `shouldStream` (`icases Hb with ⟨Hb, -⟩`, twice);
  - `noStreaming` (`setArg … false`, `featureSet` unfolded);
  - the others drop the continuation's hypothesis.
- **Producer of the new fact:** the driver's `watchList` (new):
  - spec `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/watchList.lean`
    (`if b then watchListOn`);
  - proof `Proof/.../examples/k8s/etcd3/watchList.lean`;
  - `watchListOn` in `Proof/k8s_io/apiserver/pkg/storage/etcd3/ListDefs.lean`, beside
    `rangeStreamOff`;
  - `Main`/`MainCluster`/`MainPartition` call it, and their proofs discard the fact until 7f-6;
  - the driver's `Link.lean` (regenerated, `etc/link-lean-first-k8setcd3.txt`) and `MainLinked.lean`
    pass `wp_watchList`.
  - The closed theorems' statements are unchanged: `Main*`'s outcome when a `Set` fails is the same
    "no check" arm.

### T5-d. `wait.Jitter(d, f)` returns some duration (text only; its Lean waits for 7f-5a-P)

- **Proposed** (`Spec/k8s_io/apimachinery/pkg/util/wait/Jitter.lean`, an axiom `Jitter.wp_proof`):
  for any `d : w64` and any float value `f`, `Jitter(d, f)` returns some `j : w64`, with no
  premise.
- Go: `wait.go:92-98`, `duration + time.Duration(jitterRand()*maxFactor*float64(duration))`. The
  float-to-int conversion is arbitrary in Perennial's model (`Float64Semantics`) and in Go
  (implementation-defined out of range), and it never panics.
- Evidence: `TestJitter`. It is reached only on the too-large-RV error path (`watcher.go:463`).

### Not trusted

- T5-a (translation; 7f-3a);
- flowcontrol's `WatchInitialized`/`initializationSignalFrom` (translated; their spec is 7f-5a-P's
  first leaf).

## Checks

(filled in after the build: see the handoff)
