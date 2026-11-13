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
| `ctxRL` | the client's `KV.Get` path (grpc's metadata keys, `Done`, `Err`), through `getCurrentStorageRV(ctxRL)` (added by the S1 review) | `getStartWatchResourceVersion`, `watcher.go:146,193-209`: with RV 0, `WatchList` on and `SendInitialEvents` false, before `createWatchChan`; `getCurrentStorageRV` is `store.GetCurrentResourceVersion` (`store.go:240`), whose `Kubernetes.Get` runs on `ctxRL` (`store.go:735`) | `ctxOk ∗ ctxErrClient` of the premise of `GetCurrentResourceVersion.spec`, over `ctxRL`: `WithRequireLeader`'s `WithValue` keeps every other key (T5-a) |
| `wc.ctx` | `Done()` | `run` `:282`, `serialProcessEvents` `:571`, `sendError` `:806`, `sendEvent` `:822`, `queueEvent` `:832` (7f-5b: `:615-647`) | `isContext` of the `WithCancel` child (Perennial `wp_WithCancel_any`) |
| `wc.ctx` | the client's `KV.Get` path: grpc's metadata keys, `Done`, `Err` | `getCurrentStorageRV` `:457` (via `store.GetCurrentResourceVersion`), `syncPaginated` `:347` | `ctxOk ∗ ctxErrClient` (premise of `GetCurrentResourceVersion.spec` and of the client's `Get`), over the child: `WithCancel` keeps `Values` |
| `wc.ctx` | the client's `Watch`: `Value(mdOutgoingKey{})` (`streamKeyFromCtx`, `watch.go:1102`), `Value(&cancelCtxKey)` (`WithCancel(&valCtx{ctx})`), `Done`, `Err` | `startWatching` `:493` | `watchCtx` (`examples/premisefix/watchctx`: the client's path reads no other key) |
| `wc.ctx` | none (the driver's identity transformer) | `TransformFromStorage` `:843,858` | `transformerOk` takes any context (a KMS transformer is out of scope, as in 7e) |
| any | `context.Cause` | none on the path (grep of the watcher, `event.go`, `errors.go`, `block_logger.go`, the client's `watch.go`/`ctx.go`) | - |
| errors | `Code()`, `GRPCStatus()`, `Error()`, `errors.As` targets | `isCancelError` `:253-267`, `logWatchChannelErr` `:428-437`, `interpretWatchError` (`errors.go:31-50`), `transformIfCorruptObjectError` `:881-891` | the client's errors (`clientErrTys`, 7e-1), `S.trErr`, `errStrOk`. Each method's spec on each type is the Draft's (S3) item list; none is a context read |

**The control** (`TestWatchStrictControl`): the store's `Watch` under a context that answers the
covered keys and panics at every other key does not panic, and the client's `Watch` receives the
caller's outgoing metadata plus `hasleader`. It covers only a positive resource version, with a fake
watcher (no real member): not the RV-0 paths, `getCurrentStorageRV(ctxRL)` above nor the initial
list (`sync`), which reach the client's `Get`, whose reads the 7e and context-sweep evidence covers.
The S1 review's test over a real member records, on those paths, the keys the store and the
client read of the caller's context, for RV 0 with and without `SendInitialEvents` and RV > 0
(`/shared/tmp/coord-81/k8s7f5-review/clientkeys/keys_test.go`, `TestKeys`; to be moved into
`examples/premisefix/watcherctx` with 7f-5a's Draft, which states the watch's context premise).

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
  - `TestWithRequireLeaderCause` (S1 review): a parent cancelled by `WithCancelCause` with its own
    cause, and a `WithDeadlineCause` parent that expires: the child's `Err` and `Cause` are the
    parent's;
  - `TestWithRequireLeaderNoAlias`: the parent's `MD`, whose `hasleader` exists with another value,
    is not written, nor through the child's value slices. The Copy is not what makes it hold at the
    pin (`FromOutgoingContext` returns a fresh map with copied slices, grpc `metadata.go:342-348`):
    `TestWithRequireLeaderNoAliasWithoutCopy` passes too, and `TestWithRequireLeaderNoAliasDetects`
    shows the check catches an aliasing writer.
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

*Superseded by the S1 review (below):* the check is now `etc/featuregate-check.py`, in `etc/gates.sh`,
with `ResetFeatureValueToDefault`, `AddDependencies`, `AddFlag`, `SetWithLogger` and `AddFeatureGates`
added to the grep, the DaemonSet program's closure included (as an outside program), and each hit's
verdict in `etc/featuregate-allow.txt` (66 hits: 57 inert, 2 driver, 7 outside). The order (each
`Set` before any `Enabled` of its feature) is still this section's manual check.

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

## S1 review (2026-11-13, etcd-grove-81's axiom review; decisions in `questions.md`)

Review journal: `/root/.claude-csail/projects/-shared-etcd-grove/c04a65b0-a272-4ae4-94c7-91aa4a20ea30/subagents/workflows/wf_115e23d1-72c/journal.jsonl`;
the reviewers' Go tests: `/shared/tmp/coord-81/k8s7f5-review/`. No BLOCKER; one MAJOR; minors.

| Finding | Disposition |
| --- | --- |
| **MAJOR, T5-c:** `featureOn g s` and `featureOff g s` of one feature both obtainable (a `Set(s=true)` and a `Set(s=false)`), the "one `Set` per feature" assumption load-bearing | **Fixed in the trusted text.** The `Set` triple is for one value per feature, from the table `k8sSetValue` (new trusted definition: `WatchList ↦ some true`, every other queried feature `↦ some false`, else `none`): `∀ s v Φ, ⌜k8sSetValue s = some v⌝ → … featureSet g s v … Set(setArg s v)` (was `∀ s b Φ, ⌜s ∈ k8sQueriedFeatures⌝ → … featureSet g s b … Set(setArg s b)`). `featureOn` and `featureOff` of one feature are unreachable by construction. Callers: `noStreaming`, `watchList` (the side condition is the table lookup) |
| T5-c: the assumption to say only "no other mutator runs"; drop "before any Enabled" if no triple needs it | Restated: **no code mutates the gate but `Set`s of the table's values (repeats harmless), each before any `Enabled` of its feature.** The order clause **stays**: `Enabled`'s triple hands its caller the wand `featureOff g s -∗ ⌜b = false⌝`, which the caller may keep past a later `Set`; then `b := Enabled(EtcdRangeStream); if Set("EtcdRangeStream=false") == nil && b { panic }` panics in Go (default `true`) and would be provable. Go: scenario `enabled-kept-then-set` (new). The reviewer's minor 5 ("stronger than soundness needs") missed the kept wand. Removing the clause would need `Enabled`'s triple restated (e.g. taking `featureSet` as a premise), a trusted change beyond the decisions: not done |
| T5-c: `ResetFeatureValueToDefault`, `AddDependencies` missing from the mutator lists | Added (Gate.lean header, the grep), with `AddFlag` (flag parsing calls `Set`), `SetWithLogger` and `AddFeatureGates` |
| T5-c: the closure check to cover `dsmain` | Covered, as an **outside** program: its closure is grepped and its hits have verdicts; it does mutate the gate (`setFeatureGates`' `SetFromMap`, `dsmain.go:69`; `k8s.io/kubernetes/pkg/features`' `init`: `AddVersioned`, `AddDependencies`, `ReplaceFeatureGates`, the client adapter's `SetFromMap`), so the assumption is not claimed of it; the check fails if any Lean module of its tree names the gate's specs (`k8sfeature`, `featureGateOk`, `featuresInit`). Today none does (its Lean is `apimodel` only) |
| T5-c: script the check, wire it into the gates (B5 had none) | `etc/featuregate-check.py` (closures by `go list -deps`, allow-list `etc/featuregate-allow.txt` with each hit's class and reason; fails on an unlisted hit, an `outside` hit in an inside program, a stale entry, an outside Lean use), in `etc/gates.sh` (section issues). Covers B5's `Set(EtcdRangeStream=false)` and T5-c's `Set(WatchList=true)` alike. Negative runs: an entry removed, and a driver hit reclassified `outside`, each fail |
| T5-c minor 3: the `Set` error arm's "changes nothing `Enabled` reads" inaccurate | Reworded: a failed `Set` does not store `enabled` (what `Enabled` reads) but stores the raw pair in `enabledRaw` (`feature_gate.go:498-504`), which later `Set`s re-apply: they then fail too (`failed-set`), or, after a dependency failure, may succeed and apply it; neither is excluded, and the pair is of a table value |
| T5-a minor 2: `copyOf` names-only in the dry-run configuration | 7f-3a owns the configuration: recorded in the Scope's T5-a (`notes/k8s-7f5-scope.md` §4.2), applied with 7f-3a's statements |
| T5-a: the Lean can give only "the parent's metadata plus one key" (`strings.ToLower` trusted as some string) | Stated so in the Scope's T5-a and the test file's header |
| T5-a: the Go tests weaker than claimed (trivial `Cause`; NoAlias passes without the `Copy`) | `TestWithRequireLeaderCause` (a `WithCancelCause` cause and a `WithDeadlineCause` expiry). NoAlias strengthened (a parent `hasleader: ["false"]`, the child's slices written); **no test of `WithRequireLeader` can fail without the `Copy`**: `FromOutgoingContext` already returns a fresh map with copied slices (grpc `metadata.go:342-348`). So instead `TestWithRequireLeaderNoAliasWithoutCopy` (a copy of `WithRequireLeader` without it passes: the property the proof needs holds either way) and `TestWithRequireLeaderNoAliasDetects` (the check catches an aliasing writer) |
| S0.1 minor 4: the row `getCurrentStorageRV(ctxRL)` missing; the strict control's reach overstated | Row added (`watcher.go:146,193-209`; `store.go:240,735`); the control's paragraph says it covers only RV > 0 with a fake watcher and cites the reviewer's real-member test `/shared/tmp/coord-81/k8s7f5-review/clientkeys/keys_test.go` |

Docstrings only, no meaning change: `featureOn`/`featureOff` (given for the table's value), the
features `Init`'s doc (`etc/gen-init.py`) and `etcd3/Base.lean`'s `featuresInit` ("`Set` of one to its
`k8sSetValue`").

## Checks (2026-11-13, on `f597058f4a` plus the SpecPlan PkgInit regeneration)

- **Full build:** `etc/timed-build.py` passed (17475 jobs, build `20261113-180549-3823747`, under
  flock and the 64G cap). The first run failed only at the generated
  `SpecPlan/Spec/PkgInit/k8s_io/apiserver/pkg/util/flowcontrol.lean`, because flowcontrol now imports
  `context`. It was regenerated with `etc/gen-specs-pkginit.py`, keeping only that file: the script's
  other differences are older drift on lean, which this branch leaves alone.
- **`etc/tcb-report.py --check`:** one difference, as expected: **NEW axiom
  `k8sfeature.featureOn_persistent`**. The baseline is not updated (it waits for the review).
- **Collections:** every collection matches its baseline except `k8setcd3.txt` (the same NEW
  axiom; it is reached through `watchList`, which `Main*` call). All 55 collections were checked.
- **Generated files and gates:**
  - `etc/gen-init.py --check` (228 up to date, after regeneration: flowcontrol's `Init` imports
    `context`, and the two `PkgTable`s);
  - `etc/gen-link.py --k8setcd3`/`--k8s-etcd3` reproduce;
  - `etc/goose.py --check` passes;
  - `etc/bounds-check.py --check` (330, baseline 330);
  - `etc/issues-status.py --check`;
  - every `etc/api/*.txt` interface `--check --layout` passes (no k8s package has an API list).
- **Go:** `examples/premisefix/watcherctx` (all tests), and in `examples/k8s/etcd3` `TestWatchListOn`,
  `TestNoStreaming` and `TestMainLinearizable`.
- **Closed theorems:** no statement changed. `Main*`'s proofs take one more callee spec
  (`watchList.spec`), linked in `Link.lean`/`MainLinked.lean`.

## Checks after the S1 review (2026-11-13, on `0d873a9ee5`)

- Full build passes (17475 jobs, under flock and the 64G cap).
- `etc/tcb-report.py --check`: the one expected difference, NEW axiom `k8sfeature.featureOn_persistent`;
  baseline updated (869 axioms, 4 sorries). Collections: 54 of 55 match; `k8setcd3.txt` the same NEW
  axiom, updated.
- `etc/featuregate-check.py`: ok (66 hits, 3 closures); its two negative runs fail as they should.
- Go: `examples/premisefix/watcherctx` all pass (new: `enabled-kept-then-set`, `TestWithRequireLeaderCause`,
  `...NoAliasWithoutCopy`, `...NoAliasDetects`).
- The gates: by `etc/land.sh`.
