# Translating client-go's leaf libraries with Goose (survey, 2026-10-26)

Goal: the Goose translation of the client-go libraries the DaemonSet controller uses and that are
verified directly (D49, `notes/k8s-daemonset-plan.md`, "The cut": the leaf libraries), set up for
later agents to specify and verify. No specs or proofs here. Perennial and the pinned translator
are unchanged; the gaps below are worked around in this repository's Goose configuration, and the
general fixes are for independent Perennial branches (`notes/perennial-changes.md`). The series
continues the etcd3 survey's G1-G4 (`notes/k8s-etcd3-goose.md`) as C1, C2, ....

## Setup

- Project `k8s-apiserver` of `etc/goose.py` (examples/k8setcd3's Go module), which already owned
  `Code/k8s_io/client_go` and pins client-go at `v0.0.0-20261021054439-569675c57fa3` through
  `examples/k8setcd3/go.mod` (its `util/consistency` is byte-identical to kubernetes/kubernetes#139657's
  head `13ecb9cc`). All the packages below resolve in that module as they are (`k8s.io/api`,
  `golang.org/x/time` are already in its `go.mod`): no `go.mod` change, and no reason to split the
  project (a second project would have to translate `tools/cache` and apimachinery again, under
  another root, since the KEP-6404 watch cache names them).
- New in the project: the packages below, plus `github.com/go-logr=` (logr), and the etcd
  project's names-only `golang.org/x/time/rate` and `container/heap` through their lean roots
  (`golang.org/x/time=`, `container/heap=`; translated by the etcd project, not here). Owned now
  also: `k8s_io/api`, `k8s_io/utils/trace`, `github_com/go_logr`.
- Result: `etc/goose.py --check` passes (with `GOTOOLCHAIN=go1.27.1`, CI's; under go1.27.3 the
  etcd project's `net/http` differs, unrelated); `etc/gen-init.py --check` passes; the full
  `lake build` passes (9394 jobs). `etc/tcb-report.py --check`: one new axiom,
  `github_com.go_logr.logr.opaqueInitsOk` (klog imports logr now, so the init chain of k8setcd3's
  closed theorem runs logr's untranslated initializers): `etc/tcb-baseline.txt` and
  `etc/tcb-collections/k8setcd3.txt` updated; every other collection matches.
- Package initialization: `etc/gen-init.py`'s `ROOTS` gain `workqueue`, `consistency`, `retry`,
  `listers/{apps,core}/v1` (their `Proof/**/Init.lean` are generated). Their packages' `IsPkgInit`
  instances (all `True`) are in `Proof/k8s_io/client_go/Base.lean`; those `tools/cache` now needs
  (`features`, `sets`, `utils/trace`, `util/naming`, `util/version`) in the watch cache's
  `Proof/k8s_io/apiserver/pkg/storage/cacher/Base.lean` (where the cache's own is), and logr's
  (klog imports it now) in `Proof/k8s_io/apiserver/pkg/storage/etcd3/Base.lean`. `flowcontrol` has
  no instance yet: it imports `math/rand`, whose instance is in the gRPC server's
  `v3rpc/Base.lean`; moving it to a module of its own rebuilds the server's proofs, so it waits for
  a proof that needs `flowcontrol`'s initialization.

## Per package

| Package | Bodies | Names only (why) |
|---|---|---|
| `util/workqueue` | everything: `Typed[T]` (`Add`, `Get`, `Done`, `ShutDown*`, the unfinished-work loop), `delayingType[T]` (`AddAfter`, `waitingLoop`, the `waitForPriorityQueue` heap methods, `insert`), `rateLimitingType[T]`, `NewTypedRateLimitingQueueWithConfig`, all rate limiters (`DefaultTypedControllerRateLimiter`, item-exponential, bucket, fast-slow, max-of, with-max-wait), the metrics providers (no-op by default), `parallelizer.go` | the methods `delayingType`, `rateLimitingType` and `TypedBucketRateLimiter` promote from their embedded fields (C2) |
| `util/consistency` | the whole package | - |
| `apimachinery/pkg/util/resourceversion` | `CompareResourceVersion`, `InvalidResourceVersion.Error`, `isDigit` | `isWellFormed` (C1): a spec-able stub (a decimal string without leading zero) |
| `apimachinery/pkg/util/sets` | the whole package (generic `Set[T]`, the typed sets) | - |
| `util/flowcontrol` | `Backoff` (`NewBackOff*`, `Get`, `Reset`, `IsInBackOffSince*`, `GC`, `DeleteEntry`, `jitter`, `hasExpired`), the token-bucket throttle over `rate.Limiter` | `Backoff.Next` (C4) |
| `util/retry` | `OnError`, `RetryOnConflict`, `DefaultRetry`, `DefaultBackoff` | - |
| `apimachinery/pkg/util/wait` | `ExponentialBackoff` (newly; was names only) | the rest: `Backoff.Step`, `runConditionWithCrashProtection`, `Interrupted`, `PollImmediateUntil`, ... (types now concrete: the config imports `time`, `context`, `clock`) |
| `features` | `FeatureGates`, `ReplaceFeatureGates`, `AddFeaturesToExistingFeatureGates`, `unversionedFeatureGates`, the env-var gates (`newEnvVarFeatureGates`, `Enabled`, `Set`, `getEnabledMapFromEnvVar`) | its initialization: the `init` that installs the env-var gates, the variables `featureGates`, `defaultVersionedKubernetesFeatureGates` (the known-feature table) and `internalPackages` (translated, `etc/gen-init.py` would need hand-written init steps and a fact: proof work, C7) |
| `tools/cache` | the local half (explicit `translate` list, no `translate_types`): `store.go` (all of `cache`, `NewStore`, `NewIndexer`, `MetaNamespaceKeyFunc`, `ObjectToName`, `SplitMetaNamespaceKey`, `KeyError`, transactions), `thread_safe_store.go` (`threadSafeMap`, `storeIndex`, `LastStoreSyncResourceVersion`, `Bookmark`, `Replace`, `NewThreadSafeStore`), `index.go`, `object-names.go`, `listers.go` (`ListAll`, `ListAllByNamespace`, the generic lister), the store's metrics, `DeletedFinalStateUnknown`, `DeletionHandlingMetaNamespaceKeyFunc`, `DeletionHandlingObjectToName`, `WaitForNamedCacheSyncWithContext`, `WaitForCacheSync` | `threadSafeMap.Transaction` (C4); the reflector, the FIFOs (`DeltaFIFO`, `RealFIFO`), the controller, the shared informer, the expiration and mutation caches (out of scope for now; their types axiomatized, 26 of them because they name packages the config does not import) |
| `listers` | the whole package (`ResourceIndexer[T]`, `New`, `NewNamespaced`, `List`, `Get`) | - |
| `listers/apps/v1` | `DaemonSetLister` (with `GetPodDaemonSets`, `GetHistoryDaemonSets`), `ControllerRevisionLister` | the other resources' listers |
| `listers/core/v1` | `NodeLister`, `PodLister` | the other resources' listers |
| `k8s.io/api/{apps,core}/v1` | none | everything (generated `DeepCopy`, protobuf, registration, taint and toleration helpers); **all types concrete** (39 of apps, 322 of core: `translate_types` with the imports their fields name) |
| `apimachinery/pkg/api/resource`, `util/intstr`, `util/naming`, `util/version`, `k8s.io/utils/trace`, `github.com/go-logr/logr` | none | types and names only (`Quantity`'s struct is concrete, the type of its `inf.Dec` field, `infDecAmount`, axiomatized; `IntOrString`'s struct is axiomatized, C5) |

The API types (G4 of the etcd3 survey) were cheap: one `.toml` each, every type translates. Cost:
`Code`+`GeneratedProof` of `k8s.io/api/core/v1` (7 + 14 chunks) and `apps/v1` build in about 2
minutes of wall time (5 of CPU) on 24 cores; the files are 1.4 MB (`Code/k8s_io/api`) and 1.8 MB
(`GeneratedProof/k8s_io/api`). Their methods (`DeepCopy`, which the controller calls on every
object it mutates) stay names only: translating the generated `zz_generated.deepcopy.go` is the
next step if a proof needs `DeepCopy` to copy (it is plain field copies and `make`/`copy` of
slices and maps; `resource.Quantity.DeepCopy` and `inf.Dec` are the hard part).

The `comparable` blocker of `tools/cache` (`notes/perennial-changes.md`, "Goose: a constraint
interface's `comparable` term"): bypassed without a Perennial change, by translating the local
half's types by name instead of with `translate_types`; `Object` (the constraint interface) stays
axiomatized, which the local half does not use. The KEP-6404 watch cache's modules build with the
new `tools/cache` (`Indexers`/`IndexFunc` concrete, as before).

## Gaps

**C1. Range over a string** (Goose: `[unsupported]: range over string`), `resourceversion.go:75`
in `isWellFormed`: `for i := range s { if !isDigit(s[i]) ... }`. The loop ranges over the rune
start indices, but its result is the byte loop's (a non-ASCII rune's first byte is not a digit,
so either loop returns `false`). Blocks: `CompareResourceVersion`'s proof needs `isWellFormed`'s
spec; the consistency store's `WroteAt` and `EnsureReady` call it. Workaround: `isWellFormed`
names only; a trust-boundary spec (`true` iff `s` is non-empty, all ASCII digits, no leading `0`)
is the cheapest. Options: (a) Goose support for range over a string (decode UTF-8 per step: a
model of `utf8.DecodeRuneInString`), the general fix; (b) a trusted model (`TrustedCode/`) of
`isWellFormed` as the byte loop, faithful by the argument above; (c) the trust-boundary spec.
*Taken (2026-10-27, branch `k8s-leaf-cache`):* (c),
`Spec/k8s_io/apimachinery/pkg/util/resourceversion/isWellFormed.lean` (`wellFormed`), an axiom in
the consistency store's TCB; `CompareResourceVersion` is proved over it.

**C2. A promoted method of a generic struct, through a pointer** (Lean: `Application type mismatch:
StructFieldRef ty` with `ty : go.GoType → go.GoType`). For a type `S[T]` whose method set gets a
method from an embedded field, the pointer receiver's unfolding (`ptr_M_unfold` in
`S.TypeAssumptions`, `goose/lean_types.go:338`) refers to the struct as `ctx.glangType(t.Obj(), t)`,
the generic type without its type argument, where the value receiver's uses `ty` (`(S.ty T)`).
Hits `delayingType[T]` (embeds `TypedInterface[T]`), `rateLimitingType[T]` (embeds
`TypedDelayingInterface[T]`) and `TypedBucketRateLimiter[T]` (embeds `*rate.Limiter`). Workaround:
those promoted methods are excluded (`workqueue.toml`), so `(*delayingType[T]).Get` and friends
have no `MethodUnfold`. **This blocks verifying anything that uses the queue through its
interface**: the controller's `queue.Get()`/`Done`/`AddRateLimited` are calls on a
`TypedRateLimitingInterface[T]` holding a `*rateLimitingType[T]`, resolved through these unfolds;
so do `delayingType.AddAfter`'s own `q.Add`/`q.ShuttingDown`. Fix (one line, tried in a scratch
copy of the pinned translator: `glang.VerbatimExpr(ty)` for the struct in that `StructFieldRef`):
with it the promoted methods translate and `Code`/`GeneratedProof` of workqueue elaborate, nothing
else changes. **Closed (2026-10-28)**: fixed in Perennial (`21c6ea377`, in the pin `ad74ee4f6`), the
exclusions dropped, the 14 promoted methods proved (below).

*What C2 left unlinked (phase 2, 2026-10-27, branch `k8s-leaf-workqueue`; closed 2026-10-28).* The workqueue's
proofs do not change Goose or the pin. The underlying methods are proved (`Typed[T]`'s `Add`,
`Get`, `Done`, `Len`, `ShuttingDown`, `ShutDown`, `ShutDownWithDrain`; `delayingType`'s own
`ShutDown`, `AddAfter`, `waitingLoop`; `rateLimitingType`'s own `AddRateLimited`, `Forget`,
`NumRequeues`), and the 14 promoted methods have specs (`Spec/k8s_io/client_go/util/workqueue/`)
stated as their targets' (a promoted method forwards to the embedded value's), but no proofs:
`delayingType.{Add, Len, Get, Done, ShutDownWithDrain, ShuttingDown}` and
`rateLimitingType.{Add, Len, Get, Done, ShutDown, ShutDownWithDrain, ShuttingDown, AddAfter}`.
They are `?` in `etc/link-lean-first-workqueue.txt`, so `Proof/k8s_io/client_go/util/workqueue/Link.lean`'s
`section links_pending` takes their specs as hypotheses (`h_delayingType__Add`, ...) in every
result that reaches one: `delayingType.wp_AddAfter` (its `q.ShuttingDown()`, `q.Add(item)`),
`delayingType.wp_waitingLoop` (`q.Add`), and through them `wp_newDelayingQueue`,
`wp_NewTypedDelayingQueueWithConfig`, `wp_NewTypedRateLimitingQueueWithConfig`,
`rateLimitingType.wp_AddRateLimited`. A caller using the queue through
`TypedRateLimitingInterface[T]` needs the same for the promoted methods it calls (the DaemonSet
controller's `Get`, `Done`, `Add`, `ShutDown`); its `AddRateLimited` and `Forget` are
`rateLimitingType`'s own. **Since the pin `ad74ee4f6` (2026-10-28)** each promoted method is proved, a
forward to its target's result (`delayingType.<M>` over `Typed.<M>`, `rateLimitingType.<M>` over
`delayingType.<M>`), and the hypotheses are gone: the work queue's `Link.lean` has no
`links_pending`. Not stated at all: `TypedBucketRateLimiter`'s
promoted `*rate.Limiter` methods (no caller here).

**C3. An axiomatized type alias is declared under another name than its uses** (Lean: `Invalid
field ty ... klog.v2.Logger`). Goose declares an axiomatized alias as `axiom Logger : go.GoType`
(`goose/types.go:65`) but refers to every alias as `Logger.ty`. Hit: `klog.Logger`
(`= logr.Logger`), which the workqueue's configs and `newDelayingQueue` store and pass. Workaround:
`klog`'s config imports `github.com/go-logr/logr` (names only, new), so the alias translates
(`Logger.ty := logr.Logger.ty`). General fix: declare the axiomatized alias as `X.ty` (Perennial).

**C4. `min`/`max` of a named integer type** (Goose: `[unsupported]: comparison between non-assignable
types`). `goose.go:926` joins the first parameter's *underlying* type with the others' types:
`int64` with `time.Duration` fails. Hits `Backoff.Next` (`min(delay, p.maxDuration)`, on every
failed-pod backoff the controller records) and `threadSafeMap.Transaction` (the slow-trace
threshold, the AtomicFIFO path's batch apply). Workaround: both names only. Fix: tried, joining
the underlying types throughout (both translate and elaborate); but Perennial's rule that type
choices are the Lean semantics' suggests instead passing the named type and letting `go.min`'s
semantics take its underlying type (Perennial; `notes/perennial-changes.md`). Blocks `Backoff`'s
spec (the controller's `failedPodsBackoff`) and the transaction path of the thread-safe store.

**C5. A struct field named like a type of its package** (Lean: `type expected, got (Type' :
IntOrString → intstr.Type')`). `intstr.IntOrString` has a field `Type` of the type `Type`; in the
generated `IntOrString.TypeAssumptions`, the setter's binder `(y : Type')` resolves to the field's
projection `IntOrString.Type'` (the class is in `IntOrString`'s namespace), not the package's type
`Type'`. Workaround: `intstr`'s structs stay axiomatized (`translate_types_except_structs`): the
DaemonSet's `MaxUnavailable`/`MaxSurge` (`*intstr.IntOrString`) are then opaque, which the rolling
update (`intstr.GetScaledValueFromIntOrPercent`, names only anyway) reads. Fix: Goose qualifies a
field type that is a package-level type (`_root_.Perennial.<pkg>.Type'`) in these lemmas.

**C6. Pre-existing, now relevant: an interface embedding `comparable`** (`tools/cache.Object`;
`notes/perennial-changes.md`). Not hit by the local half (see above); the typed informers
(`TypedResourceEventHandler[T Object]`) will hit it in phase 4.

**C7. Not a Goose gap: package initializers that run translated calls.** `etc/gen-init.py`
generates an `Init.lean` from the translation; a translated initializer that calls functions (here
`features`' `init` and its table of `version.MustParse` calls) needs hand-written steps and a
package fact in its `SPECIAL`. So `features`' initialization is names only (its variables then hold
what nothing states: `FeatureGates()`'s spec needs a fact, e.g. "`featureGates` holds the env-var
gates over the known table"), and the `var _ I = &T{}` assertions of `consistency`, `workqueue`,
`flowcontrol` and `features` are names only (`!_`). The composite-literal initializers of
`tools/cache`, `workqueue` and `retry` are translated (`SPECIAL` entries with only allocation types
and `wp_auto`). Blocks: any spec reading `features.FeatureGates()` (the thread-safe store's
`LastStoreSyncResourceVersion`), until the fact and the init steps are written.

## What the proofs will need: callees without specs

Specs exist (Perennial or here) for `sync`'s `Mutex`, `RWMutex`, `Cond` (`NewCond`, `Wait`,
`Signal`, `Broadcast`), `Once.Do`, `WaitGroup.Add/Done/Wait`; `sync/atomic`'s `Value.Load/Store`,
`Bool.Load/Store`; `fmt.Sprintf`/`Errorf` (basic arguments), `errors.New`, `strings.Compare`,
`strings.Split`, `slices.Sort`, `strconv.ParseBool`, `strconv.ParseUint`, `os.Getenv`,
`container/heap.Push/Fix`, `rate.NewLimiter`, `Limiter.Wait`, `math/rand.Int63n`, `time`'s
`Time.After`, `Duration.Seconds`, `NewTicker`, `Ticker.Stop`; `labels.Everything`. Missing, per
package (standard library first, then the names-only k8s callees):

- `util/workqueue`: `sync.WaitGroup.Go` (translated in Perennial, no spec), `container/heap.Init`,
  `heap.Pop`, `math.Pow` and float64 arithmetic (the exponential limiter), `time.Time.Add`,
  `Before`, `Sub`, `Duration.Nanoseconds`; `rate.Limiter.Reserve`, `Reservation.Delay`; the
  `k8s.io/utils/clock` interfaces (`Clock.Now/Since/NewTimer`, `WithTicker.NewTicker`,
  `Ticker.C/Stop`, `Timer.C/Stop`: a clock model, or `RealClock`'s methods over `time`);
  `klog.Background`, `utilruntime.HandleCrashWithLogger`/`HandleCrashWithContext` (deferred:
  no-ops unless panicking).
- `util/consistency`: `schema.GroupResource.String`; `resourceversion.isWellFormed` (C1).
- `util/flowcontrol`: `math/rand.New`, `NewSource`, `Rand.Float64` (only when jitter is on;
  `NewBackOff` has none), `time.Time.Sub`, `UnixNano`; `clock.Clock.Now/Since`; `Backoff.Next`
  (C4).
- `util/retry`: `wait.Interrupted`, `wait.Backoff.Step`, `wait.runConditionWithCrashProtection`
  (callees of the translated `ExponentialBackoff`), `time.Sleep`, `api/errors.IsConflict`.
- `features`: `os.LookupEnv`, `context.TODO`; `naming.GetNameFromCallsite`, `version.MustParse`
  (the known-feature table, at init), `utilruntime.HandleErrorWithLogger`/`WithContext`,
  `klog.Background`, `logr.Logger.V`/`Info`.
- `tools/cache`: `strconv.ParseInt` (the store's resource-version metric), `meta.Accessor` and the
  `metav1.Object` methods `GetName/GetNamespace/GetLabels/GetResourceVersion` (on `ObjectMeta`,
  names only: the store's keys and resource version come from them), `labels.MatchesNothing`,
  `Selector.Empty/Matches`, `wait.PollImmediateUntil` (the cache-sync wait),
  `klog.FromContext/TODO`, `logr.Logger.Info`, `utilruntime.HandleErrorWithContext`,
  `api/errors.NewNotFound`.
- listers: `metav1.LabelSelectorAsSelector`, `appsv1.Resource`/`corev1.Resource`,
  `api/errors.NewNotFound`, and `tools/cache`'s (above).

## Observations for the proofs (not bugs)

- `threadSafeMap.Update`/`Add`/`DeleteWithObject` set the store's `rv` to the written object's
  resource version, whatever it is: `LastStoreSyncResourceVersion` is monotone only because the
  informer delivers events in resource-version order (the informer contract of
  `notes/k8s-daemonset-plan.md` must say so). `Replace(items, "")` resets it to `""`.
- `LastStoreSyncResourceVersion` reads `features.FeatureGates().Enabled(AtomicFIFO)` on every call;
  `Enabled` panics on an unregistered feature and reads `KUBE_FEATURE_*` environment variables
  once (`os.LookupEnv`): the example's spec of the gates needs the environment as a premise.
- The consistency store's `EnsureReady` skips a record whose versions do not compare
  (`continue`), so a malformed read version lets a sync through; `WroteAt` already refuses
  malformed written versions, and the informer's versions are the model's decimal counters.

## Open items

- Propose C3, C5 to Perennial (independent branches off its `lean`); C2 and C4 have landed (pin
  `ad74ee4f6`; C4's two functions are still names only here).
- `flowcontrol`'s package instance (the `math/rand` instance's move).
- The informers (phase 4): the reflector, `RealFIFO`, the shared informer, with C6.
