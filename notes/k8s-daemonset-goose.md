# Translating the DaemonSet controller with Goose (survey, 2026-10-27)

Goal: phase 0's program and phase 1's controller half of `notes/k8s-daemonset-plan.md`: pin the
controller's source, write the program the closed theorem is about (`dsmain.Main`), translate the
controller's closure, and list what `Main` reaches (the worklist for phases 4, 5 and 6: the informers, the controller, the closed theorem). No specs
or proofs. Perennial and the pinned translator are unchanged; the gaps continue the series of
`notes/k8s-etcd3-goose.md` (G1-G4) and `notes/k8s-clientgo-goose.md` (C1-C8) as D1, D2, ....

## The pin

`k8s.io/kubernetes` at master `878cfa6c4cc76669146b7be8b139ea10c0f06411` (2026-10-21T17:38Z, the merge
of kubernetes/kubernetes#143270), pseudo-version `v1.38.0-alpha.2.0.20261021173803-878cfa6c4cc7`, in
`examples/k8sdaemonset/go.mod` (the model API server's module; no new module). It is the
Kubernetes commit the repository's `k8s.io/apiserver` pin was published from (its mirror commit
`9c4ec15b8038`, 2026-10-21T22:13:56Z), so the four existing staging pins (`examples/k8setcd3/go.mod`)
are consistent with it, as `/home/ubuntu/.claude/jobs/b271d9c0/tmp/phaseB-prep.md` found. It has
the consistency store in client-go (`k8s.io/client-go/util/consistency`, which the controller
imports) and `StaleControllerConsistencyDaemonSet` (beta, on by default).

`k8s.io/kubernetes` requires its staging modules at `v0.0.0` (its own `go.mod` replaces them by
`./staging`), so the module replaces each one it needs by the mirror at a version:

| module | version | mirror commit (date) | Kubernetes commit | how chosen |
|---|---|---|---|---|
| k8s.io/api | v0.0.0-20261020174351-067c983ccbc3 | 067c983ccbc3 (10-20 17:43Z) | bc2377fa6f64 | the repository's pin (shared with k8setcd3) |
| k8s.io/apimachinery | v0.0.0-20261021173754-0b7d352f711c | 0b7d352f711c | 2bfdf222b6ee | the repository's pin |
| k8s.io/client-go | v0.0.0-20261021054439-569675c57fa3 | 569675c57fa3 | 508cdcd00a7f | the repository's pin |
| k8s.io/apiserver | v0.0.0-20261021221356-9c4ec15b8038 | 9c4ec15b8038 (10-21 22:13Z) | 878cfa6c4cc7 | the repository's pin |
| k8s.io/component-base | v0.0.0-20261018214756-cd2c1afd246a | cd2c1afd246a (10-18) | 7f9d9d6a3d6e | the mirror's latest commit by 2026-10-21T22:14Z; also k8setcd3's (indirect) |
| k8s.io/component-helpers | v0.20.0-alpha.2.0.20261014064534-e0a714b31fcd | e0a714b31fcd (10-14) | a8b7c6042103 | latest by 2026-10-21T22:14Z |
| k8s.io/controller-manager | v0.20.0-alpha.1.0.20261016223050-ad0db927ba11 | ad0db927ba11 (10-16) | e1143b1915fe | latest by 2026-10-21T22:14Z |
| k8s.io/kubelet | v0.0.0-20261014232747-e715b5d84f6c | e715b5d84f6c (10-14) | 6c5b45d07459 | latest by 2026-10-21T22:14Z |
| k8s.io/apiextensions-apiserver | v0.0.0-20261021192051-3da7cab8aae0 | 3da7cab8aae0 (10-21) | 6dcb8a182717 | latest by 2026-10-21T22:14Z |
| k8s.io/ktesting | v0.38.0-alpha.2.0.20261015021345-0c9393b43e6d | 0c9393b43e6d (10-15) | d039b682c189 | latest by 2026-10-21T22:14Z; only for `go mod tidy` (the tests of `pkg/controller` import it) |

"Latest by" is `gh api 'repos/kubernetes/<repo>/commits?until=2026-10-21T22:14:00Z&per_page=1'`, the
time the apiserver mirror published `878cfa6c4cc7`. The modules `go list -deps
./pkg/controller/daemon` reaches are these nine (with ktesting for tidy); klog, kube-openapi,
k8s.io/utils and sigs.k8s.io are not staging and `878cfa6c4cc7`'s `go.mod` requires the versions the
repository already has. **Checked**: the Go files of every one of the ten modules are byte-identical
to `staging/src/k8s.io/<name>` at `878cfa6c4cc7` (`diff -r`, 2026-10-27; only `go.mod`/`go.sum` differ).
client-go's and apimachinery's mirrors have one later commit by then (Kubernetes `b9a668103e2e`, files
the controller does not reach), which the pins leave out, as before.

`etc/goose.py`'s `CLIENT_GO_PINS` now checks api, apimachinery, client-go, apiserver,
component-base, klog, k8s.io/utils and kube-openapi against `examples/k8setcd3/go.mod` (projects
k8s-apiserver and k8s-daemonset translate one copy of each), reading a same-path `replace` as the
selected version. The module builds with plain `go build`/`go vet` (no local paths). Note: the Go
module proxy times out on `k8s.io/kubernetes@878cfa6c4cc7` (the repository is large); `go` falls
back to a direct `git` fetch (`GOPROXY=...,direct`, the default), about 1.5 GB into the module
cache's `vcs/` the first time.

The controller at the pin differs from kubernetes/kubernetes#139657's head `13ecb9cc` (the smoke
test's until now) only by the PR's clock injection (`controller_utils.go`, 38 lines;
`daemon_controller.go`, 58 lines), which `Main` does not need.

## `Main`, the theorem's program

`examples/k8sdaemonset/dsmain` (`dsmain.go`): `Main(checks int)` runs the robustness test's scenario
over the model API server:

1. `setFeatureGates`: `utilfeature.DefaultMutableFeatureGate.SetFromMap({WatchListClient: false,
   AtomicFIFO: true, StaleControllerConsistencyDaemonSet: true})`, panicking on an error.
2. `apimodel.NewServer` with every failure flag but `AmbiguousWrites` (`FailWrites`, `FailReads`,
   `EndWatches`, `ExpireWatches`, `Bookmarks`; D50's premise), `FaultPercent` 20 (Go only).
3. The admin client creates the node `target-node` (Ready).
4. The real `informers.NewSharedInformerFactory` over the model's non-admin clientset, the real
   `daemon.NewDaemonSetsController` (its four informers, the clientset, kube-controller-manager's
   failed-pods backoff `flowcontrol.NewBackOff(1s, 15m)`), `factory.Start`, `go dsc.Run(ctx, 2)`
   (kube-controller-manager's default two workers).
5. The admin client creates the DaemonSet `default/ds-1` (selector and template `app: nginx`, one
   container `nginx`), its pod template with the defaults kube-apiserver would give it
   (`SetDefaults_PodSpec`, `SetDefaults_Container`: restart policy, grace period 30, DNS policy,
   security context, scheduler name, image pull policy `Always`, termination message path and
   policy); the model defaults the DaemonSet's own fields (update strategy, revision history limit).
6. `checks` times, a millisecond apart: `check` lists the pods through the admin client and panics
   if two pods controlled by the DaemonSet (owner reference with `Controller` and the DaemonSet's
   UID) have the same target node (`util.GetTargetNodeName`: the node name, else the node
   affinity's `metadata.name` field). Pods being deleted count, as in the robustness test (which
   counts every pod): without surge the controller never creates a pod on a node that still has
   one of its pods, terminating or not (`podsShouldBeOnNode`, the `exists` case).
7. Returns, cancelling the context (deferred); the informers and the controller wind down.

Each intermediate value of an interface type is named with its type (`var core
coreinformers.Interface = coreGroup.V1()`, ...), so the file imports every interface it calls a
method of (gap D2 otherwise).

**The feature gates: programmatic, in `Main`.** An environment variable is not an option: client-go
reads `KUBE_FEATURE_*` only in its own gates, and `k8s.io/kubernetes/pkg/features`' init (which the
controller imports) replaces those by an adapter over component-base's
`utilfeature.DefaultMutableFeatureGate` (`client_adapter.go`), so the variable would be read and
then ignored. `SetFromMap` is what kube-controller-manager's `--feature-gates` does, and it acts on
the one gate both client-go (through the adapter) and the controller read: the proofs need a model
of that gate anyway (`Enabled`, on every `LastStoreSyncResourceVersion` and in the controller's
constructor), and `SetFromMap` is one more operation on the same state. The two features that are
on by default are set too, so the proof need not read their defaults out of `pkg/features`' table
(an init, C7).

**Bounded by a check count, not a context.** `Main(checks)` is a plain loop bound: the adequacy
theorem quantifies over `checks` (and over the execution's length, as `putget_adequate` does), and
needs no model of time or deadlines (a `context.WithTimeout` would make the run's end depend on the
clock). The program's other threads do not end with `Main`; the theorem is about every finite
execution prefix, so that does not matter.

**Go tests** (`dsmain_test.go`, `go test -race`): `TestMainNeverPanics` runs `Main(2000)`
`DSMAIN_RUNS` times; `TestScheduled` counts the runs that end with the pod on the node (the
scenario is not vacuous); `TestAmbiguousWritesDetected` runs the scenario with `AmbiguousWrites` and
counts the checker's panics (the known bug, outside the premise). Results (2026-10-27, 24 cores)
below. The smoke test (`examples/k8sdaemonset/smoke`, build tag `k8ssmoke`)
now builds in the module at the pin (its generated `go.mod` and `gen-gomod.py` are gone): 10 runs
of each test, never two pods (`TestNoEffectFailures`, `TestNoFaults`; `TestAmbiguousWrites` 0 of
10), `TestNoEffectFailures`' liveness check (scheduled within 3 s) failed in 2 of 10 runs while
another `-race` test was loading the machine (the reflectors back off under 20% failures; not a
safety property).

- Final `Main` (with `StaleControllerConsistencyDaemonSet` set): `Main(2000)` 300 runs, no panic (742 s);
  35 of 50 runs end with the pod on the node; with `AmbiguousWrites` the checker panicked in 4 of 100
  runs. (An earlier `Main`, without that gate in the map: 200 runs, no panic; 38 of 50; 7 of 100.)

## Setup

- **Project `k8s-daemonset`** (`etc/goose.py`): the local module `examples/k8sdaemonset`; packages
  `./apimodel`, `./dsmain` and, with bodies, `k8s.io/kubernetes/pkg/controller/daemon`,
  `.../daemon/util`, `.../daemon/metrics`, `pkg/controller` (all of it: `controller_utils.go`,
  `controller_ref_manager.go`), `pkg/api/v1/pod`, `pkg/apis/core/v1/helper`, `pkg/util/labels`,
  `pkg/util/hash`, `pkg/features`, `k8s.io/component-helpers/scheduling/corev1` and its
  `nodeaffinity`; names only (their `.toml`) `pkg/apis/core/helper`, `pkg/apis/core/install`,
  `pkg/apis/core/validation`, `pkg/util/taints`, apiextensions-apiserver's and controller-manager's
  `pkg/features`. It owns `Code/k8s_io/{kubernetes,component_helpers,apiextensions_apiserver,
  controller_manager}`; lean roots `hash=`, `encoding/json=`, `iter=`, `github.com/go-logr=` added.
- **Project `k8s-apiserver`** (it owns `k8s_io/{client_go,apimachinery,api,component_base}`, so the
  packages under them the controller names are translated there, from the same versions), types and
  names only: `informers`, `informers/{apps,core}`, `informers/{apps,core}/v1` (their interfaces
  concrete: they import `tools/cache` and the listers), `kubernetes/scheme`, `tools/record`,
  `api/extensions/v1beta1`, apimachinery's `api/equality`, `selection`, `util/json`, `util/rand`,
  `util/strategicpatch`, `util/validation`, component-base's `metrics/legacyregistry` and
  `zpages/features`, `k8s.io/utils/{dump,ptr}` (owned now).
- **Project `etcd`** (it owns `hash`): `hash/fnv`, types and names only (`controller.ComputeHash`).
- No existing translation changed (every file `etc/goose.py` wrote is new), so nothing that builds
  today rebuilds. `etc/gen-init.py --check`: unchanged (181 files; the new packages are in no
  closed theorem's init chain yet; phase 6 adds `dsmain`'s).

## Per package

| Package | Functions | With bodies | Names only (why) |
|---|---|---|---|
| `dsmain` | 8 | 8 | - |
| `pkg/controller/daemon` | 57 | 56 | `syncDaemonSet` (D2) |
| `pkg/controller/daemon/util` | 9 | 9 | - |
| `pkg/controller/daemon/metrics` | 1 | 1 | its variable's initializer (`metrics.NewCounterVec`, an init) |
| `pkg/controller` | 106 | 96 | `RealPodControl.createPods`, `.DeletePod`, `.PatchPod`, `RealRSControl.PatchReplicaSet`, `RealControllerRevisionControl.PatchControllerRevision`, `AddOrUpdateTaintOnNode`, `RemoveTaintOffNode`, `PatchNodeTaints`, `AddOrUpdateLabelsOnNode`, `ComputeHash` (D2) |
| `pkg/api/v1/pod` | 29 | 28 | `VisitContainers` (D1) |
| `pkg/apis/core/v1/helper` | 22 | 22 | - |
| `pkg/util/labels` | 6 | 6 | - |
| `pkg/util/hash` | 1 | 1 | - |
| `pkg/features` | 5 | 4 | its `init` and the tables it registers (`defaultVersionedKubernetesFeatureGates`, `defaultKubernetesFeatureGateDependencies`; C7) and the `var _ I = &T{}` assertions; the feature names (constants) and the client adapter have bodies |
| `component-helpers/scheduling/corev1` | 6 | 6 | - |
| `.../corev1/nodeaffinity` | 15 | 11 | `LazyErrorNodeSelector.Match`, `PreferredSchedulingTerms.Score`, `extractNodeFields`, `RequiredNodeAffinity.Match` (D2) |

The API types (`k8s.io/api/{apps,core}/v1`) are concrete since phase 1's leaf half; their methods
(`DeepCopy`, ...) stay names only. Sizes: `Code/k8s_io/kubernetes` 2.1 MB, its `GeneratedProof`
0.3 MB; the new modules elaborate in a few minutes on 24 cores (`Code...controller.daemon` 21 s).

## Gaps

**D1. Range over a function** (Goose: `[unsupported]: range over func(yield func(*Container,
ContainerType) bool)`), `pkg/api/v1/pod/util.go:73`, `VisitContainers` (`for c, t := range
ContainerIter(podSpec, mask)`). G2 of the etcd3 survey, again. Blocks: nothing `Main` reaches
(`VisitContainers` is not in its call graph). Workaround: names only. Fix: on Perennial's `lean`
after the pin (`caa9d07ee`, "goose: range over functions"); the pin bump brings it.

**D2. A method of an interface whose package the file does not import, named through an imported
package of the same name** (Lean: `Unknown identifier _root_.Perennial.k8s_io.api.apps.v1.PodInterface.ty`).
G3 of the etcd3 survey (`notes/perennial-changes.md`, "Goose: imports of packages whose types a
body names, and same-named packages"), now on the controller's main path. Goose's `pkgRef`
(`goose/goose.go:2967`), for a package not among the file's imports, substitutes an imported one
with the same Go name. Kubernetes names nearly every API and client package `v1`, so:
- `controller_utils.go` imports `k8s.io/api/apps/v1` (as `apps`) but not client-go's typed
  `kubernetes/typed/{apps,core}/v1`; `r.KubeClient.CoreV1().Pods(ns).Create(...)` resolves the
  methods on `CoreV1Interface`, `PodInterface`, `NodeInterface`, ... of a typed package, emitted as
  `k8s.io/api/apps/v1`'s. Hits `RealPodControl.createPods` (every pod create the controller makes),
  `DeletePod`, `PatchPod`, `RealRSControl.PatchReplicaSet`,
  `RealControllerRevisionControl.PatchControllerRevision`, `AddOrUpdateTaintOnNode`,
  `RemoveTaintOffNode`, `PatchNodeTaints`, `AddOrUpdateLabelsOnNode`.
- `ComputeHash` calls `hash.Hash32`'s methods (`fnv.New32a()`): the standard library's `hash` is not
  imported, the repository's `pkg/util/hash` (imported as `hashutil`) is substituted.
- `daemon_controller.go`'s `syncDaemonSet` calls `metrics.DaemonsetRequeueSkips.WithLabelValues(...)
  .Inc()`: component-base's `metrics.CounterMetric`, substituted by the controller's own
  `daemon/metrics`. (This is the consistency store's not-ready branch, the heart of S1.)
- `nodeaffinity.go` reads `node.Labels`/`node.Name` (fields promoted from metav1's `ObjectMeta`,
  not imported): emitted as `core/v1.ObjectMeta`. Hits `LazyErrorNodeSelector.Match`,
  `PreferredSchedulingTerms.Score`, `extractNodeFields`, `RequiredNodeAffinity.Match` (the
  DaemonSet's node-affinity check in `nodeShouldRunDaemonPod`).
- `dsmain` itself hit it (`admin.CoreV1().Pods(ns)`, `factory.Apps().V1()`): worked around in its
  code (each value named with its interface type, so the packages are imported).

Blocks: phase 5's `syncDaemonSet`, `createPods` and the node-affinity check, i.e. S1's proof.
Workaround: the functions are names only (`pkg/controller.toml`, `daemon.toml`,
`nodeaffinity.toml`). **Fix tried** (2026-10-27): in a scratch copy of the pinned translator,
`pkgRef` without the substitution (the package's own path, always): with the exclusions dropped,
every function above translates and `Code`/`GeneratedProof` of `pkg/controller`,
`pkg/controller/daemon`, `nodeaffinity` and `dsmain` elaborate (their Lean modules reach the
interfaces' packages through public imports); no other file of the project changes (so the
substitution mistranslated nothing else here). Not on Perennial's `lean` (checked at its head,
2026-10-27). Options: (a) the Perennial change (the substitution removed, as
`notes/perennial-changes.md` proposes; an error, or an added import, when the module is not in
scope), the general fix, small; (b) a Goose fork of the controller (`upamanyus/kubernetes`) whose
files import the typed client packages (`var _ corev1client.PodInterface` style, as `dsmain` does),
a test-only source change that keeps the semantics; (c) trusted models of the ten functions. (a)
first: it unblocks all ten and the earlier G3 cases at once.

**Not hit.** Goose accepts every other function of the body packages, including those the
call-graph survey flagged: `getPatch` (`json.Marshal`, `Unmarshal` into `map[string]interface{}`,
unchecked assertions on the result), `reflect.DeepEqual` and `apiequality.Semantic.DeepEqual`,
`errors.As`, `fmt.Sprint` compared as a label value, `sync.WaitGroup.Go`, `DeepCopy`,
`legacyregistry.MustRegister` (through `sync.Once.Do`), the handlers' unchecked type assertions
(`obj.(*apps.DaemonSet)`). They translate as calls of names-only (or Perennial-modeled) functions,
so they are hazards for the proofs, not for the translation:

| Hazard | Where | What the proof needs |
|---|---|---|
| `json.Marshal` of the DaemonSet, `json.Unmarshal` into `map[string]interface{}`, `raw["spec"].(map[string]interface{})` | `getPatch` (`update.go:505`; `snapshot` → `constructHistory` on every sync) | a spec of `encoding/json`'s `Marshal` and apimachinery's `util/json.Unmarshal` over a JSON-value model, or a trusted model of `getPatch` (only the ControllerRevision's data depends on it: no S1 fact); the assertions panic unless `spec` and `template` are objects (they are: structs always serialize) |
| `controller.ComputeHash`: `fnv.New32a`, `hashutil.DeepHashObject` → `dump.ForHash` (spew, reflection), `rand.SafeEncodeString(fmt.Sprint(...))` | `snapshot` (every sync); D2 too | a spec "some string" is enough for S1 (the hash only names revisions and labels pods; a mismatch makes the rolling update delete a pod, never create a second one without surge) |
| `reflect.DeepEqual` (`syncDaemonSet`'s selector check, the handlers' owner and label checks, `update.go`'s collision count), `apiequality.Semantic.DeepEqual` (`shouldIgnoreNodeUpdate`; `third_party/forked/golang/reflect` untranslated) | handlers, every sync | specs on the values compared (a `bool`, true when equal), at the types used |
| `errors.As(err, &consistencyErr)` | `syncDaemonSet` | `errors.AsTarget` of the consistency store's error type (the putget adequacy has the class for `rpctypes.EtcdError`) |
| `fmt.Sprint(*generation)` compared with a label | `util.CreatePodTemplate`, `util.IsPodUpdated` | `fmt.Sprint` of an `int64`: a deterministic, injective string (Perennial has `Sprintf` specs for basic arguments) |
| `sync.WaitGroup.Go` | `Run`'s workers | a spec (Perennial translates it, no spec yet) |
| `DeepCopy` of `DaemonSet`, `ControllerRevision`, `PodTemplateSpec`, `PodSpec` | `storeDaemonSetStatus`, `constructHistory`, `CreatePodTemplate`, `GetPodFromTemplate` | translate `zz_generated.deepcopy.go` (plain copies) or trust-boundary specs over the deep values (`Proof/k8s_io/api/Deep.lean`) |
| `legacyregistry.MustRegister` | `metrics.Register` (once) | its spec: registration of a fresh name (the repository's `prometheus.namesUnclaimed` pattern) |
| `obj.(*apps.DaemonSet)` and friends | every event handler | the informers' delivery of objects of the handler's concrete type (phase 4's informer contract) |
| `SetFromMap`, `Enabled` of component-base's feature gate; `pkg/features`' init (C7) | `Main`, the constructor, `LastStoreSyncResourceVersion` | a model of the gate's state: known features, set values read back; the init registering the tables (C7) |

## The call graph of `Main` (the worklist)

`etc/k8s-worklist.py` (with `etc/k8s-callgraph`, a VTA call graph over RTA's, every package
initializer an RTA root) walks the graph from `dsmain.Main`, following the functions of the layers
the plan verifies (`Main`'s package, the controller's packages, client-go's leaf libraries, the
informers: `tools/cache` and `informers/...`, the model) and listing, besides them, every function
outside those layers that they call (the boundary). Each is classified by the translation in the
tree. The analysis over-approximates interface calls; the API groups the program never touches and
kube's internal API types (reached through `DeepCopyObject` and the informer factory's `newFunc`
callbacks) are pruned, and a few such leftovers remain at the boundary (`clientcmd`'s and
`clientauthentication`'s `DeepCopyObject`, through the cache mutation detector, off by default).
Rerun it after a translation change (`GOTOOLCHAIN=go1.27.1 etc/k8s-worklist.py`).

What it says, per phase (2026-10-27):
- **Phase 5 (the controller)**: 134 functions reached, 125 with bodies; the 9 names-only are all D2
  (`syncDaemonSet`, `createPods`, `DeletePod`, `PatchPod`, `PatchControllerRevision`, `ComputeHash`,
  the three node-affinity matchers). Everything else on the controller's paths translates.
- **Phase 2 (leaf libraries)**: 109 reached, all with bodies but `Backoff.Next` (C4, the failed-pods
  backoff); the workqueue's promoted methods (C2) do not show (the call graph resolves them to their
  targets), but the Lean semantics resolves `queue.Get()` through them.
- **Phase 4 (the informers)**: 312 reached, 74 with bodies (`tools/cache`'s local half), 234 names
  only: the reflector (`ListAndWatch*`, `list`, `watch`, `handleAnyWatch`, ...), `RealFIFO`, the
  shared informer and its processor and listeners, the informer factory and the four typed
  informers; and 4 untranslated (`tools/cache/synctrack`). At the boundary they also need
  `tools/pager` (the reflector's list), `k8s.io/utils/buffer` (the listener's ring buffer),
  apimachinery's `util/net`, `meta`, `watch`, `wait` (names only or untranslated).
- **Phase 3 (the model)**: 60 reached, all with bodies (and specs).
- **Phase 6 (`Main`, the closed theorem)**: 8 functions, all with bodies; the boundary it adds: component-base's
  feature gate (`SetFromMap`), `context.WithCancel`, `time.Sleep`.
- **The boundary**: 397 functions outside the verified layers are called from them: 70 with bodies
  (Perennial's or here: `sync`, `context`, apimachinery's `meta/v1` accessors, `api/errors`), 14
  trusted models (Perennial's `fmt`, `strings`, `sync`, ...), 293 names only (the API types'
  `DeepCopy` and accessors, apimachinery's `labels`, `fields`, `api/meta`, `wait`, `runtime`,
  `unstructured`, client-go's `tools/record`, klog, logr, `k8s.io/utils/clock`, `reflect`,
  `encoding/json`, `hash/fnv`, `math/rand`, ...), 20 untranslated (the pager, the ring buffer,
  `third_party/forked/golang/reflect`, `util/diff`, `util/net`, `api/validation`, and the
  over-approximation's leftovers). Each needs a spec: Perennial's, a trust-boundary one here, or a
  translation with bodies (the plan's "Below" row).

1020 functions (891 more pruned: other API groups, internal API types).

| layer | bodies | trusted model | names only | not translated |
|---|---|---|---|---|
| dsmain | 8 (128 lines) | - | - | - |
| controller | 125 (2785 lines) | - | 9 (210 lines) | - |
| leaf | 108 (959 lines) | - | 1 (14 lines) | - |
| informers | 74 (732 lines) | - | 234 (4196 lines) | 4 (30 lines) |
| apimodel | 60 (586 lines) | - | - | - |
| boundary | 70 (562 lines) | 14 (122 lines) | 293 (2084 lines) | 20 (165 lines) |

#### Main's package (phase 6)

- `github.com/mit-pdos/etcd-grove/examples/k8sdaemonset/dsmain`: bodies (8): Main, check, controlledBy, newDaemonSet, newNode, run, serverConfig, setFeatureGates.

#### The controller (phase 5)

- `k8s.io/component-helpers/scheduling/corev1`: bodies (3): FindMatchingUntoleratedTaint, TolerationsTolerateTaint, getFilteredTaints.
- `k8s.io/component-helpers/scheduling/corev1/nodeaffinity`: bodies (7): NewLazyErrorNodeSelector, NewRequiredNodeAffinity, isEmptyNodeSelectorTerm, newNodeSelectorTerm, nodeSelectorRequirementsAsFieldSelector, nodeSelectorRequirementsAsSelector, nodeSelectorTerm.match; names only (3): LazyErrorNodeSelector.Match (D2), RequiredNodeAffinity.Match (D2), extractNodeFields (D2).
- `k8s.io/kubernetes/pkg/api/v1/pod`: bodies (8): GetPodCondition, GetPodConditionFromList, GetPodReadyCondition, IsPodAvailable, IsPodPhaseTerminal, IsPodReady, IsPodReadyConditionTrue, IsPodTerminal.
- `k8s.io/kubernetes/pkg/apis/core/v1/helper`: bodies (1): AddOrUpdateTolerationInPodSpec.
- `k8s.io/kubernetes/pkg/controller`: bodies (38): AddPodControllerIndexer, AddPodNodeNameIndexer, BaseControllerRefManager.CanAdopt^, BaseControllerRefManager.ClaimObject, ControlleeExpectations.Add, ControlleeExpectations.Fulfilled, ControlleeExpectations.MarshalLog^, ControlleeExpectations.isExpired, ControllerExpectations.CreationObserved, ControllerExpectations.DeleteExpectations, ControllerExpectations.DeletionObserved, ControllerExpectations.GetExpectations, ControllerExpectations.LowerExpectations, ControllerExpectations.SatisfiedExpectations, ControllerExpectations.SetExpectations, ControllerRevisionControllerRefManager.AdoptControllerRevision, ControllerRevisionControllerRefManager.ClaimControllerRevisions, ControllerRevisionControllerRefManager.ReleaseControllerRevision, FilterPodsByOwner, GenerateDeleteOwnerRefStrategicMergeBytes, GetPodFromTemplate, NewControllerExpectations, NewControllerRevisionControllerRefManager, NewPodControllerRefManager, PodControllerIndexKey, PodControllerRefManager.AdoptPod, PodControllerRefManager.ClaimPods, PodControllerRefManager.ReleasePod, RealPodControl.CreatePods, RealPodControl.CreatePodsWithGenerateName, RecheckDeletionTimestamp, getPodsAnnotationSet, getPodsFinalizers, getPodsLabelSet, getPodsPrefix, ownerRefControllerPatch, ownerReference, validateControllerRef; names only (5): ComputeHash (D2), RealControllerRevisionControl.PatchControllerRevision (D2), RealPodControl.DeletePod (D2), RealPodControl.PatchPod (D2), RealPodControl.createPods (D2).
- `k8s.io/kubernetes/pkg/controller/daemon`: bodies (55): DaemonSetsController.Run, DaemonSetsController.addDaemonset, DaemonSetsController.addHistory, DaemonSetsController.addNode, DaemonSetsController.addPod, DaemonSetsController.cleanupHistory, DaemonSetsController.constructHistory, DaemonSetsController.controlledHistories, DaemonSetsController.dedupCurHistories, DaemonSetsController.deleteDaemonset, DaemonSetsController.deleteHistory, DaemonSetsController.deletePod, DaemonSetsController.enqueue, DaemonSetsController.enqueueDaemonSetAfter, DaemonSetsController.getDaemonPods, DaemonSetsController.getDaemonSetsForHistory, DaemonSetsController.getDaemonSetsForPod, DaemonSetsController.getNodesToDaemonPods, DaemonSetsController.manage, DaemonSetsController.podsShouldBeOnNode, DaemonSetsController.processNextNodeUpdate, DaemonSetsController.processNextWorkItem, DaemonSetsController.resolveControllerRef, DaemonSetsController.rollingUpdate, DaemonSetsController.runNodeUpdateWorker^, DaemonSetsController.runWorker^, DaemonSetsController.snapshot, DaemonSetsController.syncNodeUpdate, DaemonSetsController.syncNodes, DaemonSetsController.updateDaemonSet, DaemonSetsController.updateDaemonSetStatus, DaemonSetsController.updateDaemonset, DaemonSetsController.updateHistory, DaemonSetsController.updateNode, DaemonSetsController.updatePod, DaemonSetsController.updatedDesiredNodeCounts, Match, NewDaemonSetsController, NodeShouldRunDaemonPod, daemonPodTolerations, failedPodsBackoffKey, findUpdatedPodsOnNode, getPatch, getUnscheduledPodsWithoutNode, historiesByRevision.Len^, historiesByRevision.Less^, historiesByRevision.Swap^, maxRevision, nodeShouldRunDaemonPod, podByCreationTimestampAndPhase.Len^, podByCreationTimestampAndPhase.Less^, podByCreationTimestampAndPhase.Swap^, predicates, shouldIgnoreNodeUpdate, storeDaemonSetStatus; names only (1): DaemonSetsController.syncDaemonSet (D2).
- `k8s.io/kubernetes/pkg/controller/daemon/metrics`: bodies (1): Register.
- `k8s.io/kubernetes/pkg/controller/daemon/util`: bodies (9): AddOrUpdateDaemonPodTolerations, AllowsSurge, CreatePodTemplate, GetTargetNodeName, GetTemplateGeneration, IsPodUpdated, ReplaceDaemonSetPodNodeNameNodeAffinity, SurgeCount, UnavailableCount.
- `k8s.io/kubernetes/pkg/features`: bodies (1): clientAdapter.Enabled.
- `k8s.io/kubernetes/pkg/util/hash`: bodies (1): DeepHashObject.
- `k8s.io/kubernetes/pkg/util/labels`: bodies (1): CloneAndAddLabel.

#### client-go's leaf libraries (phase 2)

- `k8s.io/client-go/features`: bodies (5): FeatureGates, envVarFeatureGates.Enabled, envVarFeatureGates.getEnabledMapFromEnvVar^, envVarFeatureGates.hasAlreadyReadEnvVar, envVarFeatureGates.wasFeatureEnabledViaSetMethod.
- `k8s.io/client-go/listers`: bodies (4): New, NewNamespaced, ResourceIndexer.Get, ResourceIndexer.List.
- `k8s.io/client-go/listers/apps/v1`: bodies (6): NewControllerRevisionLister, NewDaemonSetLister, controllerRevisionLister.ControllerRevisions, daemonSetLister.DaemonSets, daemonSetLister.GetHistoryDaemonSets, daemonSetLister.GetPodDaemonSets.
- `k8s.io/client-go/listers/core/v1`: bodies (3): NewNodeLister, NewPodLister, podLister.Pods.
- `k8s.io/client-go/util/consistency`: bodies (15): ConsistencyError.Error*^, NewConsistencyStore*, NewNoopConsistencyStore*, consistencyStore.Clear*, consistencyStore.EnsureReady*, consistencyStore.WroteAt*, consistencyStore.ensureWrittenRecord*, consistencyStore.getWrittenRecord*, newConsistencyStore*, newOwnerRecord*, noopConsistencyStore.Clear*, noopConsistencyStore.EnsureReady*, noopConsistencyStore.WroteAt*, ownerRecord.EnsureReady*, ownerRecord.WroteAt*.
- `k8s.io/client-go/util/flowcontrol`: bodies (12): Backoff.GC^, Backoff.Get, Backoff.IsInBackOffSinceUpdate, Backoff.hasExpired, Backoff.initEntryUnsafe, Backoff.jitter, NewBackOff, NewBackOffWithJitter, NewTokenBucketPassiveRateLimiterWithClock^, newBackoff, newTokenBucketRateLimiterWithPassiveClock, tokenBucketPassiveRateLimiter.TryAccept^; names only (1): Backoff.Next (C4).
- `k8s.io/client-go/util/workqueue`: bodies (63): DefaultQueue*, DefaultTypedControllerRateLimiter*, NewTypedDelayingQueueWithConfig*, NewTypedItemExponentialFailureRateLimiter*, NewTypedMaxOfRateLimiter*, NewTypedRateLimitingQueueWithConfig*, NewTypedWithConfig*, Typed.Add*, Typed.Done*, Typed.Get*, Typed.ShutDown*^, Typed.ShutDownWithDrain*^, Typed.ShuttingDown*, Typed.updateUnfinishedWork, Typed.updateUnfinishedWorkLoop^, TypedBucketRateLimiter.Forget*, TypedBucketRateLimiter.When*, TypedItemExponentialFailureRateLimiter.Forget*, TypedItemExponentialFailureRateLimiter.When*, TypedMaxOfRateLimiter.Forget*, TypedMaxOfRateLimiter.When*, defaultQueueMetrics.add, defaultQueueMetrics.done, defaultQueueMetrics.get, defaultQueueMetrics.sinceInSeconds, defaultQueueMetrics.updateUnfinishedWork, defaultRetryMetrics.retry*, delayingType.AddAfter* (C2), delayingType.ShutDown* (C2), delayingType.waitingLoop*, insert*, newDelayingQueue*, newQueue*, newQueueMetrics*, newQueueWithConfig*, newRetryMetrics*, noMetrics.add*, noMetrics.done*, noMetrics.get*, noMetrics.updateUnfinishedWork*, noopMetric.Dec, noopMetric.Inc*, noopMetric.Observe, noopMetric.Set, noopMetricsProvider.NewAddsMetric, noopMetricsProvider.NewDepthMetric, noopMetricsProvider.NewLatencyMetric, noopMetricsProvider.NewLongestRunningProcessorSecondsMetric, noopMetricsProvider.NewRetriesMetric*, noopMetricsProvider.NewUnfinishedWorkSecondsMetric, noopMetricsProvider.NewWorkDurationMetric, queue.Len*, queue.Pop*, queue.Push*, queue.Touch*, rateLimitingType.AddRateLimited*, rateLimitingType.Forget*, waitForPriorityQueue.Len*, waitForPriorityQueue.Less*^, waitForPriorityQueue.Peek*, waitForPriorityQueue.Pop*^, waitForPriorityQueue.Push*^, waitForPriorityQueue.Swap*^.

#### The informers (phase 4)

- `k8s.io/client-go/informers`: names only (8): NewSharedInformerFactory, NewSharedInformerFactoryWithOptions, sharedInformerFactory.Apps, sharedInformerFactory.Core, sharedInformerFactory.InformerFor, sharedInformerFactory.InformerName, sharedInformerFactory.Start, sharedInformerFactory.StartWithContext.
- `k8s.io/client-go/informers/apps`: names only (2): New, group.V1.
- `k8s.io/client-go/informers/apps/v1`: names only (19): New, NewTypedControllerRevisionInformerWithOptions, NewTypedDaemonSetInformerWithOptions, NewTypedDeploymentInformerWithOptions, NewTypedReplicaSetInformerWithOptions, NewTypedStatefulSetInformerWithOptions, controllerRevisionInformer.Informer, controllerRevisionInformer.Lister, controllerRevisionInformer.TypedInformer, controllerRevisionInformer.defaultInformer, daemonSetInformer.Informer, daemonSetInformer.Lister, daemonSetInformer.TypedInformer, daemonSetInformer.defaultInformer, deploymentInformer.defaultInformer, replicaSetInformer.defaultInformer, statefulSetInformer.defaultInformer, version.ControllerRevisions, version.DaemonSets.
- `k8s.io/client-go/informers/core`: names only (2): New, group.V1.
- `k8s.io/client-go/informers/core/v1`: names only (41): New, NewTypedComponentStatusInformerWithOptions, NewTypedConfigMapInformerWithOptions, NewTypedEndpointsInformerWithOptions, NewTypedEventInformerWithOptions, NewTypedLimitRangeInformerWithOptions, NewTypedNamespaceInformerWithOptions, NewTypedNodeInformerWithOptions, NewTypedPersistentVolumeClaimInformerWithOptions, NewTypedPersistentVolumeInformerWithOptions, NewTypedPodInformerWithOptions, NewTypedPodTemplateInformerWithOptions, NewTypedReplicationControllerInformerWithOptions, NewTypedResourceQuotaInformerWithOptions, NewTypedSecretInformerWithOptions, NewTypedServiceAccountInformerWithOptions, NewTypedServiceInformerWithOptions, componentStatusInformer.defaultInformer, configMapInformer.defaultInformer, endpointsInformer.defaultInformer, eventInformer.defaultInformer, limitRangeInformer.defaultInformer, namespaceInformer.defaultInformer, nodeInformer.Informer, nodeInformer.Lister, nodeInformer.TypedInformer, nodeInformer.defaultInformer, persistentVolumeClaimInformer.defaultInformer, persistentVolumeInformer.defaultInformer, podInformer.Informer, podInformer.Lister, podInformer.TypedInformer, podInformer.defaultInformer, podTemplateInformer.defaultInformer, replicationControllerInformer.defaultInformer, resourceQuotaInformer.defaultInformer, secretInformer.defaultInformer, serviceAccountInformer.defaultInformer, serviceInformer.defaultInformer, version.Nodes, version.Pods.
- `k8s.io/client-go/tools/cache`: bodies (74): DeletionHandlingMetaNamespaceKeyFunc, InformerNameAndResource.GroupVersionResource, InformerNameAndResource.Name, InformerNameAndResource.Reserved*, KeyError.Error^, KeyError.Unwrap^, ListAll, ListAllByNamespace, MetaNamespaceIndexFunc, MetaNamespaceKeyFunc, MetaObjectToName, NewIndexer, NewObjectName, NewStore, NewThreadSafeStore*, ObjectName.String*, ObjectToName, SplitMetaNamespaceKey*, TransactionError.Error, TypedIndexerFuncToIndexerFunc, WaitForCacheSync, WaitForNamedCacheSyncWithContext, WithStoreMetrics, WithThreadSafeStoreMetrics, WithTransformer, cache.Add, cache.AddIndexers, cache.Bookmark, cache.ByIndex, cache.Delete, cache.Get, cache.GetByKey, cache.GetIndexers, cache.Index, cache.LastStoreSyncResourceVersion, cache.List, cache.ListKeys, cache.Replace, cache.Transaction, cache.Update, genericLister.List, genericNamespaceLister.List, newFIFOMetrics, newStoreMetrics*, noopInformerMetricsProvider.NewProcessingLatencyMetric, noopInformerMetricsProvider.NewQueuedItemMetric, noopInformerMetricsProvider.NewStoreResourceVersionMetric, noopMetric.Observe, noopMetric.Set*, parseRVForMetricsWithTruncation*, rvFromObject*, storeIndex.addIndexers, storeIndex.addKeyToIndex*, storeIndex.deleteKeyFromIndex*, storeIndex.getKeysByIndex*, storeIndex.getKeysFromIndex, storeIndex.reset*, storeIndex.updateIndices*, storeIndex.updateSingleIndex*, threadSafeMap.Add*, threadSafeMap.AddIndexers, threadSafeMap.Bookmark*, threadSafeMap.ByIndex*, threadSafeMap.DeleteWithObject*, threadSafeMap.Get*, threadSafeMap.GetIndexers, threadSafeMap.Index, threadSafeMap.LastStoreSyncResourceVersion, threadSafeMap.List*, threadSafeMap.ListKeys*, threadSafeMap.Replace*, threadSafeMap.Update*, threadSafeMap.deleteLocked*, threadSafeMap.updateLocked*; names only (162): DefaultWatchErrorHandler, DeltaFIFO.Add, DeltaFIFO.Close, DeltaFIFO.Delete, DeltaFIFO.Done, DeltaFIFO.HasSyncedChecker, DeltaFIFO.KeyOf, DeltaFIFO.Pop, DeltaFIFO.Replace, DeltaFIFO.Resync, DeltaFIFO.Transformer, DeltaFIFO.Update, DeltaFIFO.checkSynced_locked, DeltaFIFO.hasSynced_locked, DeltaFIFO.queueActionInternalLocked, DeltaFIFO.queueActionLocked, DeltaFIFO.syncKeyLocked, Deltas.Newest, FIFO.Done, InformerName.WithResource, ListWatch.List, ListWatch.ListWithContext^, ListWatch.Watch, ListWatch.WatchWithContext, New, NewCacheMutationDetector, NewDeltaFIFOWithOptions, NewRealFIFOWithOptions, NewReflectorWithOptions, NewRetryWithDeadline, NewShardedListWatch, NewSharedIndexInformerWithOptions, NewTypedSharedIndexInformer, RealFIFO.Add, RealFIFO.Bookmark, RealFIFO.Close, RealFIFO.Delete, RealFIFO.Done, RealFIFO.HasSyncedChecker, RealFIFO.Pop, RealFIFO.PopBatch, RealFIFO.Replace, RealFIFO.Resync, RealFIFO.Transformer, RealFIFO.Update, RealFIFO.addReplaceToItemsLocked, RealFIFO.addResyncToItemsLocked, RealFIFO.addToItems_locked, RealFIFO.checkSynced_locked, RealFIFO.hasSynced_locked, RealFIFO.keyOf, RealFIFO.whileProcessing_locked, Reflector.LastSyncResourceVersion, Reflector.ListAndWatchWithContext, Reflector.RunWithContext^, Reflector.list, Reflector.relistResourceVersion, Reflector.resyncChan, Reflector.rewatchResourceVersion, Reflector.setIsLastSyncResourceVersionUnavailable, Reflector.setLastSyncResourceVersion, Reflector.startResync, Reflector.syncWith, Reflector.watch, Reflector.watchList, Reflector.watchWithResync^, ResourceEventHandlerFuncs.OnAdd, ResourceEventHandlerFuncs.OnDelete, ResourceEventHandlerFuncs.OnUpdate, ToListWatcherWithWatchListSemantics, ToListerWatcherWithContext, ToListerWithContext, ToWatcherWithContext, VeryShortWatchError.Error^, WaitFor^, checkWatchListDataConsistencyIfRequested, controller.HasSyncedChecker, controller.RunWithContext, controller.processLoop^, dedupDeltas, defaultCacheMutationDetector.AddObject, defaultCacheMutationDetector.CompareObjects, defaultCacheMutationDetector.Run^, determineResyncPeriod, dummyMutationDetector.AddObject, dummyMutationDetector.Run^, getExpectedGVKFromObject, getTypeDescriptionFromObject, handleAnyWatch, handleListWatch, handleWatch, initialEventsEndBookmarkTicker.observeLastEventTimeStamp, initialEventsEndBookmarkTicker.produceWarningIfExpired, initialEventsEndBookmarkTicker.warnIfExpired, isDeletionDup, isDup, isExpiredError, isTooLargeResourceVersionError, isUnsupportedTableListObject, isUnsupportedTableObject, isWatchErrorRetriable, listWatcherWithWatchListSemanticsWrapper.IsWatchListSemanticsUnSupported^, listerWrapper.ListWithContext^, nameForFunction, nameForFunctions, nameForHandler, nameForHandlerFuncs, newInitialEventsEndBookmarkTicker, newInitialEventsEndBookmarkTickerInternal, newProcessListener, newQueueFIFO, noopTicker.C, noopTicker.Stop, processDeltas, processDeltasInBatch, processReplacedAllInfo, processorListener.add, processorListener.determineNextResync, processorListener.pop^, processorListener.run^, processorListener.setResyncPeriod, processorListener.shouldResync, processorListener.watchSynced^, reconcileReplacement, retryWithDeadlineImpl.After, retryWithDeadlineImpl.ShouldRetry, retryWithDeadlineImpl.reset, shardedListWatch.IsWatchListSemanticsUnSupported^, shardedListWatch.List, shardedListWatch.ListWithContext^, shardedListWatch.Watch, shardedListWatch.WatchWithContext, shardedListWatch.logClientFallback^, sharedIndexInformer.AddEventHandlerWithOptions, sharedIndexInformer.AddIndexers, sharedIndexInformer.GetIndexer, sharedIndexInformer.GetStore, sharedIndexInformer.HasStarted, sharedIndexInformer.HasSynced, sharedIndexInformer.HasSyncedChecker, sharedIndexInformer.OnAdd, sharedIndexInformer.OnDelete, sharedIndexInformer.OnUpdate, sharedIndexInformer.RunWithContext^, sharedIndexInformer.SetShardSelector, sharedIndexInformer.SetTransform, sharedIndexInformer.SetWatchErrorHandler, sharedIndexInformer.handleBatchDeltas, sharedIndexInformer.handleDeltas, sharedIndexInformerDone.Done, sharedIndexInformerDone.Name, sharedProcessor.addListener, sharedProcessor.distribute, sharedProcessor.resyncCheckPeriodChanged, sharedProcessor.run^, sharedProcessor.shouldResync, threadSafeMap.Transaction (C4), typedIndexer.AddTypedIndexers, typedResourceEventHandler.OnAdd, typedResourceEventHandler.OnDelete, typedResourceEventHandler.OnUpdate, watcherWrapper.WatchWithContext.
- `k8s.io/client-go/tools/cache/synctrack`: not translated (4): NewSingleFileTracker, SingleFileTracker.Finished, SingleFileTracker.Start, SingleFileTracker.UpstreamHasSynced.

#### The model API server (phase 3; trusted Go)

- `github.com/mit-pdos/etcd-grove/examples/k8sdaemonset/apimodel`: bodies (60): Clientset.AppsV1*, Clientset.CoreV1*, NewServer*, Server.AdminClientset*, Server.Clientset*, Server.chance*, Server.create*, Server.get*, Server.list*, Server.nextRV*, Server.record*, Server.remove*, Server.update*, Server.watch*, appsV1.ControllerRevisions*, appsV1.DaemonSets*, copyObject*, coreV1.Events*, coreV1.Nodes*, coreV1.Pods*, daemonSetClient.Create*, daemonSetClient.Get*, daemonSetClient.List*, daemonSetClient.UpdateStatus*, daemonSetClient.Watch*, daemonSetStatusEqual*, emptyDaemonSet*, emptyNode*, emptyPod*, emptyRevision*, eventClient.CreateWithEventNamespace*^, eventClient.PatchWithEventNamespace*^, int32PtrEqual*, newTable*, noGrace*, nodeClient.Create*, nodeClient.List*, nodeClient.Watch*, podClient.Create*, podClient.Delete*, podClient.List*, podClient.Watch*, podGrace*, prepareDaemonSet*, prepareNode*, preparePod*, prepareRevision*, replaceRevision*, revisionClient.Create*, revisionClient.Delete*, revisionClient.Get*, revisionClient.List*, revisionClient.Update*, revisionClient.Watch*, rvString*, updateDaemonSetStatus*, watcher.ResultChan*, watcher.Stop*, watcher.run*, watcher.send.

#### The boundary (what the verified layers call outside them)

- `bytes`: bodies (1): Equal.
- `container/heap`: names only (4): Fix*, Init, Pop*, Push*.
- `context`: bodies (5): Background, WithCancel, WithCancelCause, WithoutCancel, cancelCtx.Done.
- `encoding/binary`: bodies (1): littleEndian.PutUint32.
- `encoding/json`: names only (1): Marshal.
- `errors`: bodies (1): New; trusted model (1): Is*; names only (2): As, Join.
- `fmt`: trusted model (3): Errorf*, Printf*, Sprintf*; names only (2): Fprintf, Sprint.
- `github.com/go-logr/logr`: names only (3): Logger.Error, Logger.Info, Logger.V.
- `github.com/prometheus/client_golang/prometheus`: names only (2): counter.Inc, gauge.Inc.
- `golang.org/x/time/rate`: names only (4): Limiter.AllowN, Limiter.Reserve*, NewLimiter*, Reservation.Delay*.
- `hash/fnv`: names only (4): New32a, sum32a.Reset, sum32a.Sum32, sum32a.Write.
- `k8s.io/api/apps/v1`: names only (13): ControllerRevision.DeepCopy, ControllerRevision.DeepCopyObject*, ControllerRevisionList.DeepCopyObject, DaemonSet.DeepCopy, DaemonSet.DeepCopyObject*, DaemonSetList.DeepCopyObject, Deployment.DeepCopyObject, DeploymentList.DeepCopyObject, ReplicaSet.DeepCopyObject, ReplicaSetList.DeepCopyObject, Resource, StatefulSet.DeepCopyObject, StatefulSetList.DeepCopyObject.
- `k8s.io/api/core/v1`: names only (51): Binding.DeepCopyObject, ComponentStatus.DeepCopyObject, ComponentStatusList.DeepCopyObject, ConfigMap.DeepCopyObject, ConfigMapList.DeepCopyObject, Endpoints.DeepCopyObject, EndpointsList.DeepCopyObject, Event.DeepCopyObject, EventList.DeepCopyObject, LimitRange.DeepCopyObject, LimitRangeList.DeepCopyObject, List.DeepCopyObject, Namespace.DeepCopyObject, NamespaceList.DeepCopyObject, Node.DeepCopyObject*, NodeList.DeepCopyObject, NodeProxyOptions.DeepCopyObject, ObjectReference.DeepCopyObject, ObjectReference.GetObjectKind, ObjectReference.GroupVersionKind, PersistentVolume.DeepCopyObject, PersistentVolumeClaim.DeepCopyObject, PersistentVolumeClaimList.DeepCopyObject, PersistentVolumeList.DeepCopyObject, Pod.DeepCopyObject*, PodAttachOptions.DeepCopyObject, PodExecOptions.DeepCopyObject, PodList.DeepCopyObject, PodLogOptions.DeepCopyObject, PodPortForwardOptions.DeepCopyObject, PodProxyOptions.DeepCopyObject, PodSpec.DeepCopy, PodTemplate.DeepCopyObject, PodTemplateList.DeepCopyObject, PodTemplateSpec.DeepCopy, RangeAllocation.DeepCopyObject, ReplicationController.DeepCopyObject, ReplicationControllerList.DeepCopyObject, Resource, ResourceQuota.DeepCopyObject, ResourceQuotaList.DeepCopyObject, Secret.DeepCopyObject, SecretList.DeepCopyObject, SerializedReference.DeepCopyObject, Service.DeepCopyObject, ServiceAccount.DeepCopyObject, ServiceAccountList.DeepCopyObject, ServiceList.DeepCopyObject, ServiceProxyOptions.DeepCopyObject, Toleration.MatchToleration, Toleration.ToleratesTaint.
- `k8s.io/apimachinery/pkg/api/errors`: bodies (5): NewAlreadyExists*, NewBadRequest*, NewNotFound*, NewResourceExpired*, NewTimeoutError*; names only (13): FromObject, HasStatusCause, IsAlreadyExists, IsGone, IsInternalError, IsInvalid, IsNotFound, IsResourceExpired, IsTimeout, IsTooManyRequests, NewConflict*, NewInternalError*, StatusError.Status.
- `k8s.io/apimachinery/pkg/api/meta`: names only (6): Accessor, ExtractList, ExtractListWithAlloc, LenList, ListAccessor, SetList.
- `k8s.io/apimachinery/pkg/api/validation`: not translated (1): NameIsDNSSubdomain.
- `k8s.io/apimachinery/pkg/apis/meta/internalversion`: not translated (2): List.DeepCopyObject, ListOptions.DeepCopyObject.
- `k8s.io/apimachinery/pkg/apis/meta/v1`: bodies (19): Now*, ObjectMeta.GetAnnotations*, ObjectMeta.GetCreationTimestamp*, ObjectMeta.GetDeletionTimestamp*, ObjectMeta.GetFinalizers*, ObjectMeta.GetGenerateName*, ObjectMeta.GetLabels*, ObjectMeta.GetName*, ObjectMeta.GetNamespace*, ObjectMeta.GetResourceVersion*, ObjectMeta.GetUID*, ObjectMeta.SetCreationTimestamp*, ObjectMeta.SetDeletionGracePeriodSeconds*, ObjectMeta.SetDeletionTimestamp*, ObjectMeta.SetName*, ObjectMeta.SetNamespace*, ObjectMeta.SetResourceVersion*, ObjectMeta.SetUID*, Time.Equal*; names only (31): APIGroup.DeepCopyObject, APIGroupList.DeepCopyObject, APIResourceList.DeepCopyObject, APIVersions.DeepCopyObject, CreateOptions.DeepCopyObject, DeleteOptions.DeepCopyObject, GetControllerOf, GetControllerOfNoCopy, GetOptions.DeepCopyObject, InternalEvent.DeepCopyObject, InternalEvent.GetObjectKind, LabelSelectorAsSelector, List.DeepCopyObject, ListMeta.GetResourceVersion, ListMeta.GetShardInfo, ListMeta.SetRemainingItemCount, ListOptions.DeepCopyObject, NewControllerRef, PartialObjectMetadata.DeepCopyObject, PartialObjectMetadataList.DeepCopyObject, PatchOptions.DeepCopyObject, Status.DeepCopyObject, Table.DeepCopyObject, TableOptions.DeepCopyObject, Time.Before, Time.IsZero, TypeMeta.GetObjectKind, TypeMeta.GroupVersionKind, UpdateOptions.DeepCopyObject, WatchEvent.DeepCopyObject, WatchEvent.GetObjectKind.
- `k8s.io/apimachinery/pkg/apis/meta/v1/unstructured`: names only (24): Unstructured.DeepCopyObject, Unstructured.GetAnnotations, Unstructured.GetCreationTimestamp, Unstructured.GetDeletionTimestamp, Unstructured.GetFinalizers, Unstructured.GetGenerateName, Unstructured.GetKind, Unstructured.GetLabels, Unstructured.GetName, Unstructured.GetNamespace, Unstructured.GetObjectKind, Unstructured.GetResourceVersion, Unstructured.GetUID, Unstructured.GroupVersionKind, Unstructured.SetCreationTimestamp, Unstructured.SetDeletionGracePeriodSeconds, Unstructured.SetDeletionTimestamp, Unstructured.SetName, Unstructured.SetNamespace, Unstructured.SetResourceVersion, Unstructured.SetUID, UnstructuredList.DeepCopyObject, UnstructuredList.GetObjectKind, UnstructuredList.GroupVersionKind.
- `k8s.io/apimachinery/pkg/apis/meta/v1beta1`: not translated (1): PartialObjectMetadataList.DeepCopyObject.
- `k8s.io/apimachinery/pkg/fields`: names only (6): AndSelectors, Nothing, OneTermEqualSelector, OneTermNotEqualSelector, andTerm.Matches, nothingSelector.Matches.
- `k8s.io/apimachinery/pkg/labels`: names only (12): Everything*, MatchesNothing, NewRequirement, NewSelector, Nothing, SelectorFromSet, internalSelector.Add, internalSelector.Empty, internalSelector.Matches, nothingSelector.Add, nothingSelector.Empty, nothingSelector.Matches.
- `k8s.io/apimachinery/pkg/runtime`: names only (3): TypeMeta.GetObjectKind, TypeMeta.GroupVersionKind, Unknown.DeepCopyObject.
- `k8s.io/apimachinery/pkg/runtime/schema`: names only (7): GroupResource.String, GroupVersion.String, GroupVersionKind.Empty, GroupVersionKind.GroupVersion, GroupVersionKind.String, GroupVersionResource.Empty, emptyObjectKind.GroupVersionKind.
- `k8s.io/apimachinery/pkg/runtime/serializer/protobuf`: not translated (1): errNotMarshalable.Status.
- `k8s.io/apimachinery/pkg/util/diff`: not translated (1): ObjectGoPrintSideBySide.
- `k8s.io/apimachinery/pkg/util/errors`: names only (2): Flatten, NewAggregate.
- `k8s.io/apimachinery/pkg/util/intstr`: names only (2): FromInt32*, GetScaledValueFromIntOrPercent.
- `k8s.io/apimachinery/pkg/util/json`: names only (2): Marshal, Unmarshal.
- `k8s.io/apimachinery/pkg/util/naming`: names only (1): GetNameFromCallsite.
- `k8s.io/apimachinery/pkg/util/net`: not translated (1): IsConnectionRefused.
- `k8s.io/apimachinery/pkg/util/rand`: names only (1): SafeEncodeString.
- `k8s.io/apimachinery/pkg/util/resourceversion`: bodies (1): CompareResourceVersion*.
- `k8s.io/apimachinery/pkg/util/runtime`: names only (5): HandleCrashWithContext, HandleCrashWithLogger*, HandleError, HandleErrorWithContext, HandleErrorWithLogger.
- `k8s.io/apimachinery/pkg/util/sets`: bodies (8): KeySet, List, Set.Delete*, Set.Has*, Set.HasAny, Set.Insert*, Set.Intersection, Set.Len*.
- `k8s.io/apimachinery/pkg/util/validation/field`: names only (6): Invalid, NotSupported, Path.Child, Path.Index, ToPath, WithPath.
- `k8s.io/apimachinery/pkg/util/wait`: names only (13): Backoff.DelayFunc, Backoff.DelayWithReset, ContextForChannel, DelayFunc.Until, Group.Start, Group.StartWithChannel, Group.StartWithContext, Group.Wait, PollImmediateUntil, Until, UntilWithContext, backoffManager.Step, channelContext.Done.
- `k8s.io/apimachinery/pkg/watch`: names only (5): Filter, filteredWatch.ResultChan, filteredWatch.Stop, functionFakeRuntimeObject.DeepCopyObject, functionFakeRuntimeObject.GetObjectKind.
- `k8s.io/apimachinery/third_party/forked/golang/reflect`: not translated (1): Equalities.DeepEqual.
- `k8s.io/client-go/pkg/apis/clientauthentication`: not translated (1): ExecCredential.DeepCopyObject.
- `k8s.io/client-go/pkg/apis/clientauthentication/v1`: not translated (1): ExecCredential.DeepCopyObject.
- `k8s.io/client-go/pkg/apis/clientauthentication/v1beta1`: not translated (1): ExecCredential.DeepCopyObject.
- `k8s.io/client-go/tools/clientcmd/api`: not translated (3): Config.DeepCopyObject, Config.GetObjectKind, Config.GroupVersionKind.
- `k8s.io/client-go/tools/pager`: not translated (3): ListPager.ListWithAlloc, New, SimplePageFunc.
- `k8s.io/client-go/tools/record`: names only (7): NewBroadcaster, WithContext, eventBroadcasterImpl.NewRecorder, eventBroadcasterImpl.Shutdown, eventBroadcasterImpl.StartRecordingToSink, eventBroadcasterImpl.StartStructuredLogging, recorderImplLogger.Eventf.
- `k8s.io/client-go/util/consistencydetector`: names only (2): CheckDataConsistency, IsDataConsistencyDetectionForWatchListEnabled.
- `k8s.io/client-go/util/watchlist`: names only (1): DoesClientNotSupportWatchListSemantics.
- `k8s.io/component-base/featuregate`: names only (2): featureGate.Enabled, featureGate.SetFromMap.
- `k8s.io/component-base/metrics`: names only (3): CounterVec.WithLabelValues, kubeRegistry.MustRegister, noopMetric.Inc.
- `k8s.io/klog/v2`: names only (7): Background*, FromContext, KObj, KRef, LoggerWithName, TODO, Warningln.
- `k8s.io/utils/buffer`: not translated (3): NewRingGrowing, TypedRingGrowing.ReadOne, TypedRingGrowing.WriteOne.
- `k8s.io/utils/clock`: names only (9): RealClock.After, RealClock.NewTicker*, RealClock.NewTimer*, RealClock.Now*, RealClock.Since, realTicker.C*, realTicker.Stop*, realTimer.C*, realTimer.Stop*.
- `k8s.io/utils/dump`: names only (1): ForHash.
- `k8s.io/utils/ptr`: names only (2): Deref, To.
- `k8s.io/utils/trace`: names only (3): New, Trace.LogIfLong, Trace.Step.
- `math`: names only (2): Ceil*, Pow*.
- `math/rand`: names only (5): Float64, Int63n*, New, NewSource, Rand.Float64.
- `os`: names only (1): LookupEnv.
- `reflect`: names only (11): DeepEqual, TypeOf*, Value.Elem, Value.IsNil, Value.Pointer, Value.Type*, ValueOf*, rtype.Kind, rtype.Name, rtype.PkgPath, rtype.String.
- `runtime`: names only (2): Func.Name, FuncForPC.
- `sort`: bodies (1): Sort*.
- `strconv`: names only (3): FormatUint*, ParseBool*, ParseInt*.
- `strings`: trusted model (2): Join*, Split; names only (2): Contains*, LastIndexByte.
- `sync`: bodies (16): Cond.Broadcast, Cond.Signal, Cond.Wait, NewCond, Once.Do, RWMutex.Lock, RWMutex.RLock, RWMutex.RLocker, RWMutex.RUnlock, RWMutex.Unlock, WaitGroup.Add, WaitGroup.Done, WaitGroup.Go, WaitGroup.Wait, rlocker.Lock, rlocker.Unlock; trusted model (2): Mutex.Lock, Mutex.Unlock.
- `sync/atomic`: bodies (5): Bool.Load, Bool.Store, Int64.Add, Int64.Load, Pointer.Load; trusted model (4): AddInt64, LoadInt64, Value.Load, Value.Store.
- `time`: bodies (7): Since, Time.Add, Time.After*, Time.Before, Time.Equal, Time.Sub, Time.UnixNano; trusted model (2): After, Sleep; names only (5): Duration.Nanoseconds, Duration.Seconds*, Now, Time.Compare, Time.IsZero*.
