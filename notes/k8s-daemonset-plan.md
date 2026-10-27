# Plan: the Kubernetes DaemonSet controller (`k8s.io/kubernetes/pkg/controller/daemon`)

Status: planning (2026-10-26, branch `daemonset-plan`). Decisions: D49 in `notes/decisions.md`
(the cut: model the API server at the typed clientset, verify client-go's leaf libraries and
informers). Nothing proved yet. (2026-10-26, branch `k8s-clientgo-leaf`) Phase 1's leaf-library
half is translated: `notes/k8s-clientgo-goose.md` (gaps C1-C7). (2026-10-27, branch
`k8s-daemonset-proof`) The pin (`k8s.io/kubernetes` `878cfa6c4cc7`), `Main` (`examples/k8sdaemonset/dsmain`)
and phase 1's controller half: `notes/k8s-daemonset-goose.md` (gaps D1, D2; the call graph of `Main`).

## Goal

Prove safety properties of the real DaemonSet controller, running over a model of the Kubernetes
API server, in every execution. The first property is the one the controller robustness test
checks (kubernetes/kubernetes#139657, open; at its head `13ecb9cc`, 2026-10-26:
`test/integration/daemonset/robustness_test.go:123`, in `TestDaemonSetReconcileRobustnessMatrix`
(line 39), the PR's only DaemonSet test):

- **S1, `MaxOnePodPerNode`.** At no time does the API server hold two pods of the DaemonSet
  bound to the same node. The test checks it by listing pods every 50 ms under a fault matrix
  (409s, injected 500s, a stalled watch, a stale pod cache, the expectations clock jumped past
  `ExpectationsTimeout`). Its `ExpectationsTimeout` scenario is the interesting one: with
  expectations expired and the pod cache stale, only the consistency store (KEP-5647,
  `StaleControllerConsistencyDaemonSet`, beta and on by default since 1.36) keeps the controller
  from creating a second pod.

The result is a closed theorem in the style of `k8setcd3_safe` (`dsonepod_safe`): a Go program in
`examples/` starts the model API server, the real informers over its List/Watch, and the real
controller, then keeps checking S1 and panics if it fails. Adequacy gives: no thread panics or is
stuck. The proof covers every interleaving and every nondeterministic choice of the model, so the
test's fault scenarios are cases of the theorem, not code to verify (except `StaleRead`, a cache that
lies about its contents while reporting a fresh resource version, which no real informer does).

Candidates after S1 (decide once S1's invariant is written down):
- S2: every pod the controller creates is bound (by node affinity) to a node that should run it.
- S3: the controller deletes only pods it owns.
- S1 for N nodes and several DaemonSets (S1's first statement: one node, one DaemonSet).

The test's other assertions are not safety properties: its liveness invariant
(`DaemonSetStatusUpdated`, `Status.CurrentNumberScheduled == 1` once the controller settles, within
30 s) is bounded-time convergence, and the framework's `AssertAllFaultsMatched`/
`AssertExpectedFaultsTriggered` check the harness, not the controller. The other test the
framework sets up, `test/integration/node/robustness_test.go` (the node lifecycle controller's
`NodeAlwaysReady`), is out of scope here.

The robustness PR's own code (`test/utils/robustness`, its clock injection in
`controller_utils.go`) is not needed: the consistency store and the controller are on Kubernetes'
master already. Pin a master commit (phase 0), not the PR. Master moved under the PR: between
its heads `167a0539` and `13ecb9cc` (rebased, 2026-10-26) the consistency store moved from
`pkg/controller/util/consistency` to client-go, `k8s.io/client-go/util/consistency`, with two
changes that matter here: `EnsureReady` now reports not ready when a store has no resource
version yet (`""`: not synced, or `AtomicFIFO` off) or when no store is registered for a recorded
resource, where it used to let the sync through; and `WroteAt` ignores a resource version it cannot
parse. The precondition is now on the interface too (`consistency.go:44`). Pin a commit with the
move.

## The cut (D49)

The controller's whole interface to Kubernetes is its constructor
(`daemon_controller.go:158`): four informers (DaemonSet, ControllerRevision, Pod, Node), a
`clientset.Interface`, a `*flowcontrol.Backoff`. Of client-go, the controller's closure uses 14
packages (125 objects, found with the type checker: only `pkg/controller/daemon`,
`pkg/controller` and `pkg/features` import client-go). Every call to the API server goes
through `k8s.io/client-go/rest`, which only the typed clients reach (the informers reach it
through the `ListWatch` closures that call the typed clients' `List`/`Watch`; the recorder at its
event sink). So:

| Layer | Packages | Treatment |
|---|---|---|
| The API server | `kubernetes`, `kubernetes/typed/{apps,core}/v1` (and `rest`, HTTP, kube-apiserver behind them) | **Modeled**: a Go model in the example, verified against its own spec (below). Its spec is the trusted statement of the API server's semantics. |
| Informers | `tools/cache`: `reflector.go`, `the_real_fifo.go`, `controller.go`, `shared_informer.go`; `informers/{apps,core}/v1` (glue) | **Verified**, against the model's List/Watch spec. |
| Leaf libraries | `util/workqueue`; `util/consistency` (the consistency store); `tools/cache`'s `store.go`, `thread_safe_store.go`, `index.go`, keys, `WaitForNamedCacheSyncWithContext`; `listers/{apps,core}/v1`; `util/flowcontrol` (`Backoff`); `util/retry`; `features` | **Verified** directly. |
| Events | `tools/record`, `kubernetes/scheme` | **Trusted no-op** or verified over a no-op sink (events do not affect safety; phase 1 decides). |
| The controller | `pkg/controller/daemon`, `daemon/util`, `daemon/metrics`; `pkg/controller` (`controller_utils.go`, `controller_ref_manager.go`); `pkg/api/v1/pod`, `pkg/apis/core/v1/helper`, `pkg/util/{labels,hash}` | **Verified**. |
| Below | `k8s.io/api` (types, generated `DeepCopy`), apimachinery helpers, `component-helpers` (node affinity, taints), `apiserver/pkg/util/feature`, `component-base/{featuregate,metrics}`, `klog`, `k8s.io/utils/clock` | Verified where cheap; trust-boundary specs where not (phase 1 sorts them). |

Not a goal: replacing the model by the real API server. The repository's etcd3 store proofs
(`notes/k8s-etcd3-plan.md`) cover only its unary methods; its `GetList` and watcher do not
translate yet (gaps G2, G1), and kube-apiserver's handlers, registry, admission and serialization
are far larger. A later bridge (the model's spec implemented by the etcd3 store) is possible but
out of scope.

## The model API server

One shared state under a mutex: per resource (pods, nodes, daemonsets, controllerrevisions) a map
from namespace/name to object, a global resource-version counter, and the log of changes (for
watches). Operations, at the typed clients' signatures:

- What the controller calls: `Pods(ns).Create`/`Delete`; `ControllerRevisions(ns).Create`/`Get`;
  `DaemonSets(ns).Get`/`UpdateStatus`; `Events(ns)` (empty).
- What the informers call: `List` (a consistent snapshot and its resource version) and `Watch`
  from a resource version (every later change in order, as `watch.Interface` events), for the
  four resources.
- The rest of the typed interfaces: absent (the model defines its own interfaces with only these
  methods; a replacement module `k8s.io/client-go` via `go.mod` `replace`, or the typed packages
  only, phase 0 decides). Methods `pkg/controller` names but this scenario never reaches
  (`Pods.Patch`, `ControllerRevisions.Update/Delete/Patch`, `ReplicaSets.Patch`,
  `Nodes().Get/Patch`): `panic("unreachable")`, which the no-panic proof shows unreached.

Semantics:
- A write either takes effect at once (a fresh resource version; a create also gets a name from
  `GenerateName` and a UID; the stored object is returned) or returns an error and has no effect,
  chosen nondeterministically (`primitive.RandomUint64`). Conflicts (409) when the resource
  version given is not the current one.
- A watch may end, or fail with "too old resource version", at any time; the reflector relists.
- Objects are stored defaulted (the controller dereferences `Spec.RevisionHistoryLimit` and
  assumes a RollingUpdate strategy): `Main` creates them defaulted, or the model defaults them.
- No timing: `AddAfter`, rate limiting and watch lag are goroutines the scheduler runs whenever.

Configuration in `Main`: client-go's `WatchListClient` off (the reflector then lists and watches;
with it on the initial list is a streaming watch ending in a bookmark, more for the model),
`AtomicFIFO` on (without it `LastStoreSyncResourceVersion` returns `""`; the client-go store then
reports not ready forever after a write, safe but stuck), `StaleControllerConsistencyDaemonSet` on.

Line numbers below are at the PR's head `13ecb9cc`.

## How S1 is kept (the proof's skeleton)

The controller is the only writer of pods in the example. A sync of a DaemonSet:
1. `consistencyStore.EnsureReady` (`daemon_controller.go:1302`): if the controller recorded a write
   (`WroteAt`, after each successful pod create and status write) whose resource version the
   pod or DaemonSet informer's store has not reached, requeue. Otherwise clear the record.
2. Read the pods from the informer's cache; create one for each node that should run one and has
   none in the cache (`manage` → `syncNodes`), waiting for every create (`createWait.Wait`) before
   returning.

The invariant to establish: at the start of a sync that passes step 1, the pod cache contains
every pod of the DaemonSet the server holds. It rests on
- **the workqueue's exclusivity**: one worker per key, so no `WroteAt` for the DaemonSet runs
  during its `EnsureReady` (the store's stated precondition, client-go's `consistency.go:44,150`,
  "Must not be called concurrently with WroteAt for the same owner": its check and its `Clear` are
  not atomic, and
  a `WroteAt` between them would be lost);
- **the informer contract**: the store's `LastStoreSyncResourceVersion` never decreases, across
  relists too, and once it is at least `r` the store reflects every change up to `r`;
- **the model's write contract**: a failed write has no effect; a created pod's resource version is
  the one returned.

Expectations (`ControllerExpectations`) only make the controller more conservative; S1 should not
need them, though `SatisfiedExpectations` must be specified enough to show it does not panic.

**A bug outside the theorem's premise (confirmed in phase 0).** If a pod create is committed but
its call returns an error (a timeout after the commit), `syncNodes` lowers the expectations
(`CreationObserved`, `daemon_controller.go:1107`) and `OnWrite` never records a resource version.
A later sync on a pod cache that has not seen the pod then creates a second one. The robustness
test cannot reach this: its injected 500s are synthesized before the request is sent
(`test/utils/robustness/transport.go:110`). Reproduced over the model with
`Config.AmbiguousWrites` (`issues/k8s-daemonset-ambiguous-create-duplicate-pod.md`); the
theorem's program runs with it off, the premise "a failed write had no effect" (D50).

## Phases

0. **The example in Go.** **Model done** (2026-10-26, D50): `examples/k8sdaemonset` (a Go module
   at the client-go pin of `examples/k8setcd3/go.mod`), package `apimodel`: the model API server,
   trusted Go code (`doc.go` states its semantics and deviations), a `kubernetes.Interface` whose
   clients embed client-go's interfaces (nil) and implement what the controller and informers call:
   pods (Create, Get, List, Watch, Delete), nodes (Create, Get, List, Watch), daemonsets (Create,
   Get, List, Watch, UpdateStatus), controllerrevisions (Create, Get, List, Watch, Update, Delete),
   events (dropped). Its tests (`apimodel_test.go`, `-race`) include client-go's real informers
   converging over it under failures. `examples/k8sdaemonset/smoke` (build tag `k8ssmoke`, its
   `go.mod` generated from a Kubernetes checkout by `gen-gomod.py`) runs the real controller over it:
   no method the model lacks is called; with failures that have no effect, never two pods (0 of 30
   runs); with ambiguous writes, two pods in 4 of 50 runs (the suspected bug, confirmed).
   **Pin and `Main` done** (2026-10-27, branch `k8s-daemonset-proof`; `notes/k8s-daemonset-goose.md`):
   `examples/k8sdaemonset/go.mod` requires `k8s.io/kubernetes` at master `878cfa6c4cc7`
   (2026-10-21, the commit the repository's apiserver pin was published from), its staging modules
   replaced by their mirrors (the four shared pins, the others at their latest commit by
   2026-10-21T22:14Z; their Go files identical to `878cfa6c4cc7`'s staging). `dsmain.Main(checks)`:
   the feature gates set programmatically (`DefaultMutableFeatureGate.SetFromMap`: `WatchListClient`
   off, `AtomicFIFO` and `StaleControllerConsistencyDaemonSet` on; an environment variable would be
   ignored, `pkg/features`' init replaces client-go's gates), the model with every failure but
   `AmbiguousWrites`, the node and the (template-defaulted) DaemonSet created by the admin client,
   the real informer factory and `NewDaemonSetsController`, `Run` with two workers, and `checks`
   checks (a loop bound, not a context) panicking if two pods of the DaemonSet target one node.
   Its tests under `-race`: 300 runs of `Main(2000)`, no panic; the checker catches the known bug in 4 of 100 runs with `AmbiguousWrites`. The smoke test now builds in the module at
   the pin (no generated `go.mod`). Still open: the event recorder (`tools/record`, names only).
1. **The translation survey** (as `notes/k8s-etcd3-goose.md`). **Leaf libraries done**
   (2026-10-26, `notes/k8s-clientgo-goose.md`): in project `k8s-apiserver` (not a new project:
   `tools/cache` and apimachinery are shared with the KEP-6404 watch cache), with bodies
   `util/workqueue`, `util/consistency`, `util/flowcontrol` (`Backoff`), `util/retry`, `features`,
   `tools/cache`'s local half, the listers (DaemonSet, ControllerRevision, Node, Pod), apimachinery's
   `util/sets` and `util/resourceversion`; `k8s.io/api/{apps,core}/v1` types concrete (G4 done,
   cheap). Gaps: C1 (range over a string: `resourceversion.isWellFormed` names only), C2 (a generic
   struct's promoted methods through a pointer: the workqueue's `Get`/`Done`/... unfolds missing;
   **blocks phase 2's queue proofs until a Perennial fix and pin bump**), C3 (axiomatized alias,
   worked around), C4 (`min` on `time.Duration`: `Backoff.Next`, `threadSafeMap.Transaction` names
   only), C5 (`intstr.IntOrString` axiomatized), C6 (`cache.Object`'s `comparable`, for phase 4), C7 (`features`' initialization names only:
   its `Init.lean` would need hand-written steps).
   **Controller half done** (2026-10-27, branch `k8s-daemonset-proof`; `notes/k8s-daemonset-goose.md`):
   in project `k8s-daemonset`, with bodies `dsmain`, `pkg/controller/daemon{,/util,/metrics}`,
   `pkg/controller`, `pkg/api/v1/pod`, `pkg/apis/core/v1/helper`, `pkg/util/{labels,hash}`,
   `pkg/features` (its init names only, C7), `component-helpers/scheduling/corev1{,/nodeaffinity}`:
   248 of 265 functions; what they name names only (informers, `tools/record`, apimachinery's
   `equality`, `json`, `strategicpatch`, ..., in `k8s-apiserver`; `hash/fnv` in `etcd`). Gaps: D1
   (range over a function: `pod.VisitContainers`, unreached; fixed on Perennial's `lean`), **D2**
   (G3: an interface of a package the file does not import named through a same-named imported
   package, Kubernetes' `v1`s: `syncDaemonSet`, `RealPodControl.createPods`/`DeletePod`,
   `ComputeHash`, the node-affinity `Match`es and five patch/taint helpers names only; **blocks
   phase 5's S1 proof until a Perennial fix**, tried in a scratch translator: everything translates
   and elaborates without the substitution). The survey's hazards (`getPatch`'s JSON,
   `ComputeHash`'s spew, `reflect.DeepEqual`, `errors.As`, `fmt.Sprint`, `WaitGroup.Go`, `DeepCopy`,
   `MustRegister`, the handlers' assertions) all translate: they are boundary specs for the proofs.
   The call graph of `Main` (`etc/k8s-worklist.py`): 1020 functions, 623 in the verified layers (134
   of the controller, 125 with bodies; 312 of the informers, 74 with bodies), 397 at the boundary.
   Still to do in this phase: the informers' half of `tools/cache` (phase 4 translates it), the API
   types' `DeepCopy`. As first planned: a project `k8s-daemonset` in
   `etc/goose.py` translating the packages of "The cut" with bodies, the rest names-only, and a
   list of what the pinned Goose rejects (G-numbered, `notes/k8s-daemonset-goose.md`). Known in
   advance (from the call-graph survey, 2026-10-26):
   - `getPatch` (`update.go:505`, on every sync): `json.Marshal` of the DaemonSet, `Unmarshal` into
     `map[string]interface{}`, unchecked assertions on the result.
   - `controller.ComputeHash` (in `snapshot`): fnv over `spew`'s dump (reflection).
   - `reflect.DeepEqual` on the selector (every sync), `apiequality.Semantic.DeepEqual` in handlers.
   - `errors.As` (`syncDaemonSet`), `fmt.Sprint` whose result the logic compares (`IsPodUpdated`,
     the template-generation label).
   - `k8s.io/api`'s types concrete (G4 of the etcd3 survey: `translate_types` with what they
     name), their generated `DeepCopy`; `pkg/features`' init (a ~3000-line gate table, run at
     package init) and `component-base/featuregate`'s `Enabled`; `legacyregistry.MustRegister`
     (the repository has prometheus's registration facts, `prometheus.namesUnclaimed`).
   - Standard library: `sync.WaitGroup.Go` (translated in Perennial, no spec), `container/heap.Pop`
     (the repository has `Init`, `Push`, `Fix`), `strconv.ParseInt`, `hash/fnv`, `encoding/json`,
     `reflect`.
   For each gap: a trusted model (`TrustedCode/`), a Goose fork of the code (as `upamanyus/etcd`),
   or a Perennial change (`notes/perennial-changes.md`).
2. **The leaf libraries.** `util/workqueue` (the typed queue's spec: a per-key token held from
   `Get` to `Done`; the delaying queue; the rate limiters), `tools/cache`'s store, thread-safe map
   (with its resource version) and indexers, the listers, `flowcontrol.Backoff`, the consistency
   store (`k8s.io/client-go/util/consistency`), `ControllerExpectations`.
   *Status, `util/workqueue` (2026-10-27, branch `k8s-leaf-workqueue`):* linked in
   `Proof/k8s_io/client_go/util/workqueue/Link.lean` (results `Results.lean`, TCB
   `etc/tcb-collections/clientgo-workqueue.txt`). The typed queue proved: `Get` returns either
   `shutdownLb` (and the zero item) or the item's exclusive key token `keyTok γ k`, which `Done`
   consumes, so no two workers hold one key between `Get` and `Done` (the exclusivity S1 rests
   on); `Add`, `Len`, `ShuttingDown` (`true` gives `shutdownLb`), `ShutDown`/`ShutDownWithDrain`
   (each spends a shutdown token, `shutdownToks`), constructors for the default FIFO without
   metrics. The rate limiters proved (`When`'s bound: exponential `≤ maxDelay`, fast-slow `fast ∨
   slow`, bucket and max-of `≥ 0`; `DefaultTypedControllerRateLimiter`). The delaying and
   rate-limiting queues proved (`waitingLoop`, `AddAfter`, `AddRateLimited`, `Forget`,
   `NumRequeues`, `NewTypedRateLimitingQueueWithConfig` for an unconfigured or named queue) up to
   gap C2 (the promoted methods' specs are hypotheses, `notes/k8s-clientgo-goose.md`) and the
   waiting loop's deferred `HandleCrashWithLogger` (`sorry`, a Goose bug dropping a deferred call's
   variadic argument, `notes/perennial-changes.md`). Two bugs filed:
   `issues/k8s-workqueue-done-without-get-duplicates.md`,
   `issues/k8s-workqueue-exponential-backoff-2to63.md`. Not done: `TypedWithMaxWaitRateLimiter`,
   metrics other than the no-op ones, `SetProvider`, `parallelizer.go`.
   *Status, `util/consistency` (2026-10-27, branch `k8s-leaf-cache`):* every function proved, linked
   in `Proof/k8s_io/client_go/util/consistency/Link.lean` (results `Results.lean`, TCB
   `etc/tcb-collections/clientgo-consistency.txt`), over two trust-boundary axioms
   (`resourceversion.isWellFormed`, gap C1; `schema.GroupResource.String`). The store is logically
   atomic over `consState γ M` (`Proof/k8s_io/client_go/util/consistency/Model.lean`): `WroteAt`
   is `wroteAtM` (the newest well-formed version per group resource; a malformed one ignored),
   `Clear` is `clearM`, and `EnsureReady(o)` returns `nil` only with `readyRec S G (M !! o)`, the
   record then deleted: for every recorded `gr ↦ wroteRV`, a registered store's
   `LastStoreSyncResourceVersion()` returned `readRV ≠ ""` with the caller's contract `G gr readRV`
   and, **if `readRV` is well formed**, `wroteRV ≤ readRV` by value. What S1's proof must bring:
   permissions `T o q` with `tokExcl T` (from the work queue's `keyTok`: the worker holds `T o 1`
   for `EnsureReady`, and splits it for the create goroutines' `WroteAt`, rejoined at
   `createWait.Wait`), reader slots, a `G` that implies `readRV` well formed and "the informer has
   seen every change up to `readRV`" (stable, the informer contract), and that every recorded
   version is a created object's (well formed). `Clear` needs no permission (the delete handler's)
   and forgets the owner's writes: an invariant "every write is seen or recorded" holds for live
   owners only.
   *Status, `tools/cache`'s thread-safe store (2026-10-27, branch `k8s-leaf-cache`):* linked in
   `Proof/k8s_io/client_go/tools/cache/Link.lean` (`etc/gen-link.py --k8scache`; results
   `Results.lean`, TCB `etc/tcb-collections/clientgo-cache.txt`), no `sorry`, one trust-boundary
   axiom (`strconv.ParseInt`, the resource-version metric only). `threadSafeMap`'s `Get`, `List`,
   `ListKeys`, `ByIndex` (readers, one reader slot `tsReader` each) and `Add`, `Update`, `Delete`,
   `DeleteWithObject`, `Replace`, `Bookmark` (writers) are logically atomic over `storeSt γ σ`
   (`StoreModel.lean`: items, resource version `rv`, indexers named by index into the client's
   family `Fam`); `NewThreadSafeStore` (no options) hands out the state and all reader slots. The
   indices are exact (`ixOk`, kept by `updateSingleIndex`/`updateIndices`): `ByIndex(n, v)` returns
   exactly the items `k` with `v ∈ Fam j (obj k)` (`inIdx`, nil objects never indexed), each once.
   **`rv` is not monotone**: `Add`/`Update`/`DeleteWithObject` set it to the object's whenever its
   accessor has one, `Replace`/`Bookmark` to the given string (even `""`), `Delete` keeps it. Premises
   the client discharges: `OK` (persistent, on stored objects), index functions' contracts
   (`fnOk`: no error, values `F o`), the accessor's (`rvAcc`, apimachinery's `meta.Accessor` and
   `GetResourceVersion`, typed-nil objects excluded). Store keys: `ObjectName.String`,
   `SplitMetaNamespaceKey` (round trip `splitKey_nameKey`). Not done: the `cache` wrapper
   (`store.go`: key functions, `NewIndexer`), `Index` (the namespace lister's path), `AddIndexers`
   (the DS controller's node-name index; changes `fnIds`), `Transaction` (C4; the AtomicFIFO
   informer's write path), `IndexKeys`, `ListIndexFuncValues`, `GetIndexers` (unlocked read),
   `LastStoreSyncResourceVersion` (feature gates, C7), options/metrics providers.
   **C2 follow-up waits on the Perennial bump** (2026-10-27): the Goose fix for C2 is on
   Perennial's `lean` (`ddb0a1239`, Case 18 of its `fix-semantics` examples); the user does the
   pin bump elsewhere (`f73703285` on etcd-grove's `lean` -> a commit with `ddb0a1239`). After it
   lands on `lean`: merge `lean` into the DaemonSet branches, drop the promoted-method exclusions
   in `Code/k8s_io/client_go/util/workqueue.toml`, regenerate, and prove the 14 promoted methods
   (forwards to the proved ones; now hypotheses in the workqueue's `Link.lean`).
3. **The model API server's spec and proof.** Logically atomic triples over an abstract state of
   resources and its change log (compare D44-D48's KV state and its watches: a watch is repeated
   reads of the log). The specs are an internal layer of the controller's proof: the Go model
   stays the trust base (D50's last paragraph).
   *Status (2026-10-27, branch `k8s-daemonset-proof`; `notes/k8s-apimodel-goose.md`):* translated
   (project `k8s-daemonset` in `etc/goose.py`; client-go's typed interfaces names-only in
   `k8s-apiserver`), specified (63 specs, `Spec/.../k8sdaemonset/apimodel/`) and linked
   (`etc/gen-link.py --apimodel`; results `Results.lean`, TCB `etc/tcb-collections/k8s-apimodel.txt`).
   The abstract state `St` (`State.lean`): the last version issued, the UIDs issued, per resource
   the stored objects and the change log, well formed (`St.wf`: versions increasing along each log,
   at most `rev`; logged objects of the table's resource, at their version, with an issued UID;
   the stored objects the log's replay); a history of states (`apiState γ σ` the clients' half).
   **Proved**: `NewServer` (the empty state), the server's `create`, `get`, `list`, `update`,
   `remove` (each linearizing under the lock: a write appends a later well-formed state,
   `St.write_wf`; a check's error or a read at the locked state; a flagged failure or a
   request-only check at any state), `watch` (over the watcher goroutine's spec: the watch's start
   checked and registered, the result channel an SPSC whose events are steps of a cursor along the
   log), the watch's `Stop` and `ResultChan`, `podGrace`, `int32PtrEqual`, the typed clients' `Get`,
   `Create`, `List`, `UpdateStatus`, `Update`, `Delete`, `Watch` over them (the caller's update
   passed on, `au_mono`), the clientsets. **Not proved yet** (specified; `links_pending`
   hypotheses): the watcher's goroutine `watcher.run` (its precondition `runPre` is what `watch`
   proves it hands it; `send` needs a `select` over two SPSC channels), `preparePod`,
   `prepareDaemonSet` (C5), `updateDaemonSetStatus`, `daemonSetStatusEqual`. `copyObject` is a
   `sorry` (gap C8, the pinned translation's interface assertion: fixed by the Perennial bump, or by
   the proposed type switch, a TCB change not applied). No infidelity found in the model.
4. **The informers.** The reflector (list, watch, relist, bookmarks; watch-list off), the FIFO, the
   shared informer's processor and listeners, `WaitForNamedCacheSyncWithContext`: the informer
   contract above, plus the handlers' delivery (in order, with the objects' concrete types, which
   every handler's unchecked assertion needs). The hardest phase.
   *Status, translation (2026-10-27, branch `k8s-daemonset-proof`; `notes/k8s-daemonset-goose.md`,
   "The informers"):* `tools/cache` with bodies (the reflector, `RealFIFO`, the controller, the
   shared informer, processor, listeners), `tools/pager`, `synctrack`, `k8s.io/utils/buffer`, the
   factory and `informers/{apps,core}/v1`: 288 of the 312 informer functions `Main` reaches. Gaps:
   D3 (`RealFIFO.PopBatch`, C4's `min`) with C4 (`Transaction`): the batch path, which `Main`'s
   gates select (`InOrderInformersBatchProcess` on by default); D4 (`handleAnyWatch`'s labeled
   `break`); C2 (the typed informers' promoted methods, every call the controller makes on an
   informer); D2 (the typed informers' list-watch closures).
   *Status, proofs (2026-10-27, branch `k8s-daemonset-proof`):* linked in
   `Proof/k8s_io/client_go/tools/cache/Link.lean` (results `Results.lean`, TCB
   `etc/tcb-collections/clientgo-informers.txt`), no `sorry`. **The informer contract, pure**
   (`InformerModel.lean`, proved): the store is `tableAt log v` at its version `v`; versions are
   monotone across relists (a relist lists the model's current state, at a version at least the last
   seen); a deletion keeps the version; `HasSynced` follows the first `Replace` popped and
   processed. Its premise specific to the model: the model starts at version 1, so a list's version is
   never `"0"` (a watch from `""`/`"0"` would replay synthetic `ADDED`s in map order). **The store**
   (`store.go`'s `cache` over the thread-safe store): `Add`, `Update`, `Delete`, `Replace`,
   `Bookmark`, `Get`, `GetByKey`, `List`, `ListKeys`, `ByIndex`, `Index`, `Resync`,
   `LastStoreSyncResourceVersion` (premise: the `AtomicFIFO` gate on). **The FIFO** (`RealFIFO`,
   atomic events; `FIFODefs.lean`: the queue's state `FQ` behind an invariant, the client's half
   `fifoSt γ q`, the synced channel broadcasting `fifoSyncedLb`): the producers `Add`, `Update`,
   `Delete`, `Replace`, `Bookmark`, `Close`, `IsClosed`, `HasSynced` logically atomic; the single
   consumer's `Pop` with two linearization points (`popAU`: the head delta removed, or
   `ErrFIFOClosed` on an empty closed queue; `doneAU`: one initial item fewer after processing,
   `FQ.popDone`), the processing in between with the lock released when `unlockWhileProcessing`
   (`whileProcessing_locked`).
   *Status, proofs, second round (2026-10-27, branch `k8s-daemonset-proof`, phase C2):* no `sorry`
   added. **Keys and resource versions per call** (refactor): a pure key function or `rvOf` fixed in
   advance cannot describe heap-allocated objects, so `cache`'s `Add`/`Update`/`Delete`/`Get`/
   `Replace` take `keyOk D kf KF` and `rvAcc D rvOf` over the objects `D` of that call; `isCache`
   exposes the key function `kf`; the FIFO's `isFIFO f γ OK` drops `KF`. **The indexers**:
   `AddIndexers` (re-indexing every item, `St.addIx`; the name-clash and non-empty-store errors),
   `GetIndexers`; sets' `KeySet`, `List`, `HasAny`, `Intersection`, `UnsortedList`, `New`;
   `fmt.Errorf` with a `Set[string]` argument (`ErrorfSet.lean`). **The processing of a delta**:
   `processDeltas` (non-batch), `processReplacedAllInfo`, `reconcileReplacement` over the store's
   exclusive writer `storeWriter γ SW` and a handler contract `handlerOk OK h H` (`InformerDefs.lean`:
   the events `Ev`, `stepFD`); `sharedIndexInformer.handleDeltas` (under `blockDeltas`, the informer as
   its handler: `handlerOk` a premise). **The controller loop**: `controller.processLoop` on the
   single-delta path, premises `gateOff` (the gate `InOrderInformersBatchProcess` reads `false`: the
   batch path is taken iff the queue is a `QueueWithBatch` (the `RealFIFO` is), `ProcessBatch ≠ nil`
   (the shared informer sets it) and the gate is on) and `errIsOk` (`errors.Is(err, ErrFIFOClosed)`
   returns: the package fact says only that `ErrFIFOClosed` holds some error, and `Pop`'s spec not
   which error it returns once closed). **The listers**: `ListAll`, `ListAllByNamespace`, the
   generic `ResourceIndexer`'s `Get`/`List`, `listers.New`/`NewNamespaced`, and the typed listers of
   `Main`'s four informers (`NewDaemonSetLister`, `DaemonSets`, `NewControllerRevisionLister`,
   `ControllerRevisions`, `NewPodLister`, `Pods`, `NewNodeLister`, the namespace listers' and the
   node lister's promoted `Get`/`List`), linked in `Proof/k8s_io/client_go/informers/Link.lean`
   (`etc/gen-link.py --k8sinformers`); new boundary axioms `apps/v1.Resource`, `core/v1.Resource`
   (names-only, specified as returning some `GroupResource`). One client-go bug filed
   (`issues/k8s-clientgo-getindexers-unlocked-map.md`, a data race).
   **Not done:** the reflector (`ListAndWatch`, its watch loop D4), the shared processor and
   listeners (`distribute`, `processorListener.add`/`pop`/`run`, the informer's
   `OnAdd`/`OnUpdate`/`OnDelete`, i.e. `handleDeltas`'s `handlerOk`; `AddEventHandlerWithOptions`,
   per-handler `HasSynced`), `GetPodDaemonSets`/`GetHistoryDaemonSets` (label selectors),
   `IndexKeys`/`ListIndexFuncValues` (unreached by `Main`), the factory and typed informers (C2/D2),
   the informer contract's assembly (the invariant tying the FIFO's queue, the store through
   `storeWriter` and `InformerModel`); `PopBatch`/`Transaction` (D3/C4: the path `Main`'s default
   gates select, so either `Main` turns `InOrderInformersBatchProcess` off or C4 is fixed in
   Perennial first). ~~Decision needed: the index functions `Fam` are pure functions of the
   interface value~~ (approved and done in the third round, below).
   *Status, proofs, third round (2026-10-27, branch `k8s-daemonset-proof`, phase C3):* **index
   values per item**: `Fam` is a family of relations between an object and its values
   (`StoreDefs.lean`'s `Fn`, functional), the store's lock invariant records each item's values per
   indexer (`IV`, `itemsIv`, `ivWf`), and the queries (`ByIndex`, `Index`, `ListAllByNamespace`, the
   listers' `List`) return the relation's facts for the items they select (`idxSel`); every writer's
   spec unchanged; no axiom or `sorry` added (`notes/STATUS.md`, "The informers, third round").
   *Third round, continued:* the listeners (`processorListener.add`/`pop`/`run`), the processor's
   `distribute`, the informer's `OnAdd`/`OnUpdate`/`OnDelete` (discharging `processDeltas`'
   `handlerOk`), `synctrack`'s `Start`/`Finished`, and `GetPodDaemonSets`/`GetHistoryDaemonSets`
   over a label-selector boundary (`LabelSelectorAsSelector`, `Everything` axioms) proved; the ring
   buffer pending; one `sorry` for G-defer-variadic. Open: `AddEventHandlerWithOptions`,
   `HasSynced`, the processor's `run`/`shutdown`, the reflector minus its watch loop (D4 as a
   hypothesis), and the informer contract's assembly (the history `γe` tied to the store's steps
   through `procSend` and the FIFO; `gateOff`; the batch path still C4/D3) (`notes/STATUS.md`,
   "The informers, third round: listeners, processor, selectors").
5. **The controller.** `Run`, the workers, `syncDaemonSet` and what it calls on this scenario's
   paths, the event handlers, `syncNodeUpdate`; S1's invariant.
6. **The closed theorem.** `examples/dsonepod`'s `wp_Main`, its package table and init, and
   `dsonepod_safe` through `etcd_adequate`'s pattern (`common/Adequacy.lean`); a TCB collection
   `etc/tcb-collections/daemonset.txt`.

Phases 2 and 3 are independent and can run in parallel; 4 needs 2 and 3; 5 needs 2 and 4.

## Open

- ~~The pin~~: `878cfa6c4cc7` (2026-10-27, phase 0 above).
- One node and one DaemonSet first, or N nodes from the start (S1 per node then reads the pod's
  target node, `util.GetTargetNodeName`).
- Other writers in `Main` (a client that deletes pods at random): S1 should survive them, and
  they exercise the delete paths.
- The event recorder: trusted no-op or verified.
