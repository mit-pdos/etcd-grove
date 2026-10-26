# Plan: the Kubernetes DaemonSet controller (`k8s.io/kubernetes/pkg/controller/daemon`)

Status: planning (2026-10-26, branch `daemonset-plan`). Decisions: D49 in `notes/decisions.md`
(the cut: model the API server at the typed clientset, verify client-go's leaf libraries and
informers). Nothing translated or proved yet; phase 0 is next.

## Goal

Prove safety properties of the real DaemonSet controller, running over a model of the Kubernetes
API server, in every execution. The first property is the one the controller robustness test
checks (kubernetes/kubernetes#139657, open: `test/integration/daemonset/robustness_test.go:121`,
`TestDaemonSetReconcileRobustnessMatrix`):

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

The robustness PR's own code (`test/utils/robustness`, its clock injection in
`controller_utils.go`) is not needed: the consistency store and the controller are on Kubernetes'
master already. Pin a master commit (phase 0), not the PR.

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
| Leaf libraries | `util/workqueue`; `tools/cache`'s `store.go`, `thread_safe_store.go`, `index.go`, keys, `WaitForNamedCacheSyncWithContext`; `listers/{apps,core}/v1`; `util/flowcontrol` (`Backoff`); `util/retry`; `features` | **Verified** directly. |
| Events | `tools/record`, `kubernetes/scheme` | **Trusted no-op** or verified over a no-op sink (events do not affect safety; phase 1 decides). |
| The controller | `pkg/controller/daemon`, `daemon/util`, `daemon/metrics`; `pkg/controller` (`controller_utils.go`, `controller_ref_manager.go`); `pkg/controller/util/consistency`; `pkg/api/v1/pod`, `pkg/apis/core/v1/helper`, `pkg/util/{labels,hash}` | **Verified**. |
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
`AtomicFIFO` on (without it `LastStoreSyncResourceVersion` returns `""` and the consistency store
lets every sync through), `StaleControllerConsistencyDaemonSet` on.

## How S1 is kept (the proof's skeleton)

The controller is the only writer of pods in the example. A sync of a DaemonSet:
1. `consistencyStore.EnsureReady` (`daemon_controller.go:1299`): if the controller recorded a write
   (`WroteAt`, after each successful pod create and status write) whose resource version the
   pod or DaemonSet informer's store has not reached, requeue. Otherwise clear the record.
2. Read the pods from the informer's cache; create one for each node that should run one and has
   none in the cache (`manage` → `syncNodes`), waiting for every create (`createWait.Wait`) before
   returning.

The invariant to establish: at the start of a sync that passes step 1, the pod cache contains
every pod of the DaemonSet the server holds. It rests on
- **the workqueue's exclusivity**: one worker per key, so no `WroteAt` for the DaemonSet runs
  during its `EnsureReady` (the store's stated precondition, `consistency.go:122`, "Must not be
  called concurrent with WroteAt for the same owner": its check and its `Clear` are not atomic, and
  a `WroteAt` between them would be lost);
- **the informer contract**: the store's `LastStoreSyncResourceVersion` never decreases, across
  relists too, and once it is at least `r` the store reflects every change up to `r`;
- **the model's write contract**: a failed write has no effect; a created pod's resource version is
  the one returned.

Expectations (`ControllerExpectations`) only make the controller more conservative; S1 should not
need them, though `SatisfiedExpectations` must be specified enough to show it does not panic.

**A suspected bug outside the model's contract (phase 0 checks it).** If a pod create is committed
but its call returns an error (a timeout after the commit), `syncNodes` lowers the expectations
(`CreationObserved`, `daemon_controller.go:1104`) and `OnWrite` never records a resource version.
A later sync on a pod cache that has not seen the pod would then create a second one. The
robustness test cannot reach this: its injected 500s are synthesized before the request is sent
(`test/utils/robustness/transport.go:110`). If phase 0 reproduces it, it goes in `issues/`
(`upstream: unchecked`), and the model's "a failed write has no effect" is the premise that
records it.

## Phases

0. **The example in Go.** `examples/dsonepod`: a Go module (as `examples/k8setcd3`) requiring
   `k8s.io/kubernetes` at a pinned master commit, with `replace` for its staging modules; the model
   API server (a package of the example); `Main` (one Node, one defaulted DaemonSet, the controller,
   the check loop over the model's state, not an informer). A Go test that runs `Main` with many
   seeds, under `-race`. A variant whose failed creates may commit, to try the suspected bug above.
   Decide: the pin; replacement module vs. constructor-level mock; the event recorder.
1. **The translation survey** (as `notes/k8s-etcd3-goose.md`): a project `k8s-daemonset` in
   `etc/goose.py` translating the packages of "The cut" with bodies, the rest names-only, and a
   list of what the pinned Goose rejects (G-numbered, `notes/k8s-daemonset-goose.md`). Known in
   advance (from the call-graph survey, 2026-10-26):
   - `getPatch` (`update.go:504`, on every sync): `json.Marshal` of the DaemonSet, `Unmarshal` into
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
   store (`pkg/controller/util/consistency`), `ControllerExpectations`.
3. **The model API server's spec and proof.** Logically atomic triples over an abstract state of
   resources and its change log (compare D44-D48's KV state and its watches: a watch is repeated
   reads of the log).
4. **The informers.** The reflector (list, watch, relist, bookmarks; watch-list off), the FIFO, the
   shared informer's processor and listeners, `WaitForNamedCacheSyncWithContext`: the informer
   contract above, plus the handlers' delivery (in order, with the objects' concrete types, which
   every handler's unchecked assertion needs). The hardest phase.
5. **The controller.** `Run`, the workers, `syncDaemonSet` and what it calls on this scenario's
   paths, the event handlers, `syncNodeUpdate`; S1's invariant.
6. **The closed theorem.** `examples/dsonepod`'s `wp_Main`, its package table and init, and
   `dsonepod_safe` through `etcd_adequate`'s pattern (`common/Adequacy.lean`); a TCB collection
   `etc/tcb-collections/daemonset.txt`.

Phases 2 and 3 are independent and can run in parallel; 4 needs 2 and 3; 5 needs 2 and 4.

## Open

- The pin (a master commit with the consistency store; the controller has changed since 1.36?).
- One node and one DaemonSet first, or N nodes from the start (S1 per node then reads the pod's
  target node, `util.GetTargetNodeName`).
- Other writers in `Main` (a client that deletes pods at random): S1 should survive them, and
  they exercise the delete paths.
- The event recorder: trusted no-op or verified.
