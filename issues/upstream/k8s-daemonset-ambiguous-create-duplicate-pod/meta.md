# k8s-daemonset-ambiguous-create-duplicate-pod

- **Finding**: `issues/k8s-daemonset-ambiguous-create-duplicate-pod.md`
- **Target**: kubernetes/kubernetes (sig-apps: the DaemonSet controller). Also tell the KEP-5647
  owners (sig-api-machinery, author `michaelasp`, approvers `liggitt` and `deads2k`), who also wrote
  #139657.
- **Base**: kubernetes/kubernetes 13ecb9cc, the head of #139657, which adds `test/utils/robustness`.
- **State**: not filed. `issue.md` is the draft. There is no fix branch on a fork yet; the fix is
  `04-fix-record-unknown-pod-writes.diff`.

## Files

All diffs are against 13ecb9cc. They were made with `git diff` in a scratch checkout, on branches
`repro-ambiguous-create`, `model-backend`, `model-rv1`, `fix-unknown-write` and
`fix-keep-expectations`.

| file | what it holds |
|---|---|
| `01-repro-commit-then-fail.diff` | `HTTPStatusError.AfterCommit` and `CommitThenFail`. `FaultInjectingTransport.RoundTrip` forwards the request, drains and closes the response, and returns the injected error. Also `AmbiguousChildCreateScenarios()` (6 scenarios), added to `TestDaemonSetReconcileRobustnessMatrix` |
| `02-model-backend.diff` | Includes 01. `KUBE_ROBUSTNESS_BACKEND=model` runs the fixture over `test/utils/robustness/apimodel`, a copy of `examples/k8sdaemonset/apimodel` at f793ea63d7, unchanged except for a provenance paragraph. `modelclient.go` is the fault-injecting clientset: per call it uses the same `ClientFacts` as the HTTP transport and `ResolveTransport`, AfterCommit calls through and then fails, mutations are recorded for the settle detector, and watches are wrapped so that `ResolveWatchEvent` runs per event. On this backend `WatchListClient` is off, because the model does not serve `sendInitialEvents` |
| `03-model-empty-store-rv1.diff` | Applies on top of 02. The model's empty store is at resource version 1, not 0 (see "Model findings") |
| `04-fix-record-unknown-pod-writes.diff` | The proposed fix (controller only) |
| `05-alt-fix-keep-expectations.diff` | The rejected alternative (controller only) |

## Commands

The integration test binary was built with `go test -c ./test/integration/daemonset` from the
checkout, with `third_party/etcd` on PATH, and run from `test/integration/daemonset` as
`<bin> -test.run <re> -test.count=N -test.v`. `KUBE_ROBUSTNESS_SEED` does not matter here: none of
these scenarios uses a probabilistic condition, except `FlakyAPIServer`'s 30%, whose seeds are in
the logs.

## Results (2026-10-26)

Real kube-apiserver and etcd, at 01 or 02 with the backend unset:

| scenario | result |
|---|---|
| AmbiguousChildCreate504StaleChildWatch | FAIL 10/10 (1 + 10 runs), MaxOnePodPerNode violated about 50 ms after the 504 |
| AmbiguousChildCreate500StaleChildWatch | FAIL 10/10 (1 + 10) |
| FailedChildCreate504StaleChildWatch, FailedChildCreate500StaleChildWatch (controls: same stall, not committed) | PASS 11/11 each |
| AmbiguousChildCreate504, AmbiguousChildCreate500 (no added stall; natural lag on loopback) | PASS 200/200 each (`-test.count=50`, 4 processes) |
| the 8 existing scenarios | PASS 10/10 |

Model backend (02), the whole matrix, 20 runs (`-test.count=10`, 2 processes):

| scenario | result |
|---|---|
| Ambiguous*StaleChildWatch | FAIL 20/20 each (agrees with the real backend) |
| Failed*StaleChildWatch, Ambiguous504/500, and the 7 other existing scenarios | PASS 20/20 (agrees) |
| StaleChildWatch | FAIL 3/20, a disagreement: the real backend passed 10/10 |

Model backend with 03, 20 runs: the same, except StaleChildWatch FAILs 5/20 (see "Model findings").

Fixes, real backend:

- 04 (record the unknown writes):
  - `go test ./pkg/controller/daemon/...` passes.
  - The whole matrix (14 scenarios) passes 1 + 10/10 runs.
  - The whole `test/integration/daemonset` package (`-test.run .`) passes: 13 top-level tests, the matrix among them, none failed or skipped.
- 05 (keep the expectations):
  - It fixes both Ambiguous*StaleChildWatch scenarios.
  - It FAILs `FlakyAPIServer` and both Failed*StaleChildWatch scenarios. The uncommitted 5xx leaves
    an expectation that only the 5-minute `ExpectationsTimeout` releases, so liveness misses its
    30s deadline.
  - It FAILs the unit test `TestDaemonSetPodCreateExpectationsError`, which expects failed creates
    to lower the expectations.

## Model findings (the disagreements between the backends)

1. **Resource version "0".** The model's empty store answers a list with
   `ListMeta.ResourceVersion` "0" (`rev` starts at 0).
   - client-go's `resourceversion.CompareResourceVersion` rejects "0" as malformed.
   - `consistencyStore.EnsureReady` treats a comparison error as ready (`continue`).
   - So on the model, a pod informer whose last sync was the initial empty list does not block,
     and the KEP-5647 check is silently off until the first pod event. The log shows syncs passing
     `EnsureReady` while the pod watch is stalled.
   - kube-apiserver never serves "0": etcd's revision starts at 1, and the integration server has
     written objects before any controller lists.
   - Fix: 03 starts the store at resource version 1. It should also go into
     `examples/k8sdaemonset/apimodel`, whose doc says resource versions start at the first change;
     not changed there yet.
2. **StaleChildWatch is racy on any backend.** With the consistency check working (03),
   StaleChildWatch still fails 5/20 on the model. The settle detector checks the status after a
   2s write-idle window (`CheckWhenSettled(2s)`), and the injected stall also lasts 2s
   (`WatchStall`). In the failing runs the settle check ran 0.3 ms before the stall released
   (settle at 22:21:15.0524, stall deadline 15.0527), and saw `CurrentNumberScheduled` 0. On the
   real backend the request latency puts the last mutation (the event POST) after the stall began,
   so the check always fell after the release. This is a timing fragility of the harness, not a
   difference in semantics: a stalled controller is write-idle, so "settled" can be declared while
   a stall is still in effect. The model's near-zero latency exposes it. Suggested harness fix:
   do not declare settled before `BlockingFaultDeadline()`.
3. No other disagreement in the 14 scenarios.

## Duplicates checked (2026-10-26)

- kubernetes/kubernetes, keyword searches through `gh api search/issues`: daemonset duplicate,
  two pods on a node, extra pod on timeout, `CreationObserved`, decrementing expectations, create
  timeout duplicate, `StaleControllerConsistency`, KEP-5647. Nothing reports this.
- Related:
  - #86140 (pr merged 2019): removed the timeout special case. Its review accepted "an extra pod
    will be created and healed on the next sync"
    (https://github.com/kubernetes/kubernetes/pull/86140#discussion_r357321174). lavalamp asked
    for tests of error-and-actually-create (#discussion_r404410857).
  - #67662 (closed): the opposite problem, pods missing because timeouts were swallowed.
  - #49915 / #48893 (2017): where the special case came from.
  - #138181 (pr merged 2026-04): "any failure to delete the pod means that we will never observe
    the delete", the same assumption for deletes.
  - KEP-5647 implementation PRs (DaemonSet #134937, ReplicaSet #137212, Job #137210, StatefulSet
    #137254; all merged): no review discussion of committed-but-failed writes.
  - #139657 (pr open): the robustness framework; its injected faults never reach the server.
- kubernetes/enhancements: KEP-5647 (`keps/sig-api-machinery/5647-stale-controller-handling`,
  tracking issue kubernetes/enhancements#5647) covers only "a successful write operation". Its PRR
  answers about apiserver/etcd unavailability and known failure modes are blank.
