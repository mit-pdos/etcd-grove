---
upstream: none
checked: 2026-10-26
links:
  - kubernetes/kubernetes#86140 pr merged: removed the timeout special case (so a timed-out create lowers the expectation); its review accepted "an extra pod will be created and healed on the next sync"
  - kubernetes/kubernetes#138181 pr merged: the same assumption for deletes ("any failure to delete the pod means that we will never observe the delete"); not this bug
  - kubernetes/kubernetes#139657 pr open: the robustness framework whose MaxOnePodPerNode this breaks; its injected faults never reach the server
  - kubernetes/enhancements#5647 issue open: KEP-5647, which tracks only successful writes; does not discuss writes with unknown outcome
candidate: issues/upstream/k8s-daemonset-ambiguous-create-duplicate-pod/
---

# The DaemonSet controller creates a second pod on a node after a pod create that failed but committed

- **Status**: a bug. Two pods of one DaemonSet exist on one node for a while, a transient safety
  violation. It needs a pod create that the API server committed but whose call returned an error:
  a 504 from the apiserver's request timeout, a 500 wrapping etcd's "request timed out", or a lost
  response.
  - The KEP-5647 consistency store (`StaleControllerConsistencyDaemonSet`, on by default since
    1.36) stops the controller from acting on a pod cache that is behind its own writes, but it
    records only writes that succeeded.
  - The expectations are lowered on the error, so they do not guard the next sync either.
  - The controller deletes the extra pod once its cache sees both, so the window is one cache lag,
    plus the extra pod's graceful deletion.
  - Reproduced deterministically on the real kube-apiserver and etcd (below).
- **Where**: kubernetes/kubernetes at `13ecb9cc` (the head of kubernetes/kubernetes#139657 on
  2026-10-26; these lines are the same on master, the PR does not change them):
  - `pkg/controller/controller_utils.go:618-628`, `RealPodControl.createPods`: on the create's
    error it returns before `OnWrite`. `OnWrite` is the callback through which the DaemonSet
    controller records the written resource version in its consistency store
    (`pkg/controller/daemon/daemon_controller.go:176-188`, `podWriteCallback`).
  - `pkg/controller/daemon/daemon_controller.go:1095-1110`, `syncNodes`: on the error it calls
    `dsc.expectations.CreationObserved` ("Failed creation, decrementing expectations"), as if the
    pod will never be seen, and returns the error, so the DaemonSet is requeued.
  - `daemon_controller.go:1302`, `syncDaemonSet`: the next sync's `EnsureReady` has no record of
    the pod's write and the expectations are satisfied. `manage` then reads the pod cache, which
    has not seen the committed pod yet, finds no daemon pod on the node, and `syncNodes` creates
    one.
  - `daemon_controller.go:906-917`, `podsShouldBeOnNode`: once the cache has both, a later sync
    deletes all but the oldest.
  - Ambiguous errors that really occur:
    - `staging/src/k8s.io/apiserver/pkg/endpoints/handlers/finisher/finisher.go:83-148`,
      `finishRequest`: on the request's deadline it returns a 504 Timeout ("request did not
      complete within requested timeout") while the goroutine running the create goes on and may
      commit. `server/filters/timeout.go` likewise answers 504 while the handler keeps running.
      `NewTimeoutError(..., 0)` sets no Retry-After, so client-go does not retry the POST
      (`rest/with_retry.go:309`, `checkWait`).
    - etcd's "request timed out" for a proposal that is later applied.
    - A connection lost after the commit: client-go does not retry non-GET requests.
      kube-controller-manager sets no client-side timeout on its clients.
- **What happens**: two pods of the DaemonSet exist for one node until the controller sees both
  and deletes the newer one. The deletion is graceful (30s by default), so a running duplicate
  overlaps the original for the cache lag plus that grace period. With a host port the scheduler
  keeps the duplicate Pending. Without one, both instances run: node agents with host paths,
  sockets or exclusive devices contend.
  - **Reproduction, real API server**: `issues/upstream/k8s-daemonset-ambiguous-create-duplicate-pod/01-repro-commit-then-fail.diff`
    (against 13ecb9cc). It adds a commit-then-fail transport fault (`robustness.CommitThenFail`:
    forward the request, discard the response, return the injected error) and six scenarios in
    `TestDaemonSetReconcileRobustnessMatrix`.
    - "First pod POST commits and returns 504 (or 500); the pod watch stalls 2s at its first
      event": MaxOnePodPerNode is violated in 10 of 10 runs for each code.
    - The same stall with the error not committed (the existing behavior) passes 11 of 11.
    - Commit-then-fail with no added stall, on the loopback integration server's natural watch
      lag, passes 200 of 200 for each code. The duplicate needs the watch to lag behind the 5ms
      requeue, which an idle server does not.
    - The existing 8 scenarios pass.
    - Commands, logs and the per-run counts are in `meta.md` there.
  - **Reproduction, model**: `examples/k8sdaemonset/smoke/smoke_test.go`, `TestAmbiguousWrites`,
    runs the real controller and informers over the model API server (`examples/k8sdaemonset/apimodel`)
    with `Config.AmbiguousWrites` and the other failures at 20%. 4 of 50 runs had two pods at
    once, each after exactly one ambiguous pod create. With no ambiguous writes
    (`TestNoEffectFailures`), 0 of 30 did. The robustness matrix over the model
    (`02-model-backend.diff`, `KUBE_ROBUSTNESS_BACKEND=model`) agrees with the real server on all
    14 scenarios but `StaleChildWatch`. That one exposed a model bug (an empty store's list at
    resource version "0" turns the consistency check off, `03-model-empty-store-rv1.diff`) and a
    harness race (the settle check can run before a stall releases); details in `meta.md`.
- **Expected**: `MaxOnePodPerNode`, the safety invariant of the robustness test in
  kubernetes/kubernetes#139657 (`test/integration/daemonset/robustness_test.go:123`): at no time
  more than one pod of the DaemonSet per node. A client cannot tell a create that failed after its
  commit from one that never happened, so an error must not be read as "the pod will never appear".
- **How the proof handles it**: not yet proved (`notes/k8s-daemonset-plan.md`). The planned
  theorem takes the model with `AmbiguousWrites` off (a failed write had no effect); that premise
  records this issue (`examples/k8sdaemonset/apimodel/doc.go`, "Failures").
- **Possible fixes**:
  - Tested and proposed (`04-fix-record-unknown-pod-writes.diff`, about 50 lines). On a create
    error that may have committed (anything but a 4xx status), after the batch, list the
    DaemonSet's pods from the API server (a consistent read) and record the resource versions of
    the pods it controls in the consistency store, then lower the expectations. If the list fails,
    keep the expectations.
    - Results: it fixes the repro (the matrix passes 11 of 11 runs, all 14 scenarios), keeps
      uncommitted 5xx errors retried promptly (`FlakyAPIServer`, `Failed*StaleChildWatch`), and
      passes `go test ./pkg/controller/daemon/...` and the whole `test/integration/daemonset`
      package.
    - Cost: one LIST per sync with an ambiguous create error.
    - Residual: a create that the server's request timeout lets commit after that list is not
      covered.
    - With `StaleControllerConsistencyDaemonSet` off it changes nothing.
  - Tested and rejected (`05-alt-fix-keep-expectations.diff`): keep the expectation on an
    ambiguous error. It fixes the repro, but an uncommitted 5xx then stalls the node until
    `ExpectationsTimeout` (5 minutes). It fails `FlakyAPIServer`, both `Failed*StaleChildWatch`
    scenarios and the unit test `TestDaemonSetPodCreateExpectationsError`.
  - Complete but larger: name daemon pods so that a retry is recognizable, for example a name the
    controller chooses and reuses on retry for that node. A second create then fails with
    AlreadyExists, as StatefulSet's deterministic names do.
- **Other controllers** (read, not reproduced):
  - ReplicaSet (`pkg/controller/replicaset/replica_set.go:695-700`: `skippedPods := diff -
    successfulCreations` lowers the expectation for failed creates too) and Job
    (`pkg/controller/job/job_controller.go:1938-1942`) follow the same pattern with
    `generateName`, so they can over-create in the same way.
  - For a ReplicaSet the extra pod is surplus that gets scaled down, the case #86140's review
    accepted.
  - StatefulSet's pod names are deterministic, so it is immune.
- **Found**: 2026-10-26, running the DaemonSet controller over the model API server written for
  its verification (`examples/k8sdaemonset`), while checking the premise the plan had flagged.
  Confirmed the same day on the real API server with the commit-then-fail fault. The upstream
  search found no report: kubernetes/kubernetes issues and PRs, KEP-5647 and its implementation
  PRs (front matter; `meta.md`).
