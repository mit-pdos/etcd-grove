---
upstream: none
checked: 2026-10-26
links: []
---

# The DaemonSet controller creates a second pod on a node after a pod create that failed but committed

- **Status**: a bug (a transient safety violation: two pods of one DaemonSet on one node), on an
  error path: a pod create that the API server committed but whose call returned an error (a
  timeout after the commit, a lost response). The consistency store of KEP-5647
  (`StaleControllerConsistencyDaemonSet`, on by default since 1.36), which keeps the controller
  from acting on a stale pod cache after its own writes, records only writes that succeeded, and
  the expectations are lowered on the error, so neither guards the next sync. The controller
  deletes the extra pod once its cache sees both, so the window is one cache lag; the PR's
  robustness test cannot reach it, because its injected 500s never reach the server
  (`test/utils/robustness/transport.go:110`, `synthesizeResponse`).
- **Where**: kubernetes/kubernetes at `13ecb9cc` (the head of kubernetes/kubernetes#139657 on
  2026-10-26; the lines below are master's, the PR does not change them):
  - `pkg/controller/controller_utils.go:618-628`, `RealPodControl.createPods`: on the create's
    error it returns before `OnWrite`, the callback through which the DaemonSet controller
    records the written resource version in its consistency store
    (`pkg/controller/daemon/daemon_controller.go:176-188`, `podWriteCallback`).
  - `pkg/controller/daemon/daemon_controller.go:1095-1110`, `syncNodes`: on the error it calls
    `dsc.expectations.CreationObserved` ("Failed creation, decrementing expectations"), as if the
    pod will never be seen, and returns the error, so the DaemonSet is requeued.
  - `daemon_controller.go:1302`, `syncDaemonSet`: the next sync's `EnsureReady` has no record of
    the pod's write, the expectations are satisfied, and `manage` reads the pod cache, which has
    not seen the committed pod yet: the node has no daemon pod, and `syncNodes` creates one.
  - `daemon_controller.go:906-917`, `podsShouldBeOnNode`: once the cache has both, a later sync
    deletes all but the oldest.
- **What happens**: two pods of the DaemonSet exist for one node until the controller sees both
  and deletes one. For a node agent (host ports, host paths, exclusive devices) the second
  instance may fail or contend with the first in the meantime.
  Reproduction: `examples/k8sdaemonset/smoke/smoke_test.go`, `TestAmbiguousWrites`: the real
  controller and client-go informers over the model API server of `examples/k8sdaemonset/apimodel`
  with `Config.AmbiguousWrites` (a write may commit and still report a timeout) and the other
  failures at 20%; a checker lists the pods every millisecond. 4 of 50 runs had two pods at once,
  each after exactly one ambiguous pod create (counted by wrapping the controller's clientset).
  With the same failures but no ambiguous writes (`TestNoEffectFailures`), 0 of 30 runs did.
  Generate the test's `go.mod` from a Kubernetes checkout (`gen-gomod.py`; the file's comment).
- **Expected**: `MaxOnePodPerNode`, the safety invariant the robustness test of
  kubernetes/kubernetes#139657 checks (`test/integration/daemonset/robustness_test.go:123`):
  at no time more than one pod of the DaemonSet per node. A client cannot tell a create that
  failed after its commit from one that never happened: a client-side timeout or a broken
  connection loses the response of a committed write, and the API server's own request timeout
  answers 504 while the request's handler may still go on to commit (not checked against the
  apiserver's timeout filter in this repository; the client-side cases suffice).
- **How the proof handles it**: not yet proved (`notes/k8s-daemonset-plan.md`). The planned
  theorem takes the model with `AmbiguousWrites` off (a failed write had no effect), the
  premise that records this issue (`examples/k8sdaemonset/apimodel/doc.go`, "Failures").
- **Possible fixes**:
  - Keep the expectation on an error that may be ambiguous (a timeout, a 5xx, a broken
    connection): lower it only on an error that says the create did not happen (4xx), and let
    the expectation's own timeout or the watch event settle the rest. This is the smallest
    change, but an expired expectation (`ExpectationsTimeout`, 5 minutes) reopens the window if
    the cache is still behind.
  - Record an ambiguous create in the consistency store as an unknown write, so that
    `EnsureReady` waits for the cache to pass the API server's current resource version (one
    quorum read of the pod list's resource version) before the next `manage`.
  - Name daemon pods deterministically (from the DaemonSet and the node, as StatefulSet names
    its pods), so that a second create for the same node fails with AlreadyExists.
  Searched upstream (2026-10-26, kubernetes/kubernetes issues): "daemonset duplicate pods create
  timeout", "daemonset two pods same node", "daemonset extra pod", "controller expectations create
  error timeout duplicate"; nothing about this path.
- **Found**: 2026-10-26, running the DaemonSet controller over the model API server written for
  its verification (`examples/k8sdaemonset`), while checking the premise the plan had flagged.
