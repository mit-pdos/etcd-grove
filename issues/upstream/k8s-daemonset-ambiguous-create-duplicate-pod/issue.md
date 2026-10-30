<!-- Draft for kubernetes/kubernetes (sig-apps; cc the KEP-5647 authors and the author of #139657). Not filed. -->

# DaemonSet controller creates a second pod on a node after a pod create that is committed but returns an error

## What happened?

The DaemonSet controller can briefly run two of a DaemonSet's pods on one node. This happens when
a pod create is committed by the API server but the controller gets an error back. Examples are a
504 from the apiserver's request timeout (`FinishRequest` returns "request did not complete within
requested timeout" while the handler goroutine goes on to commit), a 500 wrapping etcd's
"request timed out" for a proposal that is later applied, and a connection lost after the commit.
In that case:

1. `syncNodes` (`pkg/controller/daemon/daemon_controller.go`, the `Failed creation, decrementing
   expectations` branch) calls `expectations.CreationObserved` and returns the error. The DaemonSet
   is requeued.
2. `RealPodControl.createPods` (`pkg/controller/controller_utils.go`) returns before `OnWrite`.
   The KEP-5647 consistency store (`StaleControllerConsistencyDaemonSet`, on by default) therefore
   records nothing for the write.
3. The requeued sync passes `EnsureReady`, and its expectations are satisfied. If the pod informer
   has not yet delivered the committed pod, `manage` sees no daemon pod on the node and creates a
   second one.
4. Once the informer has both pods, `podsShouldBeOnNode` deletes all but the oldest. The extra pod
   still goes through graceful deletion.

The problem is transient. It violates `MaxOnePodPerNode`, the safety invariant of the controller
robustness test in #139657. That test cannot reach this path: its injected errors are synthesized
in `FaultInjectingTransport.RoundTrip` without forwarding the request, so a failed write there
never takes effect.

## How can we reproduce it?

Deterministically, at #139657's head (13ecb9cc), on the real kube-apiserver and etcd of the
integration framework. The patch (attached: `01-repro-commit-then-fail.diff`) changes the following:

- It adds an `AfterCommit` flag to `robustness.HTTPStatusError`, via `CommitThenFail(err)`. With
  the flag set, `RoundTrip` forwards the request, discards the server's response and returns the
  injected error.
- It adds `AmbiguousChildCreateScenarios()`, which the DaemonSet matrix includes. In each scenario
  the first pod POST fails once, as a 504 or a 500. The error is either committed (`Ambiguous*`) or
  not committed (`Failed*`, the control). The scenario optionally adds the existing `StaleChildWatch`
  stall: the pod watch stalls for `WatchStall` (2s) at its first event.

```
go test ./test/integration/daemonset -run 'TestDaemonSetReconcileRobustnessMatrix' -count=1 -v
```

| scenario | result |
|---|---|
| AmbiguousChildCreate504StaleChildWatch | FAIL 10/10: `safety invariant "MaxOnePodPerNode" failed: detected 2 Pod objects, maximum allowed is 1` |
| AmbiguousChildCreate500StaleChildWatch | FAIL 10/10 (same) |
| FailedChildCreate{504,500}StaleChildWatch (same stall, error not committed) | PASS 10/10 |
| AmbiguousChildCreate{504,500} (no stall, natural lag on loopback) | PASS 200/200 each |
| the existing 8 scenarios | PASS 10/10 |

The controller's log in the failing runs shows the following sequence:

```
daemon_controller.go:1109] "Unhandled Error" err="Timeout: request did not complete within requested timeout ..."
daemon_controller.go:414]  "Unhandled Error" err="default/ds-1 failed with : Timeout: ..."
daemon_controller.go:414]  "Unhandled Error" err="default/ds-1 failed with : read version: 191 is not as new as written version: 199 for group resource pods"
[Invariant Safety Violation] safety invariant "MaxOnePodPerNode" failed: ... detected 2 Pod objects
```

The requeued sync created the second pod, with resource version 199, before the first one
reached the cache. Only after that second, successful write did the consistency store hold the
controller back.

## What did you expect to happen?

At most one pod of the DaemonSet per node. This is the invariant #139657 checks, and the
guarantee KEP-5647 was meant to give against acting on a pod cache that is behind the
controller's own writes. A client cannot tell a create that failed after committing from one that
never happened, so treating every create error as "the pod will never appear" is unsafe.

## Prior discussion

- #86140 (2019) removed the `IsTimeout` special case in the ReplicaSet, Job and DaemonSet
  controllers, so a timed-out create now lowers the expectation. Its review named this outcome:
  "This would cause ReplicaSet controller to create extra Pods", and the reply was "In that
  unlikely case, an extra pod will be created and healed on the next sync". For a ReplicaSet the
  extra pod is surplus that gets scaled down. For a DaemonSet it is a second instance on the same
  node.
- KEP-5647 (sig-api-machinery, `5647-stale-controller-handling`) tracks resource versions "after a
  successful write operation" and does not discuss writes whose outcome is unknown.
- #138181 documents the same assumption for deletes: "any failure to delete the pod means that we
  will never observe the delete".

## Possible fix (tested)

On a create error that may have committed (anything but a 4xx status), record the pods that exist
instead of lowering the expectation blindly. After the batch, list the DaemonSet's pods from the
API server (a consistent read) and `WroteAt` the resource versions of the pods it controls into the
consistency store. Then lower the expectations. If the list fails, keep the expectations, so the
5-minute expectation timeout settles them. Diff: `04-fix-record-unknown-pod-writes.diff`, about
50 lines in `daemon_controller.go`.

- With it, the whole matrix including the new scenarios passes, 10/10 runs. That includes
  `FlakyAPIServer` and `Failed*StaleChildWatch`, so uncommitted 5xx errors are still retried
  promptly.
- `go test ./pkg/controller/daemon/...` passes, as does the whole `test/integration/daemonset`
  package.
- Cost: one LIST per sync that saw an ambiguous create error, and nothing on the success path.
- Residual: with a server-side 504, the handler may commit after the controller's list. That
  window is much narrower but not closed. Closing it needs a create the controller can recognize:
  a client-chosen name reused on retry, or a per-node unique key that gets AlreadyExists, which is
  how StatefulSet avoids this.

The simpler alternative is to not lower the expectation on an ambiguous error
(`05-alt-fix-keep-expectations.diff`). It fixes the repro but stalls the node for the 5-minute
`ExpectationsTimeout` whenever a 5xx did not commit. It fails `FlakyAPIServer` and
`Failed*StaleChildWatch` in the matrix, and `TestDaemonSetPodCreateExpectationsError`.

## Other controllers

ReplicaSet (`manageReplicas`: `skippedPods := diff - successfulCreations` includes the failed
creates) and Job (`Failed creation, decrementing expectations`) use the same pattern with
`generateName`. Reading the code, though we have not reproduced it, they can over-create in the
same way: an extra replica, or for an Indexed Job presumably a second pod for the same index until
it is cleaned up. StatefulSet names its pods deterministically, so a second create gets
AlreadyExists, and it is immune.

## Kubernetes version

master at 13ecb9cc (the head of #139657, 2026-10-26); the code paths are unchanged on master.
