---
upstream: none
checked: 2026-10-26
links:
  - kubernetes/kubernetes#86140 pr merged: removed the timeout special case (so a timed-out create lowers the expectation); its review accepted "an extra pod will be created and healed on the next sync"
  - kubernetes/kubernetes#138181 pr merged: the same assumption for deletes ("any failure to delete the pod means that we will never observe the delete"); not this bug
  - kubernetes/kubernetes#139657 pr open: the controller robustness framework whose MaxOnePodPerNode this breaks; its injected faults never reach the server (still open 2026-11-01, head now 806c3e93)
  - kubernetes/enhancements#5647 issue open: KEP-5647, which tracks only successful writes; does not discuss writes with unknown outcome
blocks-proof: yes
---

# DaemonSet controller creates a second pod on a node after a pod create that is committed but returns an error

The DaemonSet controller can briefly run two of a DaemonSet's pods on one node. It happens when a
pod create is committed by the API server but the controller gets an error back: a 504 from the
apiserver's request timeout (the handler goes on and commits), a 500 wrapping etcd's "request
timed out" for a proposal later applied, or a connection lost after the commit. The requeued sync,
whose pod cache has not yet seen the committed pod, creates a second one; the controller deletes
the extra pod once its cache sees both.

**Expected:** at most one pod of the DaemonSet per node (`MaxOnePodPerNode`, the safety invariant
of the controller robustness test in #139657), the guarantee KEP-5647's consistency check
(`StaleControllerConsistencyDaemonSet`, on by default since 1.36) was meant to give against acting
on a pod cache behind the controller's own writes.

**Impact:** clusters whose API server returns a timeout for a pod create that commits (a slow etcd,
an overloaded apiserver), with the default feature gates. The window is one cache lag after the
error, plus the extra pod's graceful deletion (30 s by default). Without a host port both instances
run, so node agents using host paths, sockets or exclusive devices contend; with one the scheduler
keeps the duplicate Pending. ReplicaSet and Job follow the same pattern (read, not reproduced),
where an extra pod is surplus; StatefulSet's deterministic names make it immune.

**Reproduction:** [`issues/k8s-daemonset-ambiguous-create-duplicate-pod/repro-commit-then-fail.patch`](k8s-daemonset-ambiguous-create-duplicate-pod/repro-commit-then-fail.patch),
applied to kubernetes/kubernetes at 13ecb9cc (the head of #139657 on 2026-10-26; the controller
code is the same on master), on the real kube-apiserver and etcd of the integration framework,
2026-10-26 (not rerun 2026-11-01: it needs a Kubernetes checkout at #139657 and its etcd). It adds
a commit-then-fail fault to the framework's transport (`robustness.CommitThenFail`: forward the
request, discard the response, return the injected error) and six scenarios:

```
$ go test ./test/integration/daemonset -run 'TestDaemonSetReconcileRobustnessMatrix' -count=1 -v
AmbiguousChildCreate504StaleChildWatch   FAIL 10/10: safety invariant "MaxOnePodPerNode" failed: detected 2 Pod objects, maximum allowed is 1
AmbiguousChildCreate500StaleChildWatch   FAIL 10/10 (same)
FailedChildCreate{504,500}StaleChildWatch (same stall, not committed)   PASS 11/11
AmbiguousChildCreate{504,500} (no stall: loopback watch lag only)       PASS 200/200
the existing 8 scenarios                                                PASS 10/10
```

The controller's log in a failing run:

```
daemon_controller.go:1109] "Unhandled Error" err="Timeout: request did not complete within requested timeout ..."
daemon_controller.go:414]  "Unhandled Error" err="default/ds-1 failed with : read version: 191 is not as new as written version: 199 for group resource pods"
[Invariant Safety Violation] safety invariant "MaxOnePodPerNode" failed: ... detected 2 Pod objects
```

**Cause:** on the create's error,
[`RealPodControl.createPods`](https://github.com/kubernetes/kubernetes/blob/13ecb9cc55221a87f549ed8fc2dad758f22f0883/pkg/controller/controller_utils.go#L618-L628)
returns before `OnWrite`, through which the controller records the written resource version in its
consistency store, so the store records nothing; and
[`syncNodes`](https://github.com/kubernetes/kubernetes/blob/13ecb9cc55221a87f549ed8fc2dad758f22f0883/pkg/controller/daemon/daemon_controller.go#L1095-L1110)
calls `expectations.CreationObserved` ("Failed creation, decrementing expectations") as if the pod
will never appear. The next sync's `EnsureReady` has nothing to wait for, its expectations are
satisfied, and `manage` creates a pod on a node whose committed pod the cache has not seen.

## Proof

yes: the planned DaemonSet theorem takes the model API server with `AmbiguousWrites` off (a failed
write had no effect), a premise real API servers do not meet
(`examples/k8sdaemonset/apimodel/doc.go`, "Failures"; `ambiguous_create_breaks_S1` in
`Proof/k8s_io/kubernetes/pkg/controller/daemon/S1Model.lean`).

## Fix

On a create error that may have committed (anything but a 4xx), `syncNodes` would list the
DaemonSet's pods from the API server and record the versions of the pods it controls in the
consistency store before lowering the expectations
([`fix.patch`](k8s-daemonset-ambiguous-create-duplicate-pod/fix.patch), against 13ecb9cc, about 50
lines, no fix branch).

## Notes

The fix keeps the expectations if the list fails. It makes the whole matrix pass (11 of 11
runs), keeps uncommitted 5xx retried promptly, and passes `go test ./pkg/controller/daemon/...` and
`test/integration/daemonset`; cost one LIST per sync that saw such an error. Residual: a server-side
504 whose handler commits after the list. Rejected: keeping the expectation on an ambiguous error
stalls the node for the 5-minute `ExpectationsTimeout` when the 5xx did not commit (fails
`FlakyAPIServer`, `Failed*StaleChildWatch`, `TestDaemonSetPodCreateExpectationsError`). Complete but
larger: a pod name the controller reuses on retry, so a second create gets AlreadyExists.

Found 2026-10-26 running the controller over the model API server (`examples/k8sdaemonset`,
`smoke/smoke_test.go`'s `TestAmbiguousWrites`: 4 of 50 runs had two pods, each after one ambiguous
create; 0 of 30 without). The model backend for #139657's matrix (`KUBE_ROBUSTNESS_BACKEND=model`)
agreed with the real server on 13 of 14 scenarios; it found a model bug (an empty store's list at
resource version "0" turns the consistency check off: `nonissues/k8s-consistency-malformed-rv-ready.md`)
and a harness race (the settle check can run before a 2 s stall releases; suggested: do not declare
settled before `BlockingFaultDeadline()`). Those diffs and the alternative fix are in git history
(`issues/k8s-daemonset-ambiguous-create-duplicate-pod.md`, removed 2026-11-01). The draft
issue was addressed to sig-apps, cc the KEP-5647 authors (michaelasp; approvers liggitt, deads2k).
