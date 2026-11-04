---
upstream: none
checked: 2026-11-04
links: []
blocks-proof: no
---

# DaemonSet controller: on a DaemonSet recreated under the same name, the update handler clears the new DaemonSet's consistency record, not the old one's

`NewDaemonSetsController` registers `UpdateFunc: func(oldObj, newObj interface{}) {
dsc.updateDaemonset(logger, oldObj, newObj) }`, but `updateDaemonset` is declared
`updateDaemonset(logger klog.Logger, cur, old interface{})`: its `cur` is the event's old object and
its `old` the new one. Everything symmetric in the two (the UID comparison, the enqueued key)
is unaffected, but when the UIDs differ (the informer missed the delete of a DaemonSet that was
deleted and recreated under the same name) it calls `deleteDaemonset` on a
`DeletedFinalStateUnknown` of the **new** DaemonSet: `consistencyStore.Clear(name, newUID)`
forgets the writes recorded for the live DaemonSet (and keeps the dead one's record), and the
"Updating daemon set" log line names the old object.

**Why not an issue:** found by code reading, no test. The effect is the one the
consistency store exists to prevent: if a sync of the recreated DaemonSet created pods before the
update event was handled, its `WroteAt` records are cleared and a later sync can pass
`EnsureReady` on a pod cache that has not seen those creates (a duplicate pod, as in
`issues/k8s-daemonset-ambiguous-create-duplicate-pod.md`). Reaching it needs a missed delete event
(a relist) between a delete and a recreate under the same name, and a sync of the new DaemonSet
before the update event is processed: plausible but not reproduced. A Go test would make it an
issue.

## Proof

no: the DaemonSet run's model never deletes a DaemonSet (its DaemonSet client has no `Delete`;
track B's `sceneOk`: every logged version of a DaemonSet has the stored one's UID), so an update's
two versions have one UID and the branch is dead; `updateDaemonset`'s spec
(`Spec/k8s_io/kubernetes/pkg/controller/daemon/DaemonSetsController__updateDaemonset.lean`) names
the arguments as the event does and its proof refutes the branch from `s1Inv`.

## Notes

Code: `k8s.io/kubernetes/pkg/controller/daemon/daemon_controller.go` at `878cfa6c4cc7` (the
registration around line 245, `updateDaemonset` at line 302). Found 2026-11-03 writing the handler
specs (the DaemonSet run, track C). The fix: declare `updateDaemonset(logger, old, cur
interface{})`, as the other update handlers are.
