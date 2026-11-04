---
upstream: none
checked: 2026-11-04
links: []
blocks-proof: no
---

# DaemonSet controller: a claimed ControllerRevision with no labels makes the sync panic (write to a nil map)

`constructHistory` (`pkg/controller/daemon/update.go`, lines 309-311) adds the hash label to every
claimed history that lacks it: `toUpdate := history.DeepCopy();
toUpdate.Labels[apps.DefaultDaemonSetUniqueLabelKey] = toUpdate.Name`. When the
ControllerRevision has no labels at all, `toUpdate.Labels` is `nil` and the assignment panics
(`assignment to entry in nil map`), which crashes the controller's worker.

`controlledHistories` returns such a revision in two ways: an orphan with no labels in the
DaemonSet's namespace is adopted when the DaemonSet's selector matches the empty label set
(`ClaimObject` adopts on a match; a selector of only `DoesNotExist`/`NotIn` requirements matches
`labels.Set(nil)`, and is valid for a DaemonSet whose template has no matching labels), or a
ControllerRevision already controlled by the DaemonSet's UID has no labels. The slice
`controlledHistories` returns holds the cached, pre-adoption object, so the adoption's patch does
not add labels to it.

**Why not an issue:** found by code reading (review round 1 of the DaemonSet run's sync-path
specs, `notes/k8s-daemonset-run/review-1-sync.md`), no test written. The controller's own revisions
always carry labels (`snapshot` builds them with `CloneAndAddLabel`, `update.go:539`), so reaching
it takes a third party creating a ControllerRevision with no labels that the DaemonSet then claims.
A Go test (a `fake` clientset with such a revision, one `syncDaemonSet`) would make it an issue.
Upstream status not checked beyond a search of kubernetes/kubernetes' issues (nothing found).

## Proof

no: in the run's model only the controller creates ControllerRevisions, and the scenario invariant
says every logged one is one the controller made for a stored DaemonSet, labelled with the template's
labels and the hash (`sceneOk.crs`, through `crOf.lbls`:
`r.ObjectMeta'.Labels' = some (<[hashKey := dsHash d]> (dsTmplLabels d))`,
`Proof/k8s_io/kubernetes/pkg/controller/daemon/Scene.lean`). So no claimed history lacks the hash
label and the write is not reached (`constructHistory`'s spec,
`Spec/k8s_io/kubernetes/pkg/controller/daemon/DaemonSetsController__constructHistory.lean`).

## Notes

Code: `k8s.io/kubernetes/pkg/controller/daemon/update.go` at `878cfa6c4cc7`
(`constructHistory`, the label write at line 311). Found 2026-11-04 by the sync-path spec review;
filed by track B. The fix: allocate the map when it is `nil` before the write
(`if toUpdate.Labels == nil { toUpdate.Labels = map[string]string{} }`).
