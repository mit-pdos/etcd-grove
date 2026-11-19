---
upstream: none
checked: 2026-11-19
links:
  - kubernetes-sigs/structured-merge-diff#335 issue open: related, not this bug (addBackOwnedItems keeps a co-owned list item in a corrupt state; one version)
blocks-proof: no
---

# merge: Apply removes a field another manager owns when the managers are at different API versions

When server-side apply prunes the fields a manager stopped applying, a field that another manager
still owns at the applier's own API version can be removed, depending only on the version of a
third, unrelated manager. In the reproduction, manager B applies at `v1` and gives up
`containers[name=b].port`, which manager C (also at `v1`) still owns. When the third manager A,
which owns only the item `containers[name=b]` and its key, is at `v1`, the field stays; when A is at
`v2`, `Apply` removes it. With three or more versions the result can also change from run to run
(Go's map order).

**Expected:** `Apply` should keep every field some manager owns ("fields owned by other managers are
not removed", the pruning's purpose, `merge/update.go`), whatever the versions of the managers'
entries.

**Impact:** managed fields at several API versions are normal in Kubernetes: each manager's entry
records the version it applied or updated at, and clients move between versions of a resource. A
field another applier or updater still manages can disappear from the object when a co-owner stops
applying it. Not tried through the API server.

**Reproduction:** `TestApplyMultiVersionPrunesOwnedField` in
[`issues/smd-apply-multiversion-prunes-owned/multiversion_test.go`](smd-apply-multiversion-prunes-owned/multiversion_test.go),
copied into `merge` at kubernetes-sigs/structured-merge-diff@560aaa513ea735bf59e6011feecd5388e2dfeae9
(v7.0.1, the same `merge` package as v7.0.0), go1.27.3 linux/amd64:

```
$ go test ./merge -run TestApplyMultiVersionPrunesOwnedField
--- FAIL: TestApplyMultiVersionPrunesOwnedField (0.00s)
    multiversion_test.go:76: A at v2: containers[name=b].port, owned by C at v1, was removed: [map[name:b] map[name:c]]
```

**Cause:** `addBackOwnedItems` ([`merge/update.go#L284-L309`](https://github.com/kubernetes-sigs/structured-merge-diff/blob/560aaa513ea735bf59e6011feecd5388e2dfeae9/merge/update.go#L284-L309))
adds back owned fields one version at a time, each pass recomputing the removal set from the
previous pass's output ([`#L338`](https://github.com/kubernetes-sigs/structured-merge-diff/blob/560aaa513ea735bf59e6011feecd5388e2dfeae9/merge/update.go#L338)).
The `v1` pass removes the item `containers[name=b]` whole (no manager at `v1` owns the item itself);
the `v2` pass adds the item back (A owns it) but not `port`, which only the `v1` pass protected, from
an object that no longer has it.

## Proof

no: `Updater.Apply`'s spec requires every manager's entry at the request's version
(`Spec/sigs_k8s_io/structured_merge_diff/v7/merge/Updater__Apply.lean`); the driver uses one version.
