---
upstream: none
checked: 2026-11-19
links: []
blocks-proof: no
---

# merge: re-applying a struct deletes it when it holds an unowned field and an empty list

A manager that applied `spec: {}` and applies `spec: {}` again gets an object without `spec`, when
the live `spec` also holds a field no manager owns (`a`, as a field the API server defaulted) and an
empty associative list (`l: []`). The field the manager is applying right now is deleted. Without
the empty list the same apply is a no-op.

**Expected:** a field in the applied configuration should be in the result: `Apply` removes only
fields "that the manager applied last time and no longer applies" (the pruning's purpose,
`merge/update.go`), and `spec` is applied both times.

**Impact:** a client that applies an empty struct to claim it (a common way to own a block that
defaults fill in), on an object whose struct also holds defaulted fields and an empty list, loses the
whole struct on a re-apply. Not tried through the API server.

**Reproduction:** `TestReapplyDeletesOwnStruct` in
[`issues/smd-apply-deletes-own-struct/ownstruct_test.go`](smd-apply-deletes-own-struct/ownstruct_test.go),
copied into `merge` at kubernetes-sigs/structured-merge-diff@560aaa513ea735bf59e6011feecd5388e2dfeae9
(v7.0.1, the same `merge` package as v7.0.0), go1.27.3 linux/amd64:

```
$ go test ./merge -run TestReapplyDeletesOwnStruct
--- FAIL: TestReapplyDeletesOwnStruct (0.00s)
    ownstruct_test.go:70: live spec map[a:a l:[]]: re-applying spec: {} deleted spec: map[name:o]
```

**Cause:** the second pass (`addBackOwnedItems`) removes the unowned `spec.a`; the third,
`addBackDanglingItems`
([`merge/update.go#L345-L365`](https://github.com/kubernetes-sigs/structured-merge-diff/blob/560aaa513ea735bf59e6011feecd5388e2dfeae9/merge/update.go#L345-L365)),
removes every path of the manager's last set that the pruned object's field set lacks. `l: []`
contributes no field path, so `spec` has none left, and `.spec`, in the last set, is removed as
"dangling", list included.

## Proof

no: the spec of `Updater.Apply` states SMD's pruning as it is (`prune`,
`Proof/sigs_k8s_io/structured_merge_diff/v7/merge/Defs.lean`, whose header records this case); the
driver's scenario does not reach it.
