---
upstream: none
checked: 2026-11-19
links: []
blocks-proof: no
---

# merge: Apply and Update panic when IgnoredFields has no entry for the request's version

An `Updater` built with `UpdaterBuilder.IgnoredFields` set for some API versions panics with a nil
pointer dereference on any `Apply` or `Update` at a version the map has no entry for.

**Expected:** a version without ignored fields should ignore nothing, as a nil `IgnoredFields` and
a missing `IgnoreFilter` entry do; the field's documentation ("IgnoredFields provides a set of
fields to ignore for each", sic) states no requirement to cover every version.

**Impact:** callers of the public `UpdaterBuilder` that set `IgnoredFields` for the versions they
know and serve a request at another. Kubernetes itself sets `IgnoreFilter` instead, which handles a
missing version, so the API server does not reach it.

**Reproduction:** `TestIgnoredFieldsOtherVersion` in
[`issues/smd-ignoredfields-missing-version-panic/ignoredfields_test.go`](smd-ignoredfields-missing-version-panic/ignoredfields_test.go),
copied into `merge` at kubernetes-sigs/structured-merge-diff@560aaa513ea735bf59e6011feecd5388e2dfeae9
(v7.0.1), go1.27.3 linux/amd64:

```
$ go test ./merge -run TestIgnoredFieldsOtherVersion
--- FAIL: TestIgnoredFieldsOtherVersion (0.00s)
    ignoredfields_test.go:50: Apply at v2 panicked: runtime error: invalid memory address or nil pointer dereference
    ignoredfields_test.go:50: Update at v2 panicked: runtime error: invalid memory address or nil pointer dereference
```

**Cause:** `Apply` and `Update` build `fieldpath.NewExcludeSetFilter(s.IgnoredFields[version])`
([`merge/update.go#L187`](https://github.com/kubernetes-sigs/structured-merge-diff/blob/560aaa513ea735bf59e6011feecd5388e2dfeae9/merge/update.go#L187),
[`#L230`](https://github.com/kubernetes-sigs/structured-merge-diff/blob/560aaa513ea735bf59e6011feecd5388e2dfeae9/merge/update.go#L230))
whenever the map is non-nil; for a missing version that is a filter over a nil `*Set`, whose
`Filter` calls `set.RecursiveDifference(nil)`, which dereferences it.

## Proof

no: `Updater.Apply`'s and `Updater.Update`'s specs take an updater with `IgnoredFields` nil
(`Spec/sigs_k8s_io/structured_merge_diff/v7/merge/`), which the driver's `BuildUpdater` gives.
