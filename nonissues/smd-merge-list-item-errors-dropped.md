---
upstream: none
checked: 2026-11-19
links: []
blocks-proof: no
---

# structured-merge-diff: merging a list's items drops the items' errors

`typed.TypedValue.Merge` (and so server-side apply's `merge.Updater.Apply`) silently ignores an
error raised while merging an item of an associative list: in
`mergingWalker.visitListItems` (`typed/merge.go`, v7.0.0), each item is merged with
`mergeOut, errs := w.mergeListItem(t, pe, lChild, rChild)` followed by
`errs = append(errs, errs...)`; the `:=` declares a new `errs` in the loop's block, shadowing the
function's result, so the item's errors (an item whose scalar has the wrong type in both the live
object and the configuration, a schema type that does not resolve) are appended to themselves and
discarded. The merge then succeeds, keeping whatever the item's walker produced (or dropping the
item when it produced nothing). The other walkers (`compareWalker`, `toFieldSetWalker`,
`validatingObjectWalker`) and the map case of the merge propagate their children's errors.

**Why not an issue:** found by code reading while modelling `Merge` (no test written); every
object the API server merges was validated against its schema first (`typed.AsTyped`), and an
invalid configuration item is rejected by that validation before `Apply`, so only an item that
validates and still fails to merge (two scalars of a mismatching type in both objects, after a
schema change) reaches the dropped error. `go vet`'s shadow analyzer flags the line.

## Proof

no: the SMD API's specs (notes/smd-plan.md) state `merge` (`typed/Defs.lean`) on values that
conform to a schema in scope (`Schema.WF`: every list atomic or associative with keys), where an
item's merge raises no error, so the dropped errors never arise in what the specs cover; the
driver's scenario never raises one.
