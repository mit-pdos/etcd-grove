---
upstream: none
checked: 2026-11-19
links: []
blocks-proof: no
---

# structured-merge-diff: managed fields that split a list item from its key field make Apply fail

`merge.Updater.Apply` (structured-merge-diff v7.0.0) fails with an error that is not a conflict,
`failed to compare objects: .containers: element 0: associative list with keys has an element that
omits all key fields ["name"] ...`, when the managed fields it is given split an associative list
item from its key field: the applying manager's previous set has the item's key field
(`.containers[name="a1"].name`) but not the item, and another manager's set has the item but not
its key field. Pruning (`Updater.prune`) removes the key field (the applier applied it last time,
no one else owns it) and keeps the item (another manager owns it), leaving an item without a key;
`TypedValue.Compare` of the live object with the pruned one then cannot compute the item's key.

Reproduction (a throwaway Go test against v7.0.0, the driver's schema of `examples/k8s/smd`):

```go
live := typedObj(map[string]interface{}{"name": "o",
	"containers": []interface{}{map[string]interface{}{"name": "a1", "image": "x"}}})
mf := fieldpath.ManagedFields{
	"A": fieldpath.NewVersionedSet(fieldpath.NewSet(
		fieldpath.MakePathOrDie("containers", fieldpath.KeyByFields("name", "a1"), "name")), "v1", true),
	"B": fieldpath.NewVersionedSet(fieldpath.NewSet(
		fieldpath.MakePathOrDie("containers", fieldpath.KeyByFields("name", "a1"))), "v1", true)}
_, _, err := updater.Apply(live, typedObj(map[string]interface{}{"name": "o"}), "v1", mf, "A", false)
// err: failed to compare objects: .containers: element 0: associative list with keys has an
// element that omits all key fields ["name"] (and doesn't have default values for any key fields)
```

Either half alone does not fail (the item is then removed whole, or kept with its key). 3000 random
apply/update sequences on the same schema, starting from no managed fields, never produce such sets
(every set SMD computes keeps an item with its key fields), and every `Apply` error in them is a
`Conflicts`.

**Why not an issue:** the managed fields are crafted; the API server writes only the sets SMD
computes. A client can submit `metadata.managedFields` of its own in an update (FieldsV1 can express
a key field without its item), but only on an object it may write, and the outcome is an error on
its later applies, not a panic or a wrong object; no test through the API server was written.

## Proof

no: `Updater.Apply`'s spec takes the premise `keysWithItems` on every managed set
(`Proof/sigs_k8s_io/structured_merge_diff/v7/merge/Defs.lean`; notes/smd-plan.md, "Scope"), which
every set SMD computes has, and states no error outcome in its scope.
