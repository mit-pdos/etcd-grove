---
upstream: none
checked: 2026-11-19
links: []
blocks-proof: no
---

# structured-merge-diff: managed fields that split a list item from its key field make Apply fail, report a spurious conflict, or return duplicate keys

`merge.Updater.Apply` (structured-merge-diff v7.0.0) can strip a key field off an associative list
item it keeps, when the managed fields it is given split the item from its key field. Pruning
(`Updater.prune`) removes the key field (the applier applied it last time, no one else owns it) and
keeps the item (another manager owns it). Three outcomes follow, all Go-reproduced:

1. **A non-conflict error.** The applier's previous set has the item's key field
   (`.containers[name="a1"].name`) but not the item; another manager's set has the item but not its
   key field. `TypedValue.Compare` of the live object with the pruned one cannot compute the item's
   key: `failed to compare objects: .containers: element 0: associative list with keys has an element
   that omits all key fields ["name"] ...` (or, for a `null` item, `associative list with keys may
   not have a null element`).
2. **The same through a path below the key field** (review round 1, 2026-11-19): A's set has only
   `.containers[name="a1"].name.x`, a path *below* the scalar key field, and B's has the item and its
   key field. `EnsureNamedFieldsAreMembers` makes `.containers[name="a1"].name` a member of A's set
   (it has a path below it), so the third pruning pass (`addBackDanglingItems`) removes the key field
   from an item another manager keeps: the same error as (1), though the earlier form of the premise
   (no key field without its item) holds of both sets.
3. **A spurious conflict, or duplicate keys when forced.** `ports` keyed by `[port, proto]`, the live
   list `[{port: 1, proto: b}, {proto: b}]`, A owning `ports[proto=b]` and its `proto`, C owning
   `ports[port=1,proto=b].port.x`. C applies `{}`: pruning strips `port` from the first item, whose
   key becomes `(proto=b)`, a duplicate. Without force `Apply` reports
   `Conflicts{A: .ports[proto="b"]}` though nothing of A's changed; with force it returns
   `{"ports": [{"proto": "b"}, {"proto": "b"}]}` and no error, an object `AsTyped` rejects
   (`duplicate entries for key [proto="b"]`).

Reproductions: the round-1 reviewer's tests `keyless_test.go` and `dupkey_test.go` (a throwaway
module against v7.0.0; the driver's schema of `examples/k8s/smd`, and a schema with two-key lists),
and for (1):

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

Random apply/update sequences on these schemas, starting from no managed fields (10 000 sequences,
about 60 000 steps), never produce such sets: every set SMD computes keeps an item with its key
fields and has no path below a scalar, and every `Apply` error in them is a `Conflicts`.

**Why not an issue:** the managed fields are crafted; the API server writes only the sets SMD
computes. A client can submit `metadata.managedFields` of its own in an update (FieldsV1 can express
a key field without its item, or `f:name: {f:x: {}}` below a key field), but only on an object it may
write; the outcomes are an error or a spurious conflict on later applies, or, forced, a stored object
with duplicate keys. No test through the API server was written. Service and container ports are
keyed by two fields, so (3) is the one to try there.

## Proof

no: `Updater.Apply`'s spec takes the premise `keysWithItems` on every managed set
(`Proof/sigs_k8s_io/structured_merge_diff/v7/merge/Defs.lean`; notes/smd-plan.md, "Scope"): an item's
key fields come with the item, the item with its key fields (granular items), and **no path extends a
key field's path** (the third clause, added after review round 1: the first form admitted (2) and
(3), so the spec's claim of no other outcome was false). Every set SMD computes has it, and `Apply`
and `Update` keep it (`applyResult_premise`, `updateResult_premise`), so the driver discharges it by
chaining; under it the spec states no error outcome but conflicts.
