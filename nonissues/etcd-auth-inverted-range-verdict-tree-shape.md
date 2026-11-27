---
upstream: none
checked: 2026-11-27
links: []
blocks-proof: no
---

# auth: the permission check of an inverted range depends on the order the permissions were inserted

A `DeleteRange`, a `Range` or a transaction's compare or operation whose range end is below its key
(`[e, b)`, an empty range) is permitted or refused depending on the shape of the user's permission
interval tree, not on the permissions: the same two permissions inserted in the two orders give the two
answers. An empty range (`[a, a)`) or an inverted one is refused to a user without a permission around
its key, although it names no key.

**Why not an issue:** not a guarantee etcd makes: an inverted or empty range selects no key, etcd
documents nothing of its permission check, and a refusal of a request that does nothing loses nothing
a client relies on. Measured: `q2_contains_test.go` in `../notes/axiom-review/q2-shape-gotest/` (the
tree-shape dependence, `pkg/adt`) and `q2_shape_test.go` (the refusals, an integration cluster), at the
etcd fork's `8c28a4296`.

**How:** `isRangeOpPermitted` sends a non-empty range end to `checkKeyInterval`
(`server/auth/range_perm_cache.go`), which asks `IntervalTree.Contains` of `[key, end)`. For an inverted
query, `Interval.Compare` with a node is `0` exactly when the node contains the query's begin, and
`intervalNode.visit` prunes a subtree by comparing `[node begin, max)` with the query, which looks at the
query's end: a node whose interval lies in `[end, begin]` cuts off a right subtree that contains the
begin. `Contains` then answers from the nodes visited (`pkg/adt/interval_tree.go`).

## Proof

no for the top-level results: the auth-on specs require the request shape the cache decides
(`auth.reqShape`, `kvShapeAll`), where `Contains` answers by the permission set. It is why the shape
cannot be dropped for transactions (`notes/specs-only/ledger.md`, 2026-11-27, "Q2 widening stopped"): the
model grants these requests (`coversRange` is vacuous over an empty range).

## Notes

A fix: `isRangeOpPermitted` could answer an empty or inverted range without the tree (grant it, as it
names no key, or refuse it), or `checkRangeRequest`/`checkTxnRequest` could refuse it in `api/v3rpc`.
