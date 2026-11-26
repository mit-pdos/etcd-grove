---
upstream: none
checked: 2026-11-25
links: []
blocks-proof: no
---

# etcd-grove `examples/etcd/dist/client`: `Rotate`'s doc does not state that `i` must be non-negative and `i + len(xs)` must fit in an `int`

`Rotate(xs, i)` indexes `xs[(i+j)%k]` for `j < k = len(xs)`. Go's `%` keeps the sign of its left
operand, so a negative `i` (with `-i` not a multiple of `k`) gives a negative index and panics; an
`i` near `math.MaxInt` overflows `i+j` to a negative number, with the same result. Its doc ("xs from
its i-th (mod len) element on") says neither.

**Why not an issue:** this repository's own example code, documentation only: every caller
(`NodeMain`, the client machines' endpoints) passes a client machine's index `c`, which `NodeMain`
has already checked to be `0 ≤ c < NodeCount(w)`, with a well-formed deployment's client count below
`2^31` and at most 64 endpoints. The doc could add "i ≥ 0" (or the function could take
`((i % k) + k) % k`).

## Proof

no: `Rotate.spec` (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/Rotate.lean`) takes
`xs ≠ [] → 0 ≤ i ∧ i + len(xs) ≤ 2^63`, which `NodeMain` meets from its guard and the deployment's
bounds (`kvOnly_bounds`).

## Notes

Found by the N7-kv spec review (2026-11-25, `notes/etcd-dist-n7kv.md`).
