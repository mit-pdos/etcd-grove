---
upstream: none
checked: 2026-10-16
links:
blocks-proof: no
---
# recipes: PriorityQueue.Dequeue's "FIFO order" comment, and its order under concurrent dequeuers

`PriorityQueue.Dequeue` (`client/v3/experimental/recipes`) is documented as returning items "in
FIFO order", a comment copied from `Queue.Dequeue`: it returns the least priority value first, FIFO
only within a priority. And with two concurrent dequeuers, one whose claim loses the race falls back
to a watch from its old read and takes the first item put since then, which need not be the
highest-priority item present, so the queue is not linearizable as a priority queue.

**Why not an issue:** documentation only, and no test: the Go doc promises neither priority order
nor linearizability under concurrency (found by code reading; the non-linearizable history below
was checked by hand and by brute force, not run).

## Proof

no: the results are stated at the `Get`'s revision, not at the claim (`pqueue_min_key`,
`pqueue_order` under `PQKeysWf`, `pqueue_enqueue_order` in
`Proof/go_etcd_io/etcd/client/v3/experimental/recipes/Results.lean`); the history below satisfies
them.

## Notes

- **The get-to-claim window is harmless** (the 2026-10-23 review's prophecy argument holds): linearize
  a `Dequeue` that returns through `claimFirstKey` at the `Get` of its successful attempt, and an
  `Enqueue` at its put; an `Enqueue(v, 1)` committing between a dequeuer's `Get` and its delete
  linearizes after that dequeue.
- **The lost-claim path is not linearizable.** When the `Get` returned one key `k` and another
  dequeuer deletes `k` first, `Dequeue` watches from the `Get`'s revision `r` and claims the first
  put after `r`. Priorities 1 < 2 < 3: `Enqueue(a,1)`; D's `Get` sees only `a`; `Enqueue(c,3)`;
  `Enqueue(b,2)`; W's `Dequeue` claims and returns `a`; D's delete of `a` fails, its watch from `r`
  delivers `c`'s put first, D returns `c` while `b` is present. No linearization exists (with or
  without a later `Dequeue` returning `b`); no fault needed. `Queue.Dequeue` has the same fallback;
  whether it breaks FIFO there was not checked.
- A test could promote this: two dequeuers and one enqueuer, with a delay injected before
  `claimFirstKey`'s delete. Fixes: after a lost claim with `!resp.More`, retry instead of watching;
  and the comment: "the smallest `pr` first, FIFO among equal priorities".
- [Permalink, the comment](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/experimental/recipes/priority_queue.go#L44-L46).
