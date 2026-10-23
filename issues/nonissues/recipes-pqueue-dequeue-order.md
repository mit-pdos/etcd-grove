---
upstream: none
checked: 2026-10-16
links:
---

> Moved to `issues/nonissues/` on 2026-10-23 (review of `issues/INDEX-reviewed.md`): parked (documentation, skipped for now). The review asks whether `Dequeue` is really not linearizable: the linearization point might lie between the read and the delete that goes through, by a prophecy-like argument (see the note at the end).

# recipes: `PriorityQueue.Dequeue`'s "FIFO order" comment, and its order at the claim

**Status**: open (a documentation request; not filed; no fix branch).

## Where

`client/v3/experimental/recipes/priority_queue.go` at the fork's pinned `bc8b52a50`
(`etc/goose.py`; the same text upstream at f061acd09): the comment on `PriorityQueue.Dequeue`,
"Dequeue returns Enqueue()'d items in FIFO order" (lines 44-45). It is copied from
`Queue.Dequeue` (`queue.go`).

## What happens

1. **The order is by priority, not FIFO.** `Enqueue(val, pr)` puts its item under
   `key/%05d(pr)/%016d(n)` (`newSequentialKV`), and `Dequeue` claims the least key under `key/`
   (`WithFirstKey()`). With every key of that shape, that is the least priority value first, and
   FIFO only within one priority.
2. **The least key is the least one at the get's revision, not at the claim.** `Dequeue` gets
   the first key, then claims it with `deleteRevKey` in a separate transaction. An `Enqueue` of a
   higher priority (a smaller key) that lands between the get and the claim is not seen. So
   `Dequeue` can return a lower-priority item while a higher-priority one is present. Nothing in
   the API excludes this: the priority queue is not linearizable as a priority queue. The plain
   queue has no such race, because an item put after the get has a larger mod revision.

Reproduction sketch (no test written): client A calls `Dequeue` on a queue that holds only
priority 5. After A's `Get` returns the priority-5 item, and before A's `deleteRevKey` commits
(a breakpoint, or a delay injected in `claimFirstKey`), client B calls `Enqueue(v, 1)`. A then
returns the priority-5 item while the priority-1 item is present.

## Expected

What a priority queue's comment would promise: items come out in priority order (the smallest
`pr` first), FIFO among equal priorities.

## How the proof handles it

The results are stated at the get's revision, not at the claim:

- `pqueue_min_key`: the least key at the get.
- `pqueue_order`: under the premise `PQKeysWf`, the least `(priority, sequence number)` at the
  get.
- `pqueue_enqueue_order`: the enqueued key is above every key of its priority.

All three are in `Proof/go_etcd_io/etcd/client/v3/experimental/recipes/Results.lean`.
`notes/STATUS.md`, Recipes, "Unit 2" ("Weaker than planned", (3)) and "The whole package".

## Possible fixes

Documentation: "Dequeue returns the item with the highest priority (the smallest `pr`), FIFO
among equal priorities, among the items present when it reads the queue; an item enqueued
concurrently may be dequeued later than a lower-priority one." Making it linearizable would mean
claiming the item in the same transaction that checks that no smaller key exists (a
`Compare` on the range below it), which changes the recipe; that is not proposed.

## Found

2026-10-11, recipes unit 2 (`PriorityQueue.Dequeue`'s proof). Recorded here at the merge of
unit 2 (2026-10-12).

## Linearizability (2026-10-23)

Question from the review: is `Dequeue` really not linearizable, or does a linearization point
between the read and the delete that goes through (chosen by a prophecy on which delete
succeeds) make every history linearizable?

**Answer: the review is right about the scenario above, and wrong about the conclusion.**
The scenario under "What happens" (2.) is linearizable; the prophecy argument works for the
get-then-claim path. But `Dequeue` is still not linearizable, through a different path: the
watch it falls back to after losing a claim. Code read at etcd upstream/main (fetched
2026-10-23): `priority_queue.go` `Dequeue`; `client.go` `claimFirstKey`, `deleteRevKey`;
`watch.go` `WaitPrefixEvents`; the same code as the pinned `bc8b52a50`.

Model: an item is a (key, create revision) pair (a sequence number can be reused once its
key is deleted, so the key alone does not name an item). `Get(q.key, WithFirstKey()...)` is a
linearizable range read with limit 1, sorted by key: the least key under `key/` at its revision
`r`. `deleteRevKey(k, modrev)` succeeds iff `k` is still there unchanged, so each item has at
most one successful delete, by one dequeue attempt.

**The get-then-claim path is linearizable (the prophecy argument).** Linearize each `Enqueue`
at its put's commit, and each `Dequeue` that returns through `claimFirstKey` at the revision
`r` of the `Get` of its *successful* attempt (the attempt whose delete goes through: a prophecy;
failed attempts get no point). Let the abstract queue at a revision be the items put so far
minus those whose remover's point has passed. Since a remover's get precedes its delete, the
abstract queue is a subset of etcd's keys under `key/`. At `r`, the returned item `k` is the
least key in etcd; it is still abstractly present (its one remover is this attempt); so it is
the least in the abstract queue. Gets at the same revision see the same least key, so at most
one of them succeeds: no tie to break. `Enqueue`'s key is above every present key of its
priority (the base-key compare), so FIFO within a priority holds too. The finding's scenario,
an `Enqueue(v, 1)` committing between A's get and A's delete, linearizes as A's dequeue of
the priority-5 item, then the enqueue: legal, since A's get precedes the enqueue's commit.

The empty-queue path is linearizable as well: the get at `r` saw no key, so the first PUT
event at `r_p > r` is the only key under `key/` at `r_p`; linearize the dequeue at `r_p`.

**The lost-claim path is not.** When the get returned one key `k` (`resp.More == false`) and
another dequeuer deletes `k` first, `claimFirstKey` returns nil and `Dequeue` watches from the
*old* revision `r`, where the queue was not empty, and claims the first PUT after `r`. That put
need not be the least item, nor the least at any time. Counterexample (priorities 1 < 2 < 3,
distinct values):

| revision | event |
|---|---|
| r0 | `Enqueue(a, 1)` returns |
| r  | D: `Dequeue` invoked; its `Get` sees only `a` |
| r1 | `Enqueue(c, 3)` returns |
| r2 | `Enqueue(b, 2)` returns |
| r3, r4 | W: `Dequeue` invoked after r2; its `Get` sees `a` (least); its delete of `a` succeeds; W returns `a` |
| r5 | D: delete of `a` fails (`claimFirstKey` returns nil, `More` false); `WaitPrefixEvents` from `r` delivers the PUT of `c` at r1 first; D's delete of `c` succeeds; D returns `c` |
| later | E: `Dequeue` invoked after D returned; returns `b` |

No linearization exists (checked by hand, and by brute force over every ordering of the six
operations that respects real time against a sequential min-priority queue: none is legal, with
or without E). D returns `c`, so at D's point `a` and `b` must be absent. `b` is removed
only by E, whose point is after D returns; so D's point is before `b`'s enqueue at r2, which
completes before W is invoked. Then `a` is still there (only W removes it, and W starts after
r2), so the least item is `a`, not `c`. Without E the history is still not linearizable:
nobody removes `b`, so it is present at every point after r2. All the interleavings are
reachable with two dequeuers and one enqueuer; no fault is needed.

So the finding's claim ("not linearizable as a priority queue") holds, but its example and
its explanation (the get-to-claim window) do not: that window is harmless. The culprit is the
fallback `WaitPrefixEvents(..., resp.Header.Revision, ...)` after a lost claim, which treats
"the first put since a revision at which the queue was non-empty" as "the least item".
Possible fix: after a lost claim with `!resp.More`, retry (`return q.Dequeue()`) instead of
watching; or watch only when the get saw no key. (The plain `Queue.Dequeue` has the same
fallback; whether it breaks FIFO there was not checked.)

**What the documentation promises.** Little: the type is "a multi-reader, multi-writer
distributed queue", `Enqueue` puts a value "with a given priority", and `Dequeue` "returns
Enqueue()'d items in FIFO order" (copied from `Queue`, wrong for a priority queue). Nothing
says strict priority order under concurrency, so this is at most a documentation issue plus a
fault in the obvious reading of "priority queue"; it is still reasonable to keep it in
`nonissues/` as documentation-only, but if it is revived, the reproduction above (a Go test
with a delay injected before `claimFirstKey`'s delete) replaces the one under "What happens",
and the "How the proof handles it" results are unaffected: `pqueue_min_key`'s second disjunct
(the wait path) only says that the items of the get's state were all claimed by others and that
`it` was put at or after the get, which this history satisfies; it does not say `it` was least.
