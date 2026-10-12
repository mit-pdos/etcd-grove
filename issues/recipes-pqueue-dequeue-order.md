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
