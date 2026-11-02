---
upstream: known
checked: 2026-11-01
links:
  - etcd-io/etcd#17198 pr closed: same bug and fix (Dequeue panics on a nil event when the watch fails); closed unmerged by the stale bot in 2025-08
blocks-proof: yes
---

# recipes: Queue.Dequeue panics when its watch closes

`Queue.Dequeue` and `PriorityQueue.Dequeue` (`client/v3/experimental/recipes`) block on an empty
queue by watching the queue's prefix. If that watch closes before an item arrives (the client is
closed, or etcd cancels the watch because its start revision was compacted), `Dequeue` dereferences
a nil event and panics with `invalid memory address or nil pointer dereference` in the caller's
goroutine, instead of returning an error. `WaitEvents` and `WaitPrefixEvents` return `(nil, nil)`
in that case.

**Reproduction:** `TestQueueDequeueClientClosed` (subtests `Queue`, `PriorityQueue`),
`TestQueueDequeueCompacted` and `TestWaitPrefixEventsCompacted` in
[`issues/recipes-dequeue-closed-watch/v3_dequeue_closed_watch_test.go`](recipes-dequeue-closed-watch/v3_dequeue_closed_watch_test.go),
copied into `tests/integration/clientv3/experimental/recipes` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28), go1.27.3:

```
$ go test ./integration/clientv3/experimental/recipes -run '^(TestQueueDequeueClientClosed|TestQueueDequeueCompacted|TestWaitPrefixEventsCompacted)$' -count=1
--- FAIL: TestQueueDequeueClientClosed (1.18s)
    --- FAIL: TestQueueDequeueClientClosed/Queue (0.50s)
            	Error:      	Expected nil, but got: "invalid memory address or nil pointer dereference"
            	Messages:   	Dequeue panicked
    --- FAIL: TestQueueDequeueClientClosed/PriorityQueue (0.50s)
            	Error:      	Expected nil, but got: "invalid memory address or nil pointer dereference"
            	Messages:   	Dequeue panicked
--- FAIL: TestWaitPrefixEventsCompacted (0.21s)
        	Error:      	An error is expected but got nil.
        	Messages:   	WaitPrefixEvents returned event <nil> without an error
--- FAIL: TestQueueDequeueCompacted (0.20s)
        	Error:      	Expected nil, but got: "invalid memory address or nil pointer dereference"
        	Messages:   	Dequeue panicked
FAIL
```

## Proof

yes: the verified fork carries the fix (`goose-lean` `0df483bee`, the cherry-pick of `0aa6c6af8`);
before it the recipes' proofs took the premise that a watch channel never closes, which etcd's
client does not meet (`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/waitEvents.lean`,
`Proof/go_etcd_io/etcd/client/v3/experimental/recipes/InvRecipesClient.lean`).

## Fix

**Branch**: `recipes-closed-watch-channel` (upamanyus/etcd, pushed): 0aa6c6af8 test and fix (one commit; also fixes [recipes-barrier-wait-closed-watch](recipes-barrier-wait-closed-watch.md))
**Base**: etcd-io/etcd@f061acd0902d489041448cdd19d71a345d27b9f5

`waitEvents` returns the canceled watch response's `Err()` (e.g. `ErrCompacted`) and a new
`ErrWatchClosed` when the channel closes without the events; `WaitEvents`/`WaitPrefixEvents`
return it and the callers, which already check it, propagate it. Supporting or reviving #17198 (the
same fix) is the alternative to a new PR.
