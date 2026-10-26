---
upstream: known
checked: 2026-10-26
links:
  - etcd-io/etcd#17198 pr closed: same bug and fix (Dequeue panics on a nil event when the watch fails); closed unmerged by the stale bot in 2025-08
---

# clientv3/experimental/recipes: Queue.Dequeue panics when its watch closes

**Status**: fixed in the verified fork: `goose-lean` `0df483bee` (the cherry-pick of `0aa6c6af8`, branch
`recipes-closed-watch-channel`; unit W-Q, 2026-10-16); not yet upstream.

## Summary

`Queue.Dequeue` and `PriorityQueue.Dequeue` (`client/v3/experimental/recipes`) block on an empty queue by watching the queue's prefix. If that watch channel closes before a `PUT` arrives (the client is closed, or etcd cancels the watch because its start revision was compacted), `Dequeue` dereferences a nil event and panics with `invalid memory address or nil pointer dereference`, instead of returning an error. I found this while formally verifying the recipes package.

## What happens

References are to `main` at f061acd0902d489041448cdd19d71a345d27b9f5.

1. `waitEvents` (`client/v3/experimental/recipes/watch.go:45-57`) ranges over the watch channel and returns the awaited event. When the channel closes first, the loop ends and it returns `nil`. `WaitEvents` and `WaitPrefixEvents` (`watch.go:25-43`) then return `(nil, nil)`.

   ```go
   // client/v3/experimental/recipes/watch.go:35-57 (etcd main f061acd09)
   func WaitPrefixEvents(c *clientv3.Client, prefix string, rev int64, evs []mvccpb.Event_EventType) (*clientv3.Event, error) {
   	ctx, cancel := context.WithCancel(context.Background())
   	defer cancel()
   	wc := c.Watch(ctx, prefix, clientv3.WithPrefix(), clientv3.WithRev(rev))
   	if wc == nil {
   		return nil, ErrNoWatcher
   	}
   	return waitEvents(wc, evs), nil // <-
   }

   func waitEvents(wc clientv3.WatchChan, evs []mvccpb.Event_EventType) *clientv3.Event {
   	i := 0
   	for wresp := range wc {
   		for _, ev := range wresp.Events {
   			if ev.Type == evs[i] {
   				i++
   				if i == len(evs) {
   					return ev
   				}
   			}
   		}
   	}
   	return nil // <- the channel closed first
   ```
2. The watch channel closes when the client is closed, when the watch's context is canceled, or when etcd cancels the watch. In the last case the client first delivers a response with `Canceled` set (and `CompactRevision`, for a compacted start revision), whose `Err()` is `ErrCompacted`; `waitEvents` ignores it, since the response has no events.
3. `Queue.Dequeue` (`queue.go:43-77`), on an empty queue, calls `WaitPrefixEvents(q.client, q.keyPrefix, resp.Header.Revision, PUT)`. With `err == nil` it goes on to `deleteRevKey(q.client, string(ev.Kv.Key), ev.Kv.ModRevision)` (`queue.go:70`) with `ev == nil`, and panics. `PriorityQueue.Dequeue` does the same (`priority_queue.go:64-73`).

   ```go
   // client/v3/experimental/recipes/queue.go:60-70 (etcd main f061acd09)
   	// nothing yet; wait on elements
   	ev, err := WaitPrefixEvents(
   		q.client,
   		q.keyPrefix,
   		resp.Header.Revision,
   		[]mvccpb.Event_EventType{mvccpb.Event_PUT})
   	if err != nil {
   		return "", err
   	}

   	ok, err := deleteRevKey(q.client, string(ev.Kv.Key), ev.Kv.ModRevision) // <- ev == nil: panic
   ```

The panic is in the caller's goroutine, so unless the caller recovers, closing a client while another goroutine waits in `Dequeue` crashes the program. The compaction case needs no client shutdown: a compaction past the revision of `Dequeue`'s `Get`, between that `Get` and the watch's registration, is enough.

## How to reproduce

The branch below adds `tests/integration/clientv3/experimental/recipes/v3_closed_watch_test.go`, with:

- `TestQueueDequeueClientClosed` (subtests `Queue` and `PriorityQueue`): `Dequeue` on an empty queue in a goroutine that recovers a panic; after 500 ms, the test closes the dequeuer's client.
- `TestQueueDequeueCompacted`: `Dequeue` on an empty queue while another client puts to an unrelated key and compacts at the new revision in a loop. The compaction cancels the dequeuer's watch in every attempt (5 of 5).
- `TestWaitPrefixEventsCompacted`: `WaitPrefixEvents` from a compacted revision.

On `main`:

```
TestQueueDequeueClientClosed/Queue: Expected nil, but got: "invalid memory address or nil pointer dereference" (Dequeue panicked)
TestQueueDequeueClientClosed/PriorityQueue: Expected nil, but got: "invalid memory address or nil pointer dereference" (Dequeue panicked)
TestQueueDequeueCompacted: Expected nil, but got: "invalid memory address or nil pointer dereference" (Dequeue panicked)
TestWaitPrefixEventsCompacted: An error is expected but got nil. (WaitPrefixEvents returned event <nil> without an error)
```

```
cd tests && go test ./integration/clientv3/experimental/recipes/ -run 'TestQueueDequeueClientClosed|Compacted' -v
```

No existing test encodes the old behaviour; the suite passes unchanged with the fix.

## Expected

`Dequeue` returns an error when it can no longer wait: the client's closing error, or `ErrCompacted` when its watch was canceled by a compaction. `WaitEvents` and `WaitPrefixEvents` never return `(nil, nil)`.

## The fix

Branch `recipes-closed-watch-channel` (one commit, with the tests; it also fixes [recipes-barrier-wait-closed-watch](recipes-barrier-wait-closed-watch.md), which has the same cause). `waitEvents` returns the watch response's `Err()` when the watch is canceled (`ErrCompacted`, for instance), and a new `ErrWatchClosed` (`client.go`) when the channel closes without the events. `WaitEvents` and `WaitPrefixEvents` return that error, and the callers, which already check it, propagate it. After the fix, the client-close case returns `watch channel closed` and the compaction case `etcdserver: mvcc: required revision has been compacted`.

The commit is one commit off `main` (f061acd09), as the other fix branches are.

## How the proof handles it

Until unit W-Q (2026-10-16) the recipes' proofs took the premise that a watch channel never closes
(`isEtcdRangeWatcherOpen`, now deleted), which etcd's client does not meet. Since W-Q the verified
code is the fork with the fix (`goose-lean` `0df483bee`): `waitEvents.spec`
(`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/waitEvents.lean`) is over the closable watch
channel and returns `(ev, nil)` with the awaited event or `(nil, err)` with `err ≠ nil` (a canceled
response's `Err()`, or `ErrWatchClosed`); `WaitEvents.spec`/`WaitPrefixEvents.spec` pass it on, and
`Queue.Dequeue`/`PriorityQueue.Dequeue` take the error branch of their specs (`⌜err ≠ nil⌝`). The
client bundle (`isEtcdRecipesClient`) takes the closable contract `isEtcdRangeWatcher`, which etcd's
client watcher meets (`isEtcdRangeWatcher_of_watcher`), so `queue_end_to_end_client`
(`Proof/go_etcd_io/etcd/client/v3/experimental/recipes/Results.lean`) has no premise about the
watch channel.
