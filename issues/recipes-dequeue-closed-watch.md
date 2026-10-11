# clientv3/experimental/recipes: Queue.Dequeue panics when its watch closes

## Summary

`Queue.Dequeue` and `PriorityQueue.Dequeue` (`client/v3/experimental/recipes`) block on an empty queue by watching the queue's prefix. If that watch channel closes before a `PUT` arrives (the client is closed, or etcd cancels the watch because its start revision was compacted), `Dequeue` dereferences a nil event and panics with `invalid memory address or nil pointer dereference`, instead of returning an error. I found this while formally verifying the recipes package.

## What happens

References are to `main` at f061acd0902d489041448cdd19d71a345d27b9f5.

1. `waitEvents` (`client/v3/experimental/recipes/watch.go:45-57`) ranges over the watch channel and returns the awaited event. When the channel closes first, the loop ends and it returns `nil`. `WaitEvents` and `WaitPrefixEvents` (`watch.go:25-43`) then return `(nil, nil)`.
2. The watch channel closes when the client is closed, when the watch's context is canceled, or when etcd cancels the watch. In the last case the client first delivers a response with `Canceled` set (and `CompactRevision`, for a compacted start revision), whose `Err()` is `ErrCompacted`; `waitEvents` ignores it, since the response has no events.
3. `Queue.Dequeue` (`queue.go:43-77`), on an empty queue, calls `WaitPrefixEvents(q.client, q.keyPrefix, resp.Header.Revision, PUT)`. With `err == nil` it goes on to `deleteRevKey(q.client, string(ev.Kv.Key), ev.Kv.ModRevision)` (`queue.go:70`) with `ev == nil`, and panics. `PriorityQueue.Dequeue` does the same (`priority_queue.go:64-73`).

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
