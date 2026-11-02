---
upstream: known
checked: 2026-11-01
links:
  - etcd-io/etcd#17198 pr closed: same root cause, different symptom (waitEvents returns nil on a closed watch; its fix makes WaitEvents return an error, which would fix Barrier.Wait too; written for Dequeue); closed unmerged by the stale bot
blocks-proof: yes
---

# recipes: Barrier.Wait reports the barrier released when its watch closes while the barrier is still held

`Barrier.Wait` (`client/v3/experimental/recipes`) returns `nil`, meaning "released", when the watch
it waits on closes before the barrier key is deleted (the client is closed, or etcd cancels the watch
because its start revision was compacted), although the barrier is still held.
`DoubleBarrier.Enter` likewise returns `nil` before `count` processes have entered.

**Reproduction:** `TestBarrierWaitClientClosed` and `TestDoubleBarrierEnterClientClosed` in
[`issues/recipes-barrier-wait-closed-watch/v3_barrier_closed_watch_test.go`](recipes-barrier-wait-closed-watch/v3_barrier_closed_watch_test.go),
copied into `tests/integration/clientv3/experimental/recipes` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28), go1.27.3:

```
$ go test ./integration/clientv3/experimental/recipes -run '^(TestBarrierWaitClientClosed|TestDoubleBarrierEnterClientClosed)$' -count=1
--- FAIL: TestBarrierWaitClientClosed (0.67s)
        	Error:      	An error is expected but got nil.
        	Messages:   	Wait returned nil (released) while the barrier is held
--- FAIL: TestDoubleBarrierEnterClientClosed (0.69s)
        	Error:      	An error is expected but got nil.
        	Messages:   	Enter returned nil with 1 of 2 entrants
FAIL
```

## Proof

yes: the verified fork carries the fix (`goose-lean` `0df483bee`, the cherry-pick of `0aa6c6af8`);
before it the recipes' proofs took the premise that a watch channel never closes, which etcd's
client does not meet (`Proof/go_etcd_io/etcd/client/v3/experimental/recipes/InvRecipesClient.lean`).

## Fix

**Branch**: `recipes-closed-watch-channel` (upamanyus/etcd, pushed): 0aa6c6af8 test and fix (one commit; the same as [recipes-dequeue-closed-watch](recipes-dequeue-closed-watch.md))
**Base**: etcd-io/etcd@f061acd0902d489041448cdd19d71a345d27b9f5

`WaitEvents` returns an error when the watch closes or is canceled, and `Wait` and `Enter` already
return `WaitEvents`' error.

## Notes

The [Go doc](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/experimental/recipes/barrier.go#L50-L51)
says `Wait` "blocks on the barrier key until it is deleted", which is the guarantee the test
asserts. The 2026-10 review doubted the barrier is meant to be that strong (#17198 went stale); the
compaction trigger needs no client shutdown, but is a narrow race between `Wait`'s `Get` and its
watch. `DoubleBarrier.Leave` and `RWMutex.Lock`/`RLock` re-read after a closed watch, so they only
retry.
