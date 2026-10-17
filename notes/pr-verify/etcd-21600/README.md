# Files for `notes/pr-verify/etcd-21600.md`

Each test is named as it would be in etcd's `cache` package (`package cache`, internal tests).

- **`prevkv_probe_test.go`**: two tests of the PR's new code.
  - Runs against:
    - the PR head `d14b7d49441eebddd3031e40bb8a7aaa0bcb6784` (etcd-io/etcd, `GOTOOLCHAIN=go1.26.4`);
    - `mit-pdos/etcd-grove` branch `pr-etcd-21600-goose-lean` (`GOTOOLCHAIN=go1.27.1`).
  - Both tests fail on both revisions.
  - Command: `cp prevkv_probe_test.go <checkout>/cache/ && cd <checkout>/cache && go test -count=1 -run 'TestCacheWatchPrevKVSlowConsumerLosesPrevKV|TestStoreWaitForRevLostWakeup' -v .`
  - Output on the PR head: `prevkv_probe.log`.
  - `TestCacheWatchPrevKVSlowConsumerLosesPrevKV` (deterministic) shows that a `WithPrevKV` watch which reads slower than the store's history window gets update events with `PrevKv == nil` for a key that existed, and the watch is not canceled.
    - Setup: `WithHistoryWindowSize(4)`, ten puts of `/a`, and the watch read only after the store has applied them all.
    - Result: 6 of the 10 events arrive without their previous value.
  - `TestStoreWaitForRevLostWakeup` (a race, typically hit in under 5000 iterations) shows that `store.waitForRev` misses its context's cancellation.
    - Cause: `context.AfterFunc(ctx, s.revCond.Broadcast)` broadcasts without the store's lock, and the broadcast is lost when it lands between the waiter's `s.latest.rev < rev` check and its `Wait()`.
    - Effect: `waitForRev` sleeps until the store's revision next changes.
- **`waittillrevision_probe_test.go`**: `TestWaitTillRevisionLostCancelWakeup`, deterministic, for `issues/cache-waittillrevision-lost-wakeup.md`.
  - It shows the same lost wakeup in the existing `Cache.waitTillRevision`. The test's context is canceled while its first `Err()` call is running, which is a cancel racing with the waiter's check.
  - Result: `waitTillRevision` (with `WaitTimeout` 3s) is still blocked after 5s.
  - Runs against the pinned fork `09669450f` (`goose-lean`, `GOTOOLCHAIN=go1.27.1`).
  - Command: `cp waittillrevision_probe_test.go <fork>/cache/ && cd <fork>/cache && go test -count=1 -run TestWaitTillRevisionLostCancelWakeup -v .`
  - Output: `waittillrevision_probe.log`.
