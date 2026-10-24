# Reproduction & Probe Tests for `etcd-io/etcd#22269`

- `watchable_store_test.go`: `TestWatchVictims` from `etcd-io/etcd#22269`, which runs `watchableStore` inside a `testing/synctest` bubble.
- `watch_victims_head.log`: Output of running `TestWatchVictims` on `pr-etcd-22269-goose-lean` (`e0d3628f1b3d977e0b47ae1fd17c221ab65528d5`, clamping `syncDuration` to at least `time.Nanosecond`), passing in `0.04s` (`100ms` simulated time).
- `watch_victims_unclamped.log`: Output of running `TestWatchVictims` on the upstream `main` `syncWatchersLoop` without clamping `syncDuration` (and without `resyncDelay`), crashing in `0.015s` with `panic: non-positive interval for Ticker.Reset` (`issues/etcd-watch-sync-ticker-reset-zero.md`).
- `watch_victims_resyncdelay.log`: Output of running `TestWatchVictims` on `goose-lean` (`bc9c3868ced67e518fb2fecba44ce0fa70b7303b`, which uses `resyncDelay` from `etcd-io/etcd#22297`), passing in `0.05s` (`12.8s` simulated time, since `resyncDelay` falls back to `watchResyncPeriod = 100ms` when `syncDuration == 0`).

## Running

```bash
cd /root/etcd-pr/etcd-22269/server
go test -v -count=1 -run '^TestWatchVictims$' ./storage/mvcc
```
