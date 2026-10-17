# Tests and logs for `notes/pr-verify/etcd-21065.md`

Revisions:
- **PR head**: etcd-io/etcd `0efd6744f`.
- **Base**: upstream `b9ba05c8e`, the PR's merge base.
- **Pin**: `goose-lean` `09669450f`.
- **Fork branch**: `mit-pdos/etcd-grove` branch `pr-etcd-21065-goose-lean`, `af6eb0391` (the
  PR applied onto the pin).

Upstream checkouts build with `GOTOOLCHAIN=go1.26.4` and the fork with `go1.27.1`. Set
`TMPDIR` to a large directory.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `watch_send_queue_test.go` | `TestWatchCancelStormLeaksServerWatchers`: a fake etcd-like stream whose `Send` is held while 300 watches close. The cancels beyond the best-effort queue are dropped and never re-sent, even after one more event for each watch (finding 1). `TestWatchRequestProgressDroppedWhenQueueFull`: `RequestProgress` returns `nil` but its request is dropped, and no progress notification comes (finding 2). | PR head, base, fork branch | `cp watch_send_queue_test.go <checkout>/client/v3/ && cd <checkout>/client/v3 && go test -race -count=1 -v -run 'TestWatchCancelStormLeaksServerWatchers\|TestWatchRequestProgressDroppedWhenQueueFull' .` |
| `unit-up-head.log` | Both tests fail at the PR head: 171 of 300 closed watches left on the server; the progress request is dropped. | PR head | as above |
| `unit-up-base.log` | Both pass at the base: 0 left; 1 progress request and a notification. | base | as above |
| `unit-fork-pr.log` | Both fail on the verified fork branch, as at the PR head. | fork branch | as above (go1.27.1) |
| `v3_watch_inprocess_cancel_storm_test.go` | A one-member integration cluster, 2000 watches on one client closed at once. It reads the mvcc watcher gauge (`etcd_debugging_mvcc_watcher_total`), writes each closed watch's key once more and reads the gauge again, then checks that the remaining watch still gets events and that a new watch is created. Two variants: over the in-process client (`v3client`) and over a gRPC connection. | PR head, base, pin, fork branch | `cp v3_watch_inprocess_cancel_storm_test.go <checkout>/tests/integration/ && cd <checkout>/tests && go test -count=1 -v -run CancelStormServerWatchers ./integration/` |
| `integ-up-head.log` | PR head: no deadlock. In-process, 1560 closed watches left on the server; over gRPC, 496. | PR head | as above |
| `integ-up-base.log` | Base: in-process, the stream deadlocks (no event, no new watch; 1883 left); over gRPC, it passes (0 left). | base | as above |
| `integ-fork-pin.log` | Pin: the same as the base (the deadlock of `issues/etcd-watch-cancel-storm-deadlock.md`). | pin | as above (go1.27.1) |
| `integ-fork-pr.log` | Fork branch: as the PR head (1519 left in-process, 1033 over gRPC). | fork branch | as above (go1.27.1) |

The leak counts vary from run to run: in-process, 1393 to 1560 left at the PR head over several
runs; over gRPC, 496 to 1033.

The reviewer's files:

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `v3_watch_inprocess_cancel_storm_persist_test.go` | The integration test (same test names, so use it instead of `v3_watch_inprocess_cancel_storm_test.go`, not beside it), plus: it waits 12 s, sends a second event to every closed watch, and counts again. The leak does not shrink. | PR head | as for `v3_watch_inprocess_cancel_storm_test.go` |
| `integ-head-persist.log` | PR head: 1435 server watchers left in-process and 293 over gRPC, after both rounds of events. | PR head | as above |
| `watch_send_reorder_test.go` | `TestWatchProgressOvertakesCreate`: whether a progress request issued after `Watch` returned can overtake the create. It never does (0 of 40): `Watch` returns only after its `Created`. Needs `watch_send_queue_test.go` beside it. | PR head | `cp watch_send_queue_test.go watch_send_reorder_test.go <checkout>/client/v3/ && go test -count=1 -v -run TestWatchProgressOvertakesCreate .` |
| `race-head.log`, `race-head-reconnect.log` | `go test -race -count=3` of the client's watch tests and of the reconnect/resume integration tests at the PR head: clean (no race on the queue fields). | PR head | `go test -race -count=3 -run Watch .` in `client/v3` (with `watch_send_queue_test.go`, whose two tests fail as expected), and `go test -race -count=3 -run 'TestWatchRecon\|TestWatchResume\|TestWatchStressResumeClose\|TestWatchOverlap' ./integration/clientv3/watch/` in `tests` |
