# etcd-io/etcd#22594: tests and logs

The report is `notes/pr-verify/etcd-22594.md`. Revisions: the PR head `9b68342c8`
(etcd-io/etcd `pull/22594/head`), its upstream base `d3c8a1559` (merge-base with `main`), and the
fork branch the proof is of, `mit-pdos/etcd-grove` branch `pr-etcd-22594-goose-lean` (the pinned
`goose-lean` `09669450f` plus the PR).

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `watchable_store_scanlimit_test.go` | `TestSyncWatchersScanLimitDeliversAll`: an unsynced watcher loses the events of its key past the PR's bounded scan (it is moved to the synced group at the current revision). Fails on the PR head and on the fork branch, passes on the base. | PR head, base, fork branch | `cp watchable_store_scanlimit_test.go <checkout>/server/storage/mvcc/ && cd <checkout>/server && go test -count=1 -run TestSyncWatchersScanLimitDeliversAll ./storage/mvcc/` |
| `watchable_store_rangeevents_limit_test.go` | `TestRangeEventsLimitIsPrefix`: `rangeEvents` with a limit that cuts the range returns bbolt's first entries then all of the read buffer's, not the first `limit` events (`issues/etcd-backend-readtx-range-limit-not-prefix.md`). Fails on the PR head (the base's `rangeEvents` has no limit parameter). | PR head | `cp watchable_store_rangeevents_limit_test.go <checkout>/server/storage/mvcc/ && cd <checkout>/server && go test -count=1 -run TestRangeEventsLimitIsPrefix ./storage/mvcc/` |
| `head-test.log` | Both tests' output on the PR head. | PR head | as above, `-run 'TestSyncWatchersScanLimitDeliversAll\|TestRangeEventsLimitIsPrefix'` |
| `base-test.log` | `TestSyncWatchersScanLimitDeliversAll` passing on the base. | base | as above |
| `watchable_store_review_gap_test.go` | (the reviewer's) `TestReviewSyncWatchersCutScanSkipsGapEvenWithMoreRev`: with the scan cut and part of the range in the read buffer, a watcher's batch overflows on buffered events after the gap, its `moreRev` points past the gap, and the gap's event (1052) is never delivered. Drives `syncWatchers` by hand (no sync loops, no periodic commit): deterministic. Fails on the PR head, passes on the base. | PR head, base | `cp watchable_store_review_gap_test.go <checkout>/server/storage/mvcc/ && cd <checkout>/server && go test -count=1 -run TestReviewSyncWatchersCutScanSkipsGapEvenWithMoreRev ./storage/mvcc/` |
| `gap-head.log`, `gap-base.log` | Its output on the PR head and on the base. | PR head, base | as above |

Go toolchain: `GOTOOLCHAIN=go1.27.1`.
