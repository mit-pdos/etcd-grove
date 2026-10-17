# etcd-io/etcd#22265: tests and logs

The report is `notes/pr-verify/etcd-22265.md`. Revisions:

- the PR head `2c43270eb` (etcd-io/etcd `pull/22265/head`), "head" in the log names;
- its upstream base `ee043b39e` (merge-base with `main`), "base";
- the fork branch the proof is of, `mit-pdos/etcd-grove` branch `pr-etcd-22265-goose-lean`
  (the pinned `goose-lean` `09669450f` plus the PR), "fork".

Go toolchain `GOTOOLCHAIN=go1.27.1`. To run a test file against a checkout:
`cp <file> <checkout>/server/storage/mvcc/ && cd <checkout>/server && go test -count=1 -v -run '^<Name>$' ./storage/mvcc/`.
Every test below builds its `watchableStore` by hand (as `watchable_store_test.go` does) and drives
`syncWatchers` by hand, with no background loop, so the results are deterministic. Logs are trimmed
of zap output.

| File | What it shows | Runs against |
|---|---|---|
| `watchable_store_window_cut_test.go` | `TestSyncWatchersWindowCutDeliversAll`, at the **default** `watchBatchMaxRevs` (1000): a watcher on `a` from revision 1, with 1500 puts of `b` and an `a` after them, and (first subtest) another `a` before them. Head: synced after one pass with `[2]` instead of `[2 1503]`, and `[]` instead of `[1502]`: the events past the 1001-revision window are lost. Base and fork: see the logs. | head (FAIL), base (PASS), fork (FAIL) |
| `window-cut-head.log`, `window-cut-base.log`, `fork.log` | Its output (`fork.log` also has the randomized test's summary on the fork). | as named |
| `batchunsynced-head.log`, `batchunsynced-base.log` | etcd's **existing** `TestWatchBatchUnsynced` (`watchable_store_test.go`, unchanged by the PR) with `-timeout 60s`: it hangs on the head (blocked at `watchable_store_test.go:754` waiting for events that never come) and passes on the base. With `watchBatchMaxRevs = 4` and the watch at revision 1, the window `[1, 6)` holds only 4 revisions with events, so the batch has no `moreRev` and the watcher is synced after `[2 3 4 5]`. | head (FAIL, timeout), base (PASS) |
| `random-head.log`, `random-base.log` | #22304's `TestSyncWatchersCohortsRandomized` (`git show pr-verify/etcd-22304:notes/pr-verify/etcd-22304/watchable_store_cohort_random_test.go`), 200 seeds of random watchers, small channels and `watchBatchMaxRevs` from 1 to 6: 198 of the 200 seeds lose events on the head; all pass on the base. | head (FAIL), base (PASS), fork (FAIL, `fork.log`) |
| `sparse-head.log`, `sparse-base.log` | #22304's `TestSyncWatchersSparseWatcherCatchUpPasses` (same directory of `pr-verify/etcd-22304`): one `a` event after 20,000 other revisions. Head: synced in 1 pass with `[]` instead of `[20002]`. | head (FAIL), base (PASS) |
| `scanlimit-head.log`, `scanlimit-base.log` | #22594's `TestSyncWatchersScanLimitDeliversAll` (`git show pr-verify/etcd-22594:notes/pr-verify/etcd-22594/watchable_store_scanlimit_test.go`), `watchBatchMaxRevs = 1`: `[]` instead of `[1102]`, `[]` instead of `[12 1102]`. | head (FAIL), base (PASS) |
| `gap-head.log`, `gap-base.log` | #22594's reviewer test `TestReviewSyncWatchersCutScanSkipsGapEvenWithMoreRev` (`.../etcd-22594/watchable_store_review_gap_test.go`): `[]` instead of `[1052 1102 1103]`. | head (FAIL), base (PASS) |
| `watchable_store_window_overflow_test.go` | `TestSyncWatchersWindowOverflowFutureWatcher`: a future-revision watcher from `Restore` (`minRev = MaxInt64-2`) alone in `unsynced`, so `minRev + watchBatchMaxRevs + 1` overflows `int64`. The scan `[MaxInt64-2, negative)` is empty and the watcher is synced with no response, as on the base: the overflow is harmless. | head (PASS), base (PASS) |
| `overflow-head.log`, `overflow-base.log` | Its output. | as named |
| `watchable_store_review_realpath_test.go` | The reviewer's four tests, on `New(...)` with both background loops and the real `NewWatchStream`/`Watch` API (no hand-driven passes): `TestReviewRealStoreWindowCut` (the window-cut case at default constants: `[2]` instead of `[2 1503]`); `TestReviewRealStoreEveryRevisionSingleWatcher` (one watcher whose key has an event at every revision from its start, 3000 behind: the PR's own reproducer, delivered in full); `TestReviewEveryRevisionTwoWatchers` (the same key, a second watcher from revision 502 chosen with the first: the window starts at the older `minRev`, the younger watcher's batch has fewer than 1000 revisions and no `moreRev`, so it gets 501 events, last 1002, instead of 2500, last 3001); `TestReviewAllCompactedOverflow` (every chosen watcher compacted with a full channel: `chooseAll` returns `MaxInt64`, `maxRev` wraps negative, the scan is empty, no panic, the watcher stays for a retry). Run with `-run 'TestReview(RealStore|EveryRevision|AllCompacted)'`. | head: FAIL, PASS, FAIL, PASS; base: all PASS |
| `review-realpath-head.log`, `review-realpath-base.log` | Their output. | as named |

The rest of the package's tests pass on the fork branch (`go test -count=1 -skip '^TestWatchBatchUnsynced$' ./storage/mvcc/`).
