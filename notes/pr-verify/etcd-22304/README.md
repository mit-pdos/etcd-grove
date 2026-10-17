# etcd-io/etcd#22304: tests and logs

The report is `notes/pr-verify/etcd-22304.md`. Revisions:

- the PR head `09a0b7af2` (etcd-io/etcd `pull/22304/head`);
- its upstream base `80dfedef5` (merge-base with `main`);
- etcd-io/etcd#22265's head `2c43270eb` (`pull/22265/head`), for the comparison;
- the fork branch the proof is of, `mit-pdos/etcd-grove` branch `pr-etcd-22304-goose-lean`
  (the pinned `goose-lean` `09669450f` plus the PR, with its tests).

Every test builds its `watchableStore` by hand, as the PR's own tests do, and drives
`syncWatchers` (and `moveVictims`) by hand: no background loops, so the results are
deterministic. The hand-built store sets `s.store.ReadView`/`WriteView` as `newWatchableStore`
does, so writes notify the synced watchers.

Go toolchain: `GOTOOLCHAIN=go1.27.1`. To run a test against a checkout, from these notes:
`cp <file> <checkout>/server/storage/mvcc/ && cd <checkout>/server && go test -count=1 -v -run <Name> ./storage/mvcc/`.

| File | What it shows | Runs against |
|---|---|---|
| `watchable_store_cohort_random_test.go` | `TestSyncWatchersCohortsRandomized`, 200 seeds. Each seed has 2-9 watchers at random start revisions on 3 keys, channels of 1-3 slots (so some watchers become victims), and `watchBatchMaxRevs` between 1 and 6 (many cohorts, bounded windows). Puts are interleaved with `syncWatchers` and `moveVictims` passes. Every watcher must receive exactly its key's events from its start revision, in order and once. Passes on the PR head (also with 1500 seeds), on the base and on the fork branch. Fails on #22265: events are lost. | PR head, base, #22265, fork branch |
| `random-22304.log`, `random-base.log`, `random-22265.log` | Its output on the PR head, the base and #22265. | as named |
| `watchable_store_sparse_catchup_test.go` | `TestSyncWatchersSparseWatcherCatchUpPasses`: a watcher whose key has 1 event among 20,001 revisions. The test counts the `syncWatchers` passes until the watcher is synced. PR head: 20 passes. Base: 1 pass. #22265: 1 pass, but the event is lost (FAIL). | PR head, base, #22265 |
| `sparse-22304.log`, `sparse-base.log`, `sparse-22265.log` | Its output. | as named |
| `watchable_store_review_test.go` | The reviewer's four tests. `TestReviewSparseWatcherPasses`: 5000 other revisions take 5 passes on the PR head and 1 on the base. `TestReviewSparseWatcherStarves`: with 1500 revisions written between passes (about 15k writes/s at the 100 ms period), the PR head leaves a watcher on a quiet key unsynced after 50 passes, while the base syncs it in pass 1. Both FAIL on the head (the regression) and PASS on the base. `TestReviewCompactedWatcher` (a compacted watcher still gets the compacted response and is removed) and `TestReviewFutureAndVictim` (a future-revision watcher after `Restore` is synced without overflow; a victim from a cut window is resent with `Revision` = window end - 1) PASS on both. | PR head, base |
| `review-22304.log`, `review-base.log` | Their output. | PR head, base |
| `scanlimit-22304.log` | #22594's `TestSyncWatchersScanLimitDeliversAll` (`git show pr-verify/etcd-22594:notes/pr-verify/etcd-22594/watchable_store_scanlimit_test.go`) on the PR head. With its 3 s timeout it fails. With the timeout raised to 180 s it passes after 55 s per subtest: with `watchBatchMaxRevs = 1` the PR scans 2 revisions per 100 ms pass. The watcher is slow to catch up, but it loses nothing. | PR head |
