# etcd-io/etcd#22295: tests, probes and logs

The files the report (`notes/pr-verify/etcd-22295.md`) relies on. Revisions: the PR head
`2219f4914` (etcd-io/etcd, `pull/22295/head`), the pinned base `09669450f` (the fork's
`goose-lean`, `etc/goose.py`'s etcd pin), and the fork branch with the PR applied
(`mit-pdos/etcd-grove` branch `pr-etcd-22295-goose-lean`, commit `6f4851754`). Every command runs in
`server/` of a checkout of the named revision, with `GOTOOLCHAIN=go1.27.1`.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `watchable_store_test.go` | The PR's own `server/storage/mvcc/watchable_store_test.go` (at its head), with `TestWatchCompactedWatcherRemovedFromUnsyncedWhenCapped`: in the capped branch of `choose` a compacted watcher stays in the unsynced group and gets a second compaction response. Fails at the base (the pre-existing bug, `issues/etcd-watch-choose-capped-compacted-stays-unsynced.md`), passes with the PR. | `09669450f` (fails), `2219f4914` and `6f4851754` (pass) | `cp watchable_store_test.go storage/mvcc/ && go test -run TestWatchCompactedWatcherRemovedFromUnsyncedWhenCapped ./storage/mvcc/` |
| `watcher_group_choose_negative_test.go` | `choose` with a negative `maxWatchers`: an empty group before the PR, a `makeslice: cap out of range` panic with it (the reason `choose.spec` gained the premise `0 ≤ maxWatchers`). Not reachable from etcd (the only caller passes `maxWatchersPerSync`, 512). | `09669450f` (passes), `2219f4914` (fails: panic) | `cp watcher_group_choose_negative_test.go storage/mvcc/ && go test -run TestWatcherGroupChooseNegativeMax ./storage/mvcc/` |
| `base-09669450f-compacted-capped.log` | The first test's failure at the base ("compacted watchers should be removed from the unsynced group: expected 0, actual 2"). | `09669450f` | as above |
| `prhead-2219f4914.log` | Both tests at the PR head: the first passes, the second panics. | `2219f4914` | `go test -v -run 'TestWatchCompactedWatcherRemovedFromUnsyncedWhenCapped\|TestWatcherGroupChooseNegativeMax' ./storage/mvcc/` |
| `watcher_group_choose_capped_mix_test.go` | The reviewer's test: cap 2, three compacted watchers, three live ones and one compacted watcher whose channel is full, then everything cancelled. With the PR each compacted watcher gets exactly one compaction response and leaves `unsynced`, the live ones end in `synced`, the full-channel one stays unsynced and gets its response once the channel drains, and `watcherGauge`/`slowWatcherGauge` return to their starting values. At the base 4 watchers stay unsynced instead of 1. | `2219f4914` (passes), `09669450f` (fails) | `cp watcher_group_choose_capped_mix_test.go storage/mvcc/ && go test -run TestWatcherGroupChooseCappedMix ./storage/mvcc/` |
| `capped-mix-prhead-2219f4914.log`, `capped-mix-base-09669450f.log` | That test's output at the PR head and at the base. | as named | as above |
