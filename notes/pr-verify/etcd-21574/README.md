# Files for the verification of etcd-io/etcd#21574

Revisions: the fork pin `09669450f` (`goose-lean`, the base), the fork with the PR
`5d8168137` (`mit-pdos/etcd-grove` branch `pr-etcd-21574-goose-lean`), the upstream PR head
`2d00f549c`, its upstream merge base `10528e6f2`, and the PR head with
`shouldSnapshotToDisk-fix.patch` ("fixed"). Fork checkouts build with `GOTOOLCHAIN=go1.27.1`, upstream
ones with `GOTOOLCHAIN=go1.26.1`. Set `TMPDIR` to a large directory for every `go test`.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `shouldsnapshot_test.go` | `shouldSnapshotToDisk` asks for a disk snapshot only past `SnapshotCount`: passes on the base, fails on the PR (true at `appliedi=1`, `diskSnapshotIndex=0`, count 10000) | base, fork+PR, PR head, fixed | `cp shouldsnapshot_test.go <checkout>/server/etcdserver/ && cd <checkout>/server && go test -run TestShouldSnapshotToDiskSnapshotCount ./etcdserver/` |
| `snapshot_count_test.go` | one embedded member, 20 puts, default snapshot count: the WAL holds 1 snapshot record on the base, 24 on the PR (a disk snapshot per applied batch) | same | `cp snapshot_count_test.go <checkout>/server/embed/ && cd <checkout>/server && go test -v -run TestSnapshotCountRespected ./embed/` |
| `probes.log` | the two tests' output on base, fork+PR and PR head, plus the existing `TestApplyRepeat` (passes on the base, nil-pointer panic in `snapshot()`'s `s.KV().Commit()` on the PR: the unit-test servers have no KV and never expected a disk snapshot) | base, fork+PR, PR head | as above |
| `fork-tests.log` | `go test ./etcdserver/ ./etcdserver/apply/ ./storage/...` in `server/`: all pass on the base; `./etcdserver/` panics on the PR | base, fork+PR | `cd <checkout>/server && go test ./etcdserver/ ./etcdserver/apply/ ./storage/...` |
| `shouldSnapshotToDisk-fix.patch` | the obvious repair (count rule alone), relative to the PR head; it is NOT safe (next rows) | applies to the PR head | `git apply` |
| `fixed-tests.log` | with the patch, `./etcdserver/`, `./etcdserver/apply/` and `./embed/` (with both tests above) pass | fixed | `cd server && go test ./etcdserver/ ./etcdserver/apply/ ./embed/` |
| `downgrade_wal_test.go` | (reviewer's) after a single-member downgrade, which `ClusterVersionSet` entries naming the newer version come after the latest WAL snapshot record (what a restart replays): none on base, fork+PR and PR head; index 4 on fixed | all four | `cp downgrade_wal_test.go <checkout>/server/embed/ && cd <checkout>/server && go test -v -run TestReviewDowngradeWALReplay ./embed/` |
| `forcecommit_after_close_test.go` | (reviewer's) `ForceCommit` on a closed backend whose pre-commit hook writes panics (nil transaction); shows the postulated `srvBackendCommits` contract is false of a closed backend (not reachable from the server: see the report) | base, fork+PR, PR head, fixed (fails on all) | `cp forcecommit_after_close_test.go <checkout>/server/storage/backend/ && cd <checkout>/server && go test -run TestReviewForceCommitAfterClose ./storage/backend/` |
| `review-probes.log` | the two reviewer tests' output on all four checkouts | all four | as above |
| `e2e-downgrade.log` | etcd's e2e `TestDowngradeUpgradeClusterOf1` with `bin/etcd-last-release` = v3.6.15 (`release-3.6` `f31a5aa5c`): passes on the upstream base and the PR head; on fixed, the 3.6 member panics on restart in `MustDetectDowngrade` from `SetVersion`, replaying `ClusterVersionSet` | upstream base, PR head, fixed | build `bin/etcd`, `bin/etcdctl`, `bin/etcdutl` in the checkout (`go build -o ../bin/etcd .` in `server/`, likewise `etcdctl/`, `etcdutl/`) and `bin/etcd-last-release` from `release-3.6`'s `server/` (`GOTOOLCHAIN=go1.26.9`); then `cd tests && go test ./e2e/ -run 'TestDowngradeUpgradeClusterOf1$' -bin-dir=<checkout>/bin -v` |
