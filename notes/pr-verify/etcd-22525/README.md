# etcd-io/etcd#22525: tests and tools

The files the report `notes/pr-verify/etcd-22525.md` relies on. Revisions: the fork pin `09669450f`
(`etc/goose.py`, branch `goose-lean` of `upamanyus/etcd`); the fork with the PR, `mit-pdos/etcd-grove`
branch `pr-etcd-22525-goose-lean` (`cd4d431d1`: the PR's diff, tests included, applied cleanly onto
`09669450f`); the PR head `429b52576`.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `astdiff.go` | Lists the declarations (functions, methods, types) that differ between two versions of a Go file, by comparing their printed ASTs (comments dropped): here `start`, `publishV3`, `applySnapshot` changed, `hasPublishedAttributes` new, `type EtcdServer` changed. | `09669450f` vs `cd4d431d1`, `server/etcdserver/server.go` | `git -C ~/etcd show 09669450f:server/etcdserver/server.go > old.go.txt; cp <fork>/server/etcdserver/server.go new.go.txt; go run astdiff.go old.go.txt new.go.txt` |
| `server_publish_restart_test.go` | A probe of the PR description's claim that a restarting member "still publishes through raft": `TestPublishV3RestartWaitsWithoutSnapshot` (store already holding the attributes, no snapshot: the attempt keeps waiting, passes) and `TestPublishV3RestartCompletedBySnapshot` (the same member, one snapshot applied during the attempt: `publishV3` returns and the server is ready without its entry, passes). The second is correct behavior (the attributes are equal), but it shows the claim holds only while no snapshot arrives. Needs the PR's `server_test.go` (`newPublishTestServer`). | `cd4d431d1` (the PR head's `server.go` is the same) | from `server/`: `cp <file> etcdserver/ && go test -count=1 -v -run TestPublishV3 ./etcdserver/` (GOTOOLCHAIN=go1.27.1) |
| `test-fork-pr.log` | Its output with the PR's own `TestPublishV3*` tests: all pass. | `cd4d431d1` | the same |
| `server_publish_stale_applied_test.go` | `TestReadyBySnapshotWithStaleAppliedIndex`: with the PR, a member that becomes ready on a leader snapshot (simulated: committed index 20000 as raft reports it, the membership updated and the notifier notified as `applySnapshot` does, `s.appliedIndex` left at 0 as `applySnapshot` leaves it, `issues/etcd-snapshot-applied-index-stale.md`) is ready, and a write through it fails with `ErrTooManyRequests` before reaching raft (passes: it shows the state). Needs the PR's `server_test.go`. | `cd4d431d1` | from `server/`: `cp <file> etcdserver/ && go test -count=1 -v -run TestReadyBySnapshotWithStaleAppliedIndex ./etcdserver/` |
| `test-stale-applied-fork-pr.log` | Its output. | `cd4d431d1` | the same |
