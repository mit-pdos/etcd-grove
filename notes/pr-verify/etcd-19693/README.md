# etcd-io/etcd#19693: the tests and logs behind the report

The report is `../etcd-19693.md`. Revisions:

- **PR head**: upstream `05e2b0b1ed23085db060de5a6c57c977e7c0dece` (`git fetch upstream pull/19693/head`).
- **PR base**: upstream `8784cf561` (the PR's first commit, "Remove v2 store", on its merge base
  `780aef5f6`; the PR's other two commits are what it changes beyond upstream, which has that
  first commit as `fdedec1ed`).
- **fork PR**: `mit-pdos/etcd-grove` branch `pr-etcd-19693-goose-lean` (`594370526`), the verified
  code: the fork's `goose-lean` `09669450f` plus the PR's commits 2-3.
- **fork base**: the fork's `goose-lean` `09669450f` (the pin in `etc/goose.py`).

At the PR head and base the package's other test files do not all compile (the PR's head still
calls `cl.SetStore` in `server_test.go`, which its first commit removed), so the tests were run in
a scratch checkout with the other `server/etcdserver/*_test.go` files deleted. Go: `go1.24.3`
(upstream, its `go.mod`'s toolchain), `go1.27.1` (fork).

| File | What it shows | Runs against |
|---|---|---|
| `bootstrap_restart_test.go` | Three restarts of a data dir built by hand, raft started on the storage bootstrap builds (`raft.NewRawNode`, as `RestartNode` does): `TestRestartAfterSnapshotPersistedBeforeApplied` (a leader's snapshot in the WAL, its `.snap.db` not yet applied: finding 1), `TestRestartWithConsistentIndexPastWALCommit` (backend index 8, last durable `HardState.Commit` 5: finding 2), `TestRestartWithBackendWithoutConfState` (no conf state in the backend: finding 3) | PR head, PR base |
| `bootstrap_restart_helper_pr_test.go` | `bootstrapStorageForTest`: `bootstrapBackend(cfg)` + `bootstrapWALFromBackend` + `MemoryStorage()` | PR head (copy as `bootstrap_restart_helper_test.go`) |
| `bootstrap_restart_helper_base_test.go` | the same with `bootstrapBackend(cfg, true, ss)` + `bootstrapWALFromSnapshot` | PR base (copy as `bootstrap_restart_helper_test.go`) |
| `pr-head.log`, `pr-base.log` | the three tests: all fail at the PR head (raft panics `state.commit 10 is out of range [3, 3]`, `state.commit 5 is out of range [8, 10]`, `missing log entry [last: 0, append at: 4]`), all pass at the base | |
| `fork/bootstrap_restart_test.go` | the first two tests over the fork's protobuf-go v2 `raftpb`/`walpb` (no v2 `.snap` file: at this revision bootstrap reads the WAL's snapshot record) | fork PR, fork base |
| `fork/bootstrap_restart_helper_forkpr_test.go`, `fork/bootstrap_restart_helper_forkbase_test.go` | the helpers at the fork PR and fork base | fork PR, fork base |
| `fork/fork-pr.log`, `fork/fork-base.log` | both fail on the verified code (same panics), both pass on the fork base. (The third test does not apply to the fork's `bootstrap`, which overrides the conf state from the v3 store before `MemoryStorage`; the helper bypasses that.) | |
| `fork/force_new_cluster_confstate_test.go` (the reviewer's) | `--force-new-cluster` on a member of `{1,2,3}` whose backend has no conf state (the WAL's snapshot record at 3 has `{1,2,3}`): the forced restart must remove 2 and 3. Needs `fork/bootstrap_restart_test.go` (for its helpers) and a `bootstrapWALForTest` helper: `fork/force_new_cluster_helper_forkpr_test.go` / `..._forkbase_test.go` | fork PR, fork base |
| `fork/force-new-cluster-fork-pr.log`, `fork/force-new-cluster-fork-base.log` | fork PR: `added [1] removed []` (fails); fork base: `removed [2 3]` (passes) | |

Commands (upstream; `<rev>` is `pr` or `base`, `<dir>` a checkout of that revision):

```
rm <dir>/server/etcdserver/*_test.go
cp bootstrap_restart_test.go <dir>/server/etcdserver/
cp bootstrap_restart_helper_<rev>_test.go <dir>/server/etcdserver/bootstrap_restart_helper_test.go
cd <dir>/server/etcdserver && GOTOOLCHAIN=go1.24.3 go test -count=1 -run TestRestart -v .
```

Fork (`<rev>` is `forkpr` or `forkbase`; the package's own tests compile there):

```
cp fork/bootstrap_restart_test.go <dir>/server/etcdserver/
cp fork/bootstrap_restart_helper_<rev>_test.go <dir>/server/etcdserver/bootstrap_restart_helper_test.go
cd <dir>/server/etcdserver && GOTOOLCHAIN=go1.27.1 go test -count=1 \
  -run 'TestRestartAfterSnapshotPersistedBeforeApplied|TestRestartWithConsistentIndexPastWALCommit' -v .
# the force-new-cluster test, in addition to the two files above:
cp fork/force_new_cluster_confstate_test.go <dir>/server/etcdserver/
cp fork/force_new_cluster_helper_<rev>_test.go <dir>/server/etcdserver/force_new_cluster_helper_test.go
cd <dir>/server/etcdserver && GOTOOLCHAIN=go1.27.1 go test -count=1 -run TestReviewForceNewCluster -v .
```
