# etcd-io/etcd#22046: tests and logs

Revisions: the PR head is upstream `9314c0bd5` (`git fetch https://github.com/etcd-io/etcd pull/22046/head`);
the upstream base is `6bb7e5eea` (its merge-base with `main`); the fork branch is
`mit-pdos/etcd-grove` branch `pr-etcd-22046-goose-lean` (commit `596beb368`: the fork's `goose-lean`
`09669450f` plus the PR's non-test diff). Run each test from `server/` of a checkout, with a
disk-backed `TMPDIR` for the race test (on tmpfs the directory sync is too fast to open the window).

| File | What it shows | Against | Command |
|---|---|---|---|
| `snapshotter_release_pending_test.go` | `TestReleaseSnapDBsDeletesDBPendingApply`: the bug the PR fixes (#18055): `ReleaseSnapDBs(B)` deletes snapshot A's saved file before A is applied. Fails at the base, passes at the PR head. | base, PR head | `cp snapshotter_release_pending_test.go server/etcdserver/api/snap/ && cd server && go test -run TestReleaseSnapDBsDeletesDBPendingApply ./etcdserver/api/snap/` |
| `release-pending.log` | its output at both revisions | | |
| `snapshotter_pending_test.go` | Findings 1-3 at the PR head: `TestReleaseSnapDBsUnappliedDBIsKept` (a saved snapshot db raft never applies is never released), `TestReleaseSnapDBsReceivedAgainAfterApplyIsKept` (a db re-received after its apply is re-marked and never released, contrary to `ReleaseDBSnapshot`'s comment), `TestSaveDBFromRacesReleaseSnapDBs` (a concurrent `ReleaseSnapDBs` deletes a file `SaveDBFrom` then reports saved and marks). All three fail (the failure is the finding). | PR head | `cp snapshotter_pending_test.go server/etcdserver/api/snap/ && cd server && TMPDIR=<disk dir> go test -v -run 'TestReleaseSnapDBsUnappliedDBIsKept\|TestReleaseSnapDBsReceivedAgainAfterApplyIsKept\|TestSaveDBFromRacesReleaseSnapDBs' ./etcdserver/api/snap/` |
| `pr-head.log` | its output (with the PR's own test, which passes) | PR head | |
| `snapshotter_unapplied_base_test.go` | the first test of `snapshotter_pending_test.go` alone (compiles without the PR's API): it passes at the base, so finding 1 is a regression | base | as above, `-run TestReleaseSnapDBsUnappliedDBIsKept` |
| `base.log` | its output at the base | base | |
| `fork-tests.log` | `go test ./etcdserver/api/snap/ ./storage/ ./etcdserver/` on the fork branch with the PR's test file | fork branch | `cd server && go test ./etcdserver/api/snap/ ./storage/ ./etcdserver/` |

Toolchain: `GOTOOLCHAIN=go1.27.1`.
