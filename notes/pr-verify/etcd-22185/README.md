# Files of the verification of etcd-io/etcd#22185

Report: `notes/pr-verify/etcd-22185.md`. Revisions: the PR head `aad3f3a2b` (upstream base
`cb846f6d2`); the verified fork `goose-lean` `09669450f` (the "base" below) and, with the PR
applied, `mit-pdos/etcd-grove` branch `pr-etcd-22185-goose-lean` (`757233c4a`). Go 1.27.1
(`GOTOOLCHAIN=go1.27.1`). Each test is a file of package `mvcc`: copy it into
`server/storage/mvcc/` of a checkout and run the command from `server/`.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `watchable_store_progress_deadlock_test.go` | The PR's regression test `TestProgressIfSyncDeadlock` (as a file of its own): the three-way cycle write txn / `Commit` / `progressIfSync`. Fails (3 s deadline) before the fix, passes after. | base `09669450f` (fails), PR head / fork branch (passes; the PR head and the fork branch already carry it in `watchable_store_test.go`, so copy it only onto the base) | `go test ./storage/mvcc/ -run TestProgressIfSyncDeadlock -count=1` |
| `deadlock-test-base.log` | Its failure on the base. | base `09669450f` | as above |
| `deadlock-test-pr-head.log` | The PR's own copy passing at the PR head. | upstream PR head `aad3f3a2b` | `go test ./storage/mvcc/ -run TestProgressIfSyncDeadlock -count=1 -v` |
| `watchable_store_progress_stress_test.go` | The reviewer's probe `TestReviewProgressIfSyncStress`: two writers, a `Commit` loop and `RequestProgress` on one watch for 3 s; checks progress revisions never fall below delivered events, events after a progress response are above it, and the workers stop (no deadlock); under `-race`, no data race. | base (deadlocks), PR head and fork branch (pass, `-race`) | `go test -race ./storage/mvcc/ -run TestReviewProgressIfSyncStress -count=1 -v` (on the base add `-timeout 60s`) |
| `stress-test-pr-head.log` | It passing at the PR head under `-race`. | upstream PR head `aad3f3a2b` | as above |
| `stress-test-base.log` | It deadlocking on the base ("workers did not stop", then the test timeout). | base `09669450f` | as above, without `-race`, `-timeout 60s` |
