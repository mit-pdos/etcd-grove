# Files for `notes/pr-verify/etcd-22496.md`

Revisions: upstream base = etcd-io/etcd `7583cc6e7e2756bb4166d646fe48d2fa1863b4b6` (the PR's merge
base with `main`); PR head = `bb2f0f7695cc0e048d089ab277d83e7c40ccf79c`; fork branch =
`mit-pdos/etcd-grove` branch `pr-etcd-22496-goose-lean` (`9714cb8f5`: the fork's `goose-lean`
`09669450f` plus the PR, applied without conflicts). Go toolchain `go1.27.1`.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `schedule_retention_test.go` | `TestFIFOFinishedJobCollected`: a finished FIFO job (its closure holding a 1 MiB object with a finalizer) is garbage collected while a later job is still running; and `Pending()` is 1 while that later job runs (the running job is counted) | PR head (passes), upstream base (fails), fork branch with the PR (passes), fork `goose-lean` without it (fails) | `cp schedule_retention_test.go <checkout>/pkg/schedule/ && cd <checkout>/pkg && go test -count=1 -run TestFIFOFinishedJobCollected ./schedule/` |
| `schedule_retention_test-pr-head.log` | passes with the PR | PR head | as above |
| `schedule_retention_test-upstream-base.log` | fails on the base: the finished job stays reachable through the queue's backing array | upstream base's `pkg/schedule/schedule.go` (with the PR head's other files) | as above, after `git checkout 7583cc6e7 -- pkg/schedule/schedule.go` |

Also run: `go test -race -count=3 ./schedule/` in `pkg` at the PR head with the probe (clean, by
the reviewer; `-count=1` again by the verifier), `go build ./...` in `server` and `pkg` and `go test
./etcdserver/` in `server` and `go test ./schedule/` in `pkg` on the fork branch (pass).
