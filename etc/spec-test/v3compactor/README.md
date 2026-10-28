# v3compactor spec test

Tests the auto-compactor's specs (`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/`,
over `Proof/.../api/v3compactor/Defs.lean`) and the clock's trust boundary
(`Proof/github_com/jonboulle/clockwork/Defs.lean`) against etcd's compactor at the pinned revision:
phase 2 of `notes/spec-first-plan.md`, for the spec-first pilot (`notes/compactor-pilot-plan.md`).
`spec_test.go` is an in-package test (it drives `newPeriodic`/`newRevision` with clockwork's fake
clock); `run.sh` extracts the pinned etcd (`etc/goose.py`'s `etcd` rev, from `.lake/go-src/etcd`) to
`.lake/spec-test/`, copies the test in and runs it. Its comment says what each check transcribes;
keep them in step with the Lean files.

    etc/spec-test/v3compactor/run.sh                               # 200 runs per mode, no refutation expected
    etc/spec-test/v3compactor/run.sh -spec-runs 1000
    etc/spec-test/v3compactor/run.sh -spec-mutant rev-plus-one     # wrong permits: refuted
    etc/spec-test/v3compactor/run.sh -spec-mutant full-window,no-first
    etc/spec-test/v3compactor/run.sh -spec-seed N -spec-runs 1     # replay one run (-spec-v: events)

It prints the strength margins the specs leave out (decreasing request revisions, compactions while
paused or after `Stop`, the slack past each permit's bound). Needs `go` (the toolchain of
`etc/goose.py`'s `GO_TOOLCHAIN`, fetched if absent).
