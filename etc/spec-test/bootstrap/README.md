# bootstrap spec test

Tests `bootstrap`'s trusted contracts against etcd's `bootstrap` at the pinned revision (the
whole-`bootOk` review, 2026-11-03): `bootOk`/`bootstrapContract`
(`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvBoot.lean`) on a fresh data directory, and
`srvDiskImage`, `bootOkR`/`bootstrapRestartContract` (`.../etcdserver/InvRestart.lean`) on a member's
directory after a graceful stop, each with and without a compaction and with and without auth
enabled, at the examples' configuration (`examples/common/common.go`). `spec_test.go` is an
in-package test (it calls the unexported `bootstrap` and reads private fields by reflection);
`run.sh` extracts the pinned etcd (`etc/goose.py`'s `etcd` rev) to `.lake/spec-test/`, copies the
test in and runs it.

    etc/spec-test/bootstrap/run.sh                     # from .lake/go-src/etcd
    ETCD_SRC=../etcd etc/spec-test/bootstrap/run.sh    # from another checkout of the fork
    SPEC_TABLE=.lake/logs/bootok.txt etc/spec-test/bootstrap/run.sh

Each check is named by the Lean conjunct it transcribes; keep them in step. The checks the review
found false of Go are listed in `knownFalse` (with the finding's name): the test fails if one of
them holds, or if any other check fails, so a repair of the Lean statement goes with moving its
check out of the list (2026-11-03: the review's A, T1-B, C and G repaired; left, a restart's image in
auth mode, H). The table of every check in every run is in the test's log. Needs `go` (the
toolchain of `etc/goose.py`'s `GO_TOOLCHAIN`, fetched if absent). The test's data directories go
under `.lake/spec-test/tmp` (`TMPDIR_SPEC` to change it): each WAL preallocates 64 MiB.
