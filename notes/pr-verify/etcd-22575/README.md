# etcd-io/etcd#22575: tests and logs

The files the report `notes/pr-verify/etcd-22575.md` relies on. Revisions: the fork pin
`09669450f` (`etc/goose.py`, branch `goose-lean` of `upamanyus/etcd`); the fork with the PR,
`mit-pdos/etcd-grove` branch `pr-etcd-22575-goose-lean` (`4fd932e97`); upstream's base
`bc12c9498` (the PR's merge base with `main`); the PR head `5aa78069a`.

| File | What it shows | Runs against | Command (from `server/`) |
|---|---|---|---|
| `v3_server_downgrade_test.go` | `TestDowngradeClusterVersionUnavailable`: with no cluster version yet, every action must return `ErrClusterVersionUnavailable` (ENABLE and CANCEL panic before the PR); `TestDowngradeCancelWithoutDowngradeReportsError`: CANCEL with no downgrade in progress must return `ErrNoInflightDowngrade` (fails: the error is only logged). The fork's layout (its `read` package runs the linearizable read loop, Masterminds semver). | `09669450f`, `4fd932e97` | `cp <file> etcdserver/ && go test -v -run TestDowngrade ./etcdserver/` |
| `upstream/v3_server_downgrade_test.go` | The same two tests in upstream's layout (the server's own read notifier, coreos go-semver). | `bc12c9498`, `5aa78069a` | the same |
| `test-base.log` | On `09669450f`: ENABLE and CANCEL panic (nil pointer dereference), VALIDATE passes; the cancel test fails. | `09669450f` | `go test -v -count=1 -run TestDowngrade ./etcdserver/` (GOTOOLCHAIN=go1.27.1) |
| `test-fork-pr.log` | On the fork with the PR: all three actions return `ErrClusterVersionUnavailable`; the cancel test still fails. | `4fd932e97` | the same |
| `upstream/test-upbase.log` | On upstream's base: the same panics as the fork's pin. | `bc12c9498` | the same |
| `upstream/test-uphead.log` | On the PR head: no panic; the cancel test still fails. | `5aa78069a` | the same |
| `review_downgrade_test.go` | The reviewer's: `TestReviewMalformedNilVersionOrdering` (a malformed target with no cluster version: VALIDATE answers the format error, ENABLE `ErrClusterVersionUnavailable`) and `TestReviewDowngradeTargetUnderflow` (at cluster version 3.0, VALIDATE accepts `3.18446744073709551615`); logs only, no assertions. Needs `v3_server_downgrade_test.go`'s helpers. | `4fd932e97` | `cp v3_server_downgrade_test.go review_downgrade_test.go etcdserver/ && go test -v -run TestReview ./etcdserver/` |
| `test-review-fork-pr.log` | Its output on the fork with the PR. | `4fd932e97` | the same |
| `version/downgrade_underflow_test.go` | `TestDowngradeValidateAtMinorZero`: `allowedDowngradeVersion(3.0)` is `3.18446744073709551615`, and `DowngradeValidate` accepts that target (`issues/etcd-downgrade-target-minor-underflow.md`). | `09669450f`, `4fd932e97`, upstream `main` `b25719d10` (not the PR head, whose base still uses coreos go-semver) | `cp <file> etcdserver/version/ && go test -v -run TestDowngradeValidateAtMinorZero ./etcdserver/version/` |
| `version/test-base.log`, `version/test-fork-pr.log`, `version/test-upmain.log` | It fails on each. | as named | the same |
