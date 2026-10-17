# Files for `notes/pr-verify/etcd-22589.md`

Revisions: upstream base `d3c8a1559` (etcd-io/etcd `main` at the PR's merge base); PR head
`aa0116420` (etcd-io/etcd#22589); fork branch `pr-etcd-22589-goose-lean` (`d35affb63`: the fork's
`goose-lean` `09669450f` plus the PR, tests included), pushed as `mit-pdos/etcd-grove` branch
`pr-etcd-22589-goose-lean`.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `tests/integration/v3_downgrade_cancel_test.go` | `downgrade cancel` with no downgrade in progress succeeds; the server only logs `etcdserver: no inflight downgrade job` (`issues/etcd-downgrade-cancel-error-dropped.md`) | upstream base and PR head (fails at both) | `cp tests/integration/v3_downgrade_cancel_test.go <checkout>/tests/integration/ && cd <checkout>/tests && go test ./integration/ -run TestDowngradeCancelWithoutDowngradeInProgress` |
| `downgrade_cancel_swallow.log` | that test's output at the PR head (the fork branch), filtered: the server's warning, then "An error is expected but got nil" | fork branch | as above |
| `astdiff/main.go`, `astdiff/go.mod` | lists the declarations two revisions of Go files differ in (printed AST, comments ignored) | any two checkouts | `cd astdiff && go run . <old> <new> server/etcdserver/v3_server.go server/etcdserver/version/version.go` |
| `astdiff.log` | its output, upstream base vs PR head: `downgradeCancel`, `downgradeEnable`, `Manager.DowngradeValidate` changed, one import added; the same run on upstream base vs the fork pin `09669450f` (also `downgrade.go`, `cluster_util.go`, `adapters.go`) prints nothing: the fork does not rewrite this code | upstream base, PR head, fork pin | as above |
| `base-pr-tests.log` | the PR's two nil-version tests at the upstream base: `TestDowngradeValidateNilClusterVersion` panics in `allowedDowngradeVersion` (the reported bug); `TestDowngradeCancelNilClusterVersion` panics in `read.go` (`LinearizableReadNotify` of the bare test server), not at the nil cluster version | upstream base plus the PR's test files | `git show aa0116420:<test file> > <base>/<test file>`, then `go test ./etcdserver/version/ -run TestDowngradeValidateNilClusterVersion` and `go test ./etcdserver/ -run TestDowngradeCancelNilClusterVersion` in `server/` |
