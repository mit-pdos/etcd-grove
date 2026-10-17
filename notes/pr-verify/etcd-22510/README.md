# etcd-io/etcd#22510: tests and logs

The report is `../etcd-22510.md`. The proofs, and the reviewer's restart test, are #22529's
(`../etcd-22529/`, `../etcd-22529.md`): the two PRs' code is the same.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `base.log` | The PR's own test `TestApplySnapshotUpdatesAppliedIndex` (in the PR's `server/etcdserver/server_test.go`, head `3a12930b6`) **fails** without the PR's two lines: `AppliedIndex()` is 0 (expected 0x2711 = 10001), `Term()` is 0 (expected 1), and `Put` fails with `ErrTooManyRequests`. | the fork's pinned `goose-lean` (`09669450f`) with the PR's test diff applied | in a checkout of `09669450f`: `git diff 64f26db45 3a12930b6 -- server/etcdserver/server_test.go \| git apply` (`3a12930b6` fetched from etcd-io/etcd `pull/22510/head`), then `cd server && GOTOOLCHAIN=go1.27.1 go test ./etcdserver/ -run 'TestApplySnapshotUpdatesAppliedIndex$' -count=1` |
| `pr-head.log` | The same test passes with the PR; so does the whole `./etcdserver/` package. | `mit-pdos/etcd-grove` branch `pr-etcd-22510-goose-lean` (`a98134199`) with the PR's test diff applied | as above, in that branch |
