# Files for the verification of etcd-io/etcd#21595

Revisions: the fork base is `09669450f` (`upamanyus/etcd` branch `goose-lean`, the etcd pin of
`etc/goose.py`); the PR applied to it is `mit-pdos/etcd-grove` branch `pr-etcd-21595-goose-lean`
(`674769349`, PR head `a376fbb3e`). Go: `GOTOOLCHAIN=go1.27.1`. Each test goes in
`server/etcdserver/` of a checkout; run from `server/`.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `base/doserialize_compacted_test.go` | With auth enabled, a read that fails with `ErrCompacted` while an auth change commits gets `ErrAuthOldRevision` from `doSerialize` (the bug the PR fixes). Fails. | `09669450f` (old `get func()`) | `cp base/doserialize_compacted_test.go <checkout>/server/etcdserver/ && go test -run TestDoSerializeCompacted -v ./etcdserver/` |
| `base-fork.log` | Its output at `09669450f`. | | |
| `pr/doserialize_compacted_test.go` | The same scenario with the PR's `get func() error`: `doSerialize` returns `ErrCompacted`. Passes. | `pr-etcd-21595-goose-lean` | as above, with `pr/` |
| `pr-fork.log` | Its output on the PR branch, with the PR's own `TestDoSerializeGetErrorPropagated` (passes). | | |
| `both/txn_readonly_metric_test.go` | A serializable read-only `Txn` denied by auth is counted as `ReadonlyTxn success="true"` (`issues/etcd-txn-readonly-auth-failure-metric.md`). Fails on both revisions: the PR does not change it. | `09669450f` and `pr-etcd-21595-goose-lean` | `cp both/txn_readonly_metric_test.go <checkout>/server/etcdserver/ && go test -run TestReadonlyTxnAuthFailure -v ./etcdserver/` |
| `txn-metric-base-fork.log`, `txn-metric-pr-fork.log` | Its output on each. | | |
