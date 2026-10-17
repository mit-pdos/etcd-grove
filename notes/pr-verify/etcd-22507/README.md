# Files for `notes/pr-verify/etcd-22507.md`

Revisions: upstream base = etcd-io/etcd `7583cc6e7e2756bb4166d646fe48d2fa1863b4b6` (the PR's
merge base with `main`); PR head = `4c832698add2865fe185362b6f977716e4b69fe9`; fork branch =
`mit-pdos/etcd-grove` branch `pr-etcd-22507-goose-lean` (`0b0ecaaab`: the fork's `goose-lean`
`09669450f` plus the PR; its tree is identical to `pr-etcd-22585-goose-lean`'s). Go toolchain
`go1.27.1`.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `leasing_test-upstream-base.log` | the PR's `TestLeasingDeleteCachedCount` fails on the base (`Count` 1, expected 0), and so do #22585's `TestLeasingDeleteCount` and `TestLeasingTxnDeleteCount` (`../etcd-22585/leasing_count_test.go`); `Error Trace` paths shortened to `<checkout>` | upstream base with the PR's `tests/integration/clientv3/lease/leasing_test.go` and `../etcd-22585/leasing_count_test.go` copied in | `git show 4c832698a:tests/integration/clientv3/lease/leasing_test.go > <base>/tests/integration/clientv3/lease/leasing_test.go && cp ../etcd-22585/leasing_count_test.go <base>/tests/integration/clientv3/lease/ && cd <base>/tests && go test ./integration/clientv3/lease/ -run 'TestLeasingDeleteCachedCount\|TestLeasing(Txn)?DeleteCount' -count=1 -v` (output filtered to the test lines) |
| `leasing_test-upstream-head.log` | all three pass with the PR | PR head with `../etcd-22585/leasing_count_test.go` copied in | as above, in the PR head |

On the fork branch, `go build ./...` and `go test ./leasing/` in `client/v3` pass.
