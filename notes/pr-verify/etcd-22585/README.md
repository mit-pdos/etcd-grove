# Files for `notes/pr-verify/etcd-22585.md`

Revisions: upstream base = etcd-io/etcd `d3c8a155909211c6681f3075802a4aacf11528b4` (the PR's
merge base with `main`); PR head = `3097507cc2b8fc7b950e16847d6165dbe346cbba`; fork branch =
`mit-pdos/etcd-grove` branch `pr-etcd-22585-goose-lean` (`9c6eb8106`: the fork's `goose-lean`
`09669450f` plus the PR). Go toolchain `go1.27.1`.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `leasing_count_test.go` | `TestLeasingDeleteCount` (delete through `leasingKV.Delete`, then put again) and `TestLeasingTxnDeleteCount` (delete through a leasing `Txn`, `commitToCache`): after each step the leasing KV's cached `Get` (plain and `WithCountOnly`) has the same `len(Kvs)` and `Count` as a plain client's `Get` | upstream base (fails), PR head (passes), fork branch (passes) | `cp leasing_count_test.go <checkout>/tests/integration/clientv3/lease/ && cd <checkout>/tests && go test ./integration/clientv3/lease/ -run 'TestLeasing(Txn)?DeleteCount' -count=1` |
| `leasing_count_test-upstream-base.log` | both tests fail on the base: `Count` 1 where etcd says 0, after the delete and after the transaction's delete (logger lines removed) | upstream base | as above |
| `leasing_count_test-pr-head.log` | both pass with the PR | PR head | as above |
| `cache_test-upstream-base.log` | the PR's own unit test `TestLeaseCacheDeleteClearsCount` fails on the base (expected 0, actual 1); its `TestLeaseCacheDeleteDoesNotClearCountWhenRevisionOlder` passes on the base too (it guards the existing older-revision no-op) | upstream base with the PR's `client/v3/leasing/cache_test.go` | `git show 3097507cc:client/v3/leasing/cache_test.go > <base>/client/v3/leasing/cache_test.go && cd <base>/client/v3 && go test ./leasing/` |

On the fork branch, `go build ./...` and `go test ./leasing/` (with the PR's test) in `client/v3`
and `go test ./integration/clientv3/lease/ -run TestLeasing` in `tests` pass.
