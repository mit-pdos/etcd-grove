# Files for `notes/pr-verify/etcd-22418.md`

Revisions: upstream base = etcd-io/etcd `e041c4fa2025c78ce6c48dcb079c63b37a27285a` (the PR's merge
base with `main`); PR head = `d23dd2ba47bc93bed511495c478c72b7226842f4`; fork branch =
`mit-pdos/etcd-grove` branch `pr-etcd-22418-goose-lean` (`e47f108cf`: the fork's `goose-lean`
`09669450f` plus the PR's non-test diff; same tree, `582fff27e`, as `pr-etcd-22585-goose-lean`).
Go toolchain `go1.27.1`. The tests are the PR's own (`client/v3/leasing/util_test.go`,
`tests/integration/clientv3/lease/leasing_test.go` at the PR head), copied into the base for the
base runs; `leasing_count_test.go` is #22585's reviewer test
(`notes/pr-verify/etcd-22585/leasing_count_test.go`, on this branch too).

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `util_test-upstream-base.log` | the PR's unit test `TestLeaseCacheDeleteClearsCount` fails on the base (`Count` 1, expected 0) | upstream base with the PR's `util_test.go` | `git show d23dd2ba4:client/v3/leasing/util_test.go > <base>/client/v3/leasing/util_test.go && cd <base>/client/v3 && go test -count=1 -run TestLeaseCacheDeleteClearsCount ./leasing/` |
| `util_test-pr-head.log` | it passes with the PR | PR head | `cd <head>/client/v3 && go test -count=1 -run TestLeaseCacheDeleteClearsCount ./leasing/` |
| `leasing_test-upstream-base.log` | of the two integration tests the PR extends, `TestLeasingDeleteOwner` fails on the base (`Count` 1 after the delete); `TestLeasingDeleteNonOwner` passes on the base too (the non-owner's delete revokes lkv1's lease, which evicts the entry, so the second `Get` goes to the server) | upstream base with the PR's `leasing_test.go` | `git show d23dd2ba4:tests/integration/clientv3/lease/leasing_test.go > <base>/tests/integration/clientv3/lease/leasing_test.go && cd <base>/tests && go test -count=1 -v -run 'TestLeasingDeleteOwner$\|TestLeasingDeleteNonOwner$' ./integration/clientv3/lease/` |
| `leasing_test-pr-head.log` | both pass with the PR | PR head | `cd <head>/tests && go test -count=1 -v -run 'TestLeasingDeleteOwner$\|TestLeasingDeleteNonOwner$' ./integration/clientv3/lease/` |
| `leasing_count_test-pr-head.log` | #22585's `TestLeasingDeleteCount` and `TestLeasingTxnDeleteCount` (delete through `Delete` and through a `Txn`) pass on this PR's head (they fail on the base: `notes/pr-verify/etcd-22585/leasing_count_test-upstream-base.log`) | PR head | `cp notes/pr-verify/etcd-22585/leasing_count_test.go <head>/tests/integration/clientv3/lease/ && cd <head>/tests && go test -count=1 -v -run 'TestLeasing(Txn)?DeleteCount' ./integration/clientv3/lease/` |
