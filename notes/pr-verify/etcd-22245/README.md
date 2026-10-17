# etcd-io/etcd#22245: tests and logs

Revisions: PR head `ab44f11fdf9bc05910e4a5045666857c32f1b9e9` (upstream base `ee043b39e`); fork branch
`mit-pdos/etcd-grove` branch `pr-etcd-22245-goose-lean` (`3aacc0e73` the PR's non-test code onto
`goose-lean` `09669450f`, `4294e7305` its mvcc unit tests).

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `keyindexput-pr-head.log` | the PR's `TestKeyIndexPut` fails: it expects revision 5's lease to be rewritten to 1 by a later put | PR head | `cd server && go test ./storage/mvcc/ -run '^TestKeyIndexPut$'` |
| `kvget-pr-head.log` | the PR's new "after update" cases of `TestKVGet` fail, full reads included (test bugs, not server bugs) | PR head | `cd tests && go test -tags integration ./common -run '^TestKVGet$'` |
| `pr-test-fixes.patch` | the minimal fix of the three test bugs: `TestKeyIndexPut`'s expectation; the update loop putting `inputs[i]`'s value and lease instead of `updates[i]`'s; `kvWithLease` mutated before it is the expectation of the read before the update | PR head | `git apply pr-test-fixes.patch` in a checkout of the PR head |
| `kv_test.go` | `tests/common/kv_test.go` of the PR head with the patch applied | PR head | copy to `tests/common/` |
| `fixed-tests-pr-head.log` | with the patch, mvcc's unit tests and `TestKVGet`, `TestKVGetStream`, `TestKVGetNoQuorum` (integration) pass | PR head + patch | `cd server && go test ./storage/mvcc/`; `cd tests && go test -tags integration ./common -run '^TestKVGet' -v` |
| `fixed-tests-base-code.log` | the patched tests fail on the base's mvcc code exactly in the `--keys-only` cases (the bug, etcd#22209), so they test the fix | PR head tests + patch, mvcc non-test files from `ee043b39e` | `git checkout ee043b39e -- server/storage/mvcc/{index,key_index,kvstore,kvstore_txn}.go`, then the integration command |

The tests of the code itself (randomized histories, restart, compaction) are etcd#22550's, which has
the same code: `notes/pr-verify/etcd-22550/` (on this branch too, cherry-picked).
