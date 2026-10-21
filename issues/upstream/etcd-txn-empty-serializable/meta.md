# etcd-txn-empty-serializable

- **Finding**: `issues/etcd-txn-empty-serializable.md`
- **Target**: etcd-io/etcd, `main`
- **Branch**: `fix/etcd-txn-empty-serializable` in `~/etcd-fixes/etcd-txn-empty-serializable`, two commits
  (2026-10-21): 1fb35aaba adds the test, which fails there; 8cf21d8e9 is the fix. Not pushed; the issue's test link
  (`#L186-L208`, doc comment to closing brace) to be checked on GitHub after the push.
- **Base**: upstream `main` 7ff040cb84c9944d0c38a9f0dc9f12ed9c58223b (2026-10-21; `IsTxnSerializable` unchanged since
  fab3c8e70, 2016, which made it vacuously true)
- **State**: draft

Commit messages (drafts for the user to rewrite):

- `tests: test a compare-only txn at a partitioned member` (no body)
- `etcdserver: serve a txn without operations linearizably`, body: "A txn with no operations asks for no
  serializable read, so take the read index for it."

Push: `git -C ~/etcd-fixes/etcd-txn-empty-serializable push origin fix/etcd-txn-empty-serializable`

## Duplicates checked (2026-10-21)

Searches (issues and PRs separately): `IsTxnSerializable`, `txn serializable compare stale`, `txn empty
linearizable`, `txn without operations`. No duplicate. Looked at and different: #20418 (stale reads from a paused
process, robustness), #18803 (read-only txn failures at apply), #18424 (client retry and `Serializable`).

## Why the fix works

At the base, `(*EtcdServer).Txn` finds the compare-only txn read-only (`IsTxnReadonly`: no op is a write) and
serializable (`IsTxnSerializable`: no op is a non-serializable range, vacuously), so it skips
`LinearizableReadNotify` and runs the txn on the follower's store, which has not applied the put: `Version(foo) = 0`
holds, revision 1. With the fix, `IsTxnSerializable` is false for no ops, so the follower requests the read index;
cut off from the leader, it cannot get one, and the txn fails with the client's deadline (after the partition heals
it would answer with the put applied). A txn with at least one op is classified as before.

The test is the issue's example: a follower partitioned by the integration harness's `InjectPartition` (the
package's usual way to make a member fall behind), one put through the leader, acknowledged, then one ordinary
client txn at the follower. Nothing is misused: the client asks for no serializable read (`clientv3.Txn` has no way
to), and `rpc.proto` says ranges are linearizable unless `serializable` is set. The test accepts either an error or a
reply that includes the put (revision at least the put's), the guarantee; at the fix it takes the error path (1s).

## If a reviewer asks

Candidate layers and fixes:

1. **The helper (chosen)**: `IsTxnSerializable` false when both lists are empty. Its informal spec (its name, and its
   use: "the txn may be served without the read index") is "the client asked for a serializable read"; a txn with no
   ranges asked for nothing, so the helper's answer is wrong, not the caller's use of it. It has one caller
   (`(*EtcdServer).Txn`, `server/etcdserver/v3_server.go`), inside `if readOnly`, which wants exactly the corrected
   answer; no test, tool or other module calls it (grep over the repository). One change, no exported signature
   change, the same shape as #22615's `IsDefaultOrdering` fix.
2. **The caller**: `if !txn.IsTxnSerializable(r) || (len(r.Success) == 0 && len(r.Failure) == 0)` in `Txn`. Same
   behavior today, but leaves the helper answering "serializable" for a request that never asked, for the next
   caller; a workaround of the kind the #22612 review preferred against.
3. **`IsTxnReadonly`**: also vacuously true for no ops, but correctly so (no writes), and its two callers
   (`(*EtcdServer).Txn`'s read path, `txn.Txn`'s read mode) want that; routing an empty txn through raft instead would
   be slower than the read index for no gain.
4. **Stricter rule** (serializable only if both branches are non-empty, so the verdict always comes from a branch
   the client marked): changes txns that do ask for serializable ranges in one branch; not this bug; not proposed.
5. **API**: a `serializable` field on `TxnRequest` (so compare-only txns can opt in): a feature, out of scope.

Cost: a compare-only or empty txn now waits for the read index, like every other linearizable read; clients that
want the old local answer can add a serializable `Get`.

## Verification (go1.27.1 linux/amd64)

- At the tests commit 1fb35aaba (`cd tests && go test ./integration/clientv3/ -run TestTxnCompareOnlyLinearizable
  -count=1`): fails, `"1" is not greater than or equal to "2"`, `txn answered without the put (succeeded: true)`.
- The issue's example (a temporary test, not committed, same setup; at the base): put revision 2; the compare-only
  txn `succeeded true, revision 1`; with `Then(OpGet("foo"))`, `context deadline exceeded`.
- At the fix commit 8cf21d8e9: the test passes (1.31s); `cd tests && go test ./integration/clientv3/
  ./integration/clientv3/concurrency/` ok; `go test ./integration/ -run TestV3Txn` ok; `cd server && go test
  ./etcdserver/...` ok; `gofmt -l` empty; `go vet ./etcdserver/txn/ ./etcdserver/` and `go vet
  ./integration/clientv3/` clean.

Not run: `tests/e2e`, robustness, `make verify` (golangci-lint).

## Review (2026-10-21)

By hand: every caller of `IsTxnSerializable` (one) and `IsTxnReadonly` (two) read; no comment or doc claims the old
behavior (the helper has no doc comment; `rpc.proto` says nothing about txn serializability). Learners reject `Txn`
regardless (`isRPCSupportedForLearner`). The gRPC proxy forwards `Txn` as is. No non-test code in the repository sends
an empty txn. No new bug found.
