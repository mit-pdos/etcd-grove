# etcd#22395: the Go tests and probes of the verification

The files are laid out as in etcd's repository. Each one is new, so copy it into a checkout of
that revision. The report is `../etcd-22395.md`. `results.log` holds the outputs below, run on
2026-10-16 with `GOTOOLCHAIN=go1.27.1`.

Revisions:
- **PR head**: `eb347e2b4`, etcd-io/etcd#22395, local branch `pr-etcd-22395` in `~/etcd`.
- **Upstream base**: `d848b43ae`, upstream `main`, the PR's merge base.
- **Fork branch**: `pr-etcd-22395-goose-lean` (`c99e5b1f9`), `goose-lean` plus the PR. It is the
  code that was verified. Its `checkIntervals` is the PR head's.

| File | What it shows | Result at PR head | Result at upstream base |
|---|---|---|---|
| `server/etcdserver/api/v3rpc/key_fromkey_test.go`: `TestCheckIntervalsFromKeyDelete` | The finding's unit test (`issues/etcd-txn-delete-then-ignore-put.md`, from fork branch `txn-delete-then-ignore-put` d9ba0e03c), as its own file. Covers a from-key delete with a put at or after its key: same level, before the delete, nested, and `Key "\x00"`. | PASS (8/8) | FAIL (6 rows: `got <nil>`) |
| same file: `TestCheckIntervalsClearAndReseed` | The behavior change: "clear and re-seed", `Then(OpDelete("", WithPrefix()), OpPut("cfg", v))`, sent as Key = RangeEnd = `"\x00"`. The test asserts the PR's rejection. | PASS (rejected, `ErrGRPCDuplicateKey`) | FAIL (`got <nil>`: accepted) |
| `server/proxy/grpcproxy/cache/store_fromkey_test.go`: `TestCacheFromKeyInvalidate` | `issues/etcd-grpcproxy-cache-from-key.md`. The proxy's range cache misreads `"\x00"`: a cached from-key range survives a put inside it, and a from-key delete leaves later cached ranges in place. | FAIL (both subtests) | FAIL (both subtests) |
| `tests/integration/clientv3/txn_fromkey_test.go`: `TestTxnDeleteFromKeyThenIgnorePut` | The finding's integration test (same fork branch), as its own file. A from-key delete followed by an `IgnoreValue`/`IgnoreLease` put of the key gets `ErrDuplicateKey` on a 1-member cluster, the key survives, and a put below the range is accepted. | PASS | not run here. The finding records the base result: the member panics, `index out of range [0] with length 0` |

Commands, with `<checkout>` an etcd checkout at the revision:

```
cp server/etcdserver/api/v3rpc/key_fromkey_test.go <checkout>/server/etcdserver/api/v3rpc/
(cd <checkout>/server && go test ./etcdserver/api/v3rpc/ -run 'TestCheckIntervalsFromKeyDelete|TestCheckIntervalsClearAndReseed' -v)

cp server/proxy/grpcproxy/cache/store_fromkey_test.go <checkout>/server/proxy/grpcproxy/cache/
(cd <checkout>/server && go test ./proxy/grpcproxy/cache/ -run TestCacheFromKeyInvalidate -v)

cp tests/integration/clientv3/txn_fromkey_test.go <checkout>/tests/integration/clientv3/
(cd <checkout>/tests && go test ./integration/clientv3/ -run TestTxnDeleteFromKeyThenIgnorePut -v)
```

`key_fromkey_test.go` uses `getError` from the package's `key_test.go`, which both revisions have.
The PR's own `TestCheckIntervalsOpenEndedDeleteRange` is in the PR's `key_test.go`. It passes at the
head, and `results.log` includes its run.

Not here: the reviewer subagent's own `checkIntervals` probes (sibling orders, WithPrefix on an
all-`0xff` key, `RangeEnd "\x00\x00"`, a delete nested two deep). The reviewer wrote them into a
scratch worktree and deleted them, and the report states their results only as the reviewer's. The
`checkIntervals` cases the report relies on are the tests above.
