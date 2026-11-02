---
upstream: known
checked: 2026-11-01
links:
  - etcd-io/etcd#22615 pr open: would fix this bug without saying so (a fix of #22612 that makes IsDefaultOrdering false for a non-key target with NONE, so RangeStream rejects these requests; checked 2026-10-23); no issue filed for this bug
  - etcd-io/etcd#21631 pr merged: related, not this bug (the RangeStream server, whose IsDefaultOrdering check is the defect)
  - etcd-io/etcd@9acc0ebe3: related, not this bug (clones the chunk's last key before appending \x00 in rangeStream)
blocks-proof: no
---

# etcdserver: RangeStream sorted by a non-key target without an order returns duplicated and missing keys

With a sort target other than the key and no sort order, `etcdctl get --stream` (`GetStream` in
clientv3) over a range of more than 10 keys whose order by that target is not their key order
returns some keys twice and misses others: over 11 keys created in reverse key order,
`etcdctl get a z --sort-by=CREATE --keys-only --stream` returns 19 keys, `a` missing and `c` to `k`
twice, while the same `get` without `--stream` returns the 11 keys and `--order=ASCEND` is rejected
as unsupported.

**Expected:** `GetStream` should return what `Get` returns, or reject the request, as it rejects
`--order=ASCEND` ("RangeStream does not support custom sort orders").

**Impact:** wrong results for clients that stream a range sorted by a non-key target without an
order; v3.7 (RangeStream is new in 3.7). The stream also advances only about two keys per chunk in
such a range, so it sends far more than the range (267 MB for a 2 MB range, measured 2026-10-18).

**Reproduction:** `TestKVGetStreamSortByCreateRevision` in
[`issues/etcd-rangestream-sort-none/kv_get_stream_sort_test.go`](etcd-rangestream-sort-none/kv_get_stream_sort_test.go),
copied (as `zz_kv_get_stream_sort_test.go`) into `tests/integration/clientv3` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28), go1.27.3:

```
$ (cd tests && go test ./integration/clientv3 -run '^TestKVGetStreamSortByCreateRevision$' -count=1)
--- FAIL: TestKVGetStreamSortByCreateRevision (0.22s)
        	Error:      	Not equal:
        	            	expected: []string{"k", "j", "i", "h", "g", "f", "e", "d", "c", "b", "a"}
        	            	actual  : []string{"k", "j", "i", "h", "g", "f", "e", "d", "c", "b", "k", "j", "i", "h", "g", "f", "e", "d", "c"}
FAIL
```

**Cause:** `RangeStream` starts each chunk just after the previous chunk's last key
([v3_server.go#L247](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/v3_server.go#L247)),
so chunks must be in key order. `checkRangeStreamRequest` rejects other orders with
`IsDefaultOrdering`
([key.go#L173](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/api/v3rpc/key.go#L173)),
which holds for `SortOrder: NONE` with any target
([range.go#L97-L103](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/txn/range.go#L97-L103)),
while `sortRangeResults` sorts `NONE` with a non-key target ascending by that target
([range.go#L125-L129](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/txn/range.go#L125-L129)).

## Proof

no: `RangeStream` is not in the verified code.

## Fix

**Branch**: `fix/etcd-rangestream-sort-none` in `~/etcd-fixes/etcd-rangestream-sort-none` (upamanyus/etcd, pushed): a8c642742 test, 638081c75 fix
**Base**: etcd-io/etcd@22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4

**PR draft**:

Title: v3rpc: reject RangeStream sorted by a non-key target without an order

`RangeStream` starts each chunk just after the previous chunk's last key ([`rangeStream`](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/server/etcdserver/v3_server.go#L245-L248)), so chunks must be in key order. [`checkRangeStreamRequest`](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/server/etcdserver/api/v3rpc/key.go#L173-L175) rejects other orders, assuming that [`IsDefaultOrdering`](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/server/etcdserver/txn/range.go#L97-L103) holds only for key order, but it also holds for `SortOrder: NONE` with a non-key target, which [`sortRangeResults`](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/server/etcdserver/txn/range.go#L125-L129) sorts ascending by that target. This PR makes `checkRangeStreamRequest` reject every non-key sort target.

The first commit adds a test of the issue's example, which fails on `main`, and stops two tests from streaming such a sort; the second, the fix, makes the new test pass.

## Notes

The plan (2026-10-23, and the user's in the 2026-10-23 review): file this as an issue linked to #22615,
saying #22615 fixes it; open this branch's PR only if #22616 merges instead of #22615.
