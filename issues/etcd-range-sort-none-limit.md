---
upstream: reported
checked: 2026-10-19
links:
  - etcd-io/etcd#22612 issue open: this bug, reported 2026-10-19
  - etcd-io/etcd#22616 pr open: the fix, opened 2026-10-19
  - etcd-io/etcd#22615 pr open: a fix of this bug by someone else, opened 2026-10-19 an hour before #22616: makes IsDefaultOrdering false for a non-key target with NONE, which changes its other callers too (RangeStream then rejects these requests: etcd-rangestream-sort-none)
  - etcd-io/etcd#21326 pr merged: related (the same limit/sort logic, KEY/ASCEND); not this bug
  - etcd-io/etcd#6672 pr merged: related (2016: NONE with a non-key target sorts ascending); where the bug starts
candidate: issues/upstream/etcd-range-sort-none-limit/
---

# server/etcdserver/txn: a range sorted by version, revision or value with no order and a limit returns the wrong keys

## Summary

A `Range` sorted by a target other than the key (`VERSION`, `CREATE`, `MOD` or `VALUE`) with `SortOrder: NONE` and a `Limit` returns the first `limit` key-values of a sort of the first `limit + 1` keys of the range in key order, not the first `limit` key-values of the sorted range. The server reads `NONE` with such a target as `ASCEND` when it sorts, but not when it decides whether mvcc may stop reading after `limit + 1` keys. With `SortOrder: ASCEND` the answer is right. `clientv3.WithSort(target, clientv3.SortNone)` and `etcdctl get --sort-by=VERSION --limit=1` (without `--order`) send such requests. I found this while formally verifying etcd's range execution.

## What happens

References are to `main` at f061acd0902d489041448cdd19d71a345d27b9f5.

1. `executeRange` (`server/etcdserver/txn/range.go:62`) takes mvcc's read limit from `rangeLimit` (`range.go:86-95`), which keeps the request's limit (plus one, for `More`) unless `!IsDefaultOrdering(r.SortTarget, r.SortOrder)` or a revision filter is set. `IsDefaultOrdering` (`range.go:97-103`) is true whenever `sortOrder == NONE`, whatever the target. So for `VERSION`/`NONE` with limit `n`, mvcc returns only the first `n + 1` keys of the range in key order.

   ```go
   // server/etcdserver/txn/range.go:86-103 (etcd main f061acd09)
   func rangeLimit(r *pb.RangeRequest) int64 {
   	limit := r.Limit
   	if !IsDefaultOrdering(r.SortTarget, r.SortOrder) || HasRevisionFilters(r) { // <- the raw order
   		limit = 0
   	}
   	if limit > 0 && limit < math.MaxInt64 {
   		limit = limit + 1
   	}
   	return limit
   }

   func IsDefaultOrdering(sortTarget pb.RangeRequest_SortTarget, sortOrder pb.RangeRequest_SortOrder) bool {
   	// ...
   	return sortOrder == pb.RangeRequest_NONE || // <- true for VERSION/NONE too
   		(sortTarget == pb.RangeRequest_KEY && sortOrder == pb.RangeRequest_ASCEND)
   }
   ```
2. `sortRangeResults` (`range.go:125-154`, called at `range.go:77`) turns `NONE` into `ASCEND` when the target is not the key (`range.go:126-129`) and sorts those `n + 1` key-values by the target.

   ```go
   // server/etcdserver/txn/range.go:125-131 (etcd main f061acd09)
   func sortRangeResults(rr *mvcc.RangeResult, r *pb.RangeRequest, lg *zap.Logger) {
   	sortOrder := r.SortOrder
   	if r.SortTarget != pb.RangeRequest_KEY && sortOrder == pb.RangeRequest_NONE {
   		sortOrder = pb.RangeRequest_ASCEND // <- here NONE means sort ascending
   	}

   	if !IsDefaultOrdering(r.SortTarget, sortOrder) {
   	// ... sort the (already cut) results by the target ...
   ```
3. `asembleRangeResponse` (`range.go:156-159`) keeps the first `n` of them and sets `More`.

   ```go
   // server/etcdserver/txn/range.go:156-161 (etcd main f061acd09)
   func asembleRangeResponse(rr *mvcc.RangeResult, r *pb.RangeRequest) *pb.RangeResponse {
   	resp := &pb.RangeResponse{Header: &pb.ResponseHeader{}}
   	if r.Limit > 0 && len(rr.KVs) > int(r.Limit) {
   		rr.KVs = rr.KVs[:r.Limit]
   		resp.More = true
   	}
   ```

For example, with keys `c` (version 1), `b` (version 2) and `a` (version 3), as in the reproduction below, a range over `[a, d)` with `VERSION`/`NONE` and limit 1 reads `limit + 1 = 2` keys in key order, `a` and `b`; sorted by version they are `b` (2), `a` (3); the response is `b`, with `More` true and `Count` 3. The right answer is `c`, which mvcc never read.

The response is thus the `n` smallest (by the target) of the first `n + 1` keys, which can miss the `n` smallest of the range. With an explicit `ASCEND`, `IsDefaultOrdering` is false, mvcc reads the whole range, and the answer is right; `Count` is right in both cases.

History: the limit was meant to be dropped whenever the results are sorted afterwards ("fetch everything; sort and truncate afterwards", 82eeffbd5, 2016, which tested `r.SortOrder != NONE`). 1cd6fefd4 ("etcdserver: set sort ASCEND for empty sort order", 2016) made `NONE` with a non-key target sort ascending but left that test unchanged; fd604517e (2026) moved the test into `IsDefaultOrdering`.

The client sends such requests as written: `WithSort` (`client/v3/op.go:386-397`) rewrites only `SortByKey`/`SortAscend`, and `etcdctl get` sends `SortNone` when `--sort-by` is given without `--order` (`etcdctl/ctlv3/command/get_command.go:153-185`).

## How to reproduce

The branch below adds:

- `TestRangeSortNoneLimit` (`server/etcdserver/txn/txn_test.go`, next to `setup`): keys `c`, `b` (twice), `a` (three times) are put in that order, so `c` has the lowest version, create revision, mod revision and value; a range over `[a, d)` with limit 1, for each of `VERSION`, `CREATE`, `MOD`, `VALUE` and each of `NONE`, `ASCEND`, must return `c` with `More` true and `Count` 3.
- `TestKVGetSortNoneLimit` (`tests/integration/clientv3/kv_test.go`): the same through a client, `kv.Get(ctx, "a", WithRange("d"), WithSort(SortByVersion, order), WithLimit(1))` for `SortNone` and `SortAscend`, checking the key, its version, `More` and `Count`.

```
cd server && go test ./etcdserver/txn/ -run TestRangeSortNoneLimit -v
cd tests && go test ./integration/clientv3/ -run TestKVGetSortNoneLimit -v
```

On `main` (the tests applied without the fix):

```
--- FAIL: TestRangeSortNoneLimit/VERSION/NONE   expected: "c"  actual: "b"
--- FAIL: TestRangeSortNoneLimit/CREATE/NONE    expected: "c"  actual: "b"
--- FAIL: TestRangeSortNoneLimit/MOD/NONE       expected: "c"  actual: "b"
--- FAIL: TestRangeSortNoneLimit/VALUE/NONE     expected: "c"  actual: "b"
--- FAIL: TestKVGetSortNoneLimit                expected: "c"  actual: "b"  (order 0, i.e. SortNone)
```

The `ASCEND` subtests pass on `main`. With `etcdctl`, after `etcdctl put` of `c`, `b`, `b`, `a`, `a`, `a`:

```
$ etcdctl get a d --sort-by=VERSION --limit=1 -w fields      # main: "Key" : "b", "Version" : 2, "More" : true, "Count" : 3
$ etcdctl get a d --sort-by=VERSION --order=ASCEND --limit=1 # c
```

## Expected

The same answer as with `ASCEND`, which is how the server reads `NONE` with a non-key target: the `limit` key-values of the range that come first in the target's ascending order (here `c`, version 1).

## The fix

Branch `range-sort-none-limit` (one commit, 7362d4129, with the tests; superseded by the candidate's branch `fix/etcd-range-sort-none-limit`, `issues/upstream/etcd-range-sort-none-limit/meta.md`). A new `rangeSortOrder(r)` returns the order in which the results are sorted (`r.SortOrder`, with `NONE` read as `ASCEND` for a non-key target), and both `rangeLimit` and `sortRangeResults` use it, so the limit is dropped exactly when the results are re-sorted. `IsDefaultOrdering` is unchanged: `checkRangeStreamRequest` (`server/etcdserver/api/v3rpc/key.go:169-180`) and `tests/common/kv_test.go`'s `rangeStreamSupports` also call it, and changing it would make `RangeStream` reject requests it now accepts. After the fix both tests pass, `etcdctl get a d --sort-by=VERSION --limit=1` returns `c`, and the existing tests pass unchanged (`go test ./etcdserver/txn/ ./etcdserver/api/v3rpc/`; `go test ./integration/clientv3/ -run 'Range|Get|Sort'`; `go test -tags integration ./common/ -run 'TestKVGet$|TestKVGetStream'`; `go test ./e2e/ -run TestCtlV3Get`, which covers `--sort-by`).

The commit is one commit off `main` (f061acd09), as the other fix branches are.

How the verification handles it: `notes/STATUS.md` (txn, unit 2).
