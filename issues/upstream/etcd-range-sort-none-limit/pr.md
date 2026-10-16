Title: etcdserver/txn: do not apply a range's limit before sorting with SortOrder NONE

A range with a non-key sort target and `SortOrder: NONE` is sorted ascending ([`sortRangeResults`](https://github.com/etcd-io/etcd/blob/ea8b59433d82e8fc3f1365618740395e0028bd03/server/etcdserver/txn/range.go#L125-L129)), but [`rangeLimit`](https://github.com/etcd-io/etcd/blob/ea8b59433d82e8fc3f1365618740395e0028bd03/server/etcdserver/txn/range.go#L86-L95) checked the order as sent and kept the limit. So mvcc read only the first `limit + 1` keys in key order, and a limited response was not the start of the unlimited one. This change adds `rangeSortOrder`, which returns the order the results are actually sorted in, and uses it in both `rangeLimit` and `sortRangeResults`.

Fixes #<issue>

**Testing**

- New `TestRangeSortLimit` (`server/etcdserver/txn/range_test.go`) runs the issue's example (`SortTarget: CREATE`, `SortOrder: NONE`, limits 0, 1 and 2). On `main` it fails at limit 1; with this change it passes.
- `go test ./etcdserver/txn/ ./etcdserver/api/v3rpc/` (server); `go test ./integration/clientv3/ -run 'Range|Get|Sort'` and `go test -tags integration ./common/ -run 'TestKVGet$|TestKVGetStream'` (tests).
- Manually: with the keys from the issue, `etcdctl get a d --sort-by=CREATE --keys-only --limit=1` now prints `c`, the first key of the same `get` without `--limit`.

**Notes for the reviewer**

- These requests now read the whole range before sorting, as the same request with `SortOrder: ASCEND` already does.
- Alternatives considered:
  - Have `etcdctl` send `ASCEND` when `--sort-by` is given without `--order`. That fixes `etcdctl` only; other clients sending `NONE` with a limit would still get the wrong keys.
  - Make `NONE` mean no sorting, as `rpc.proto` documents. That would undo #6672, which made a non-key target with no order sort ascending; `TestV3RangeRequest` ("sort ASCEND by default") and `TestCtlV3GetTimeout` (`--sort-by=CREATE`) test that behavior.
- `IsDefaultOrdering` is unchanged, so [`checkRangeStreamRequest`](https://github.com/etcd-io/etcd/blob/ea8b59433d82e8fc3f1365618740395e0028bd03/server/etcdserver/api/v3rpc/key.go#L169-L180) still accepts a non-key target with `NONE`; with this change, each `RangeStream` chunk of such a request reads the rest of the range. Such a stream is still wrong once it needs a second chunk (the next chunk starts after the last key of a chunk sorted by the target), before and after this change; that is a separate bug.
- Needs a backport to `release-3.6` and `release-3.5`, where the same condition (`r.SortOrder != NONE`) is in `executeRange` and `applierV3backend.Range` respectively.

This PR was written in part with the assistance of generative AI; I have reviewed and tested every change.
