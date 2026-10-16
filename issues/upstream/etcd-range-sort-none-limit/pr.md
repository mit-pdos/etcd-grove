Title: etcdserver/txn: do not apply a range's limit before sorting with SortOrder NONE

A range with a non-key sort target and `SortOrder: NONE` is sorted ascending, but `rangeLimit` checked the order as sent and kept the limit. As a result, mvcc returned only the first `limit + 1` keys in key order, and the response contained the smallest of those rather than of the whole range. This change adds `rangeSortOrder`, which returns the order the results are actually sorted in, and uses it in both `rangeLimit` and `sortRangeResults`.

Fixes #<issue>

**Testing**

- New `TestRangeSortLimit` (`server/etcdserver/txn/range_test.go`): fails on `main` for every non-key target with `NONE`, and passes with this change.
- `go test ./etcdserver/txn/ ./etcdserver/api/v3rpc/` (server); `go test ./integration/clientv3/ -run 'Range|Get|Sort'` and `go test -tags integration ./common/ -run 'TestKVGet$|TestKVGetStream'` (tests).
- Manually: `etcdctl get a d --sort-by=VERSION --limit=1` now returns the same key as with `--order=ASCEND`.

**Notes for the reviewer**

- `IsDefaultOrdering` is unchanged because `checkRangeStreamRequest` (`api/v3rpc/key.go`) also calls it. Changing it would make `RangeStream` reject requests it accepts today.
- Needs a backport to `release-3.6` and `release-3.5`, where the same condition (`r.SortOrder != NONE`) is in `executeRange` and `applierV3backend.Range` respectively.

This PR was written in part with the assistance of generative AI; I have reviewed and tested every change.
