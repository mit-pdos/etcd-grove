Title: etcdserver/txn: do not apply a range's limit before sorting with SortOrder NONE

A range with a non-key sort target and `SortOrder: NONE` is sorted ascending, but `rangeLimit` checked the order as sent and kept the limit. So mvcc read only the first `limit + 1` keys in key order, and a limited response was not the start of the unlimited one. This change adds `rangeSortOrder`, which returns the order the results are actually sorted in, and uses it in both `rangeLimit` and `sortRangeResults`.

Fixes #<issue>

**Testing**

- New `TestRangeSortLimit` (`server/etcdserver/txn/range_test.go`): for every sort target and order, a range with limits 1 to 3 returns the first key-values of the same range without a limit. On `main` it fails for every non-key target with `NONE`; with this change it passes.
- `go test ./etcdserver/txn/ ./etcdserver/api/v3rpc/` (server); `go test ./integration/clientv3/ -run 'Range|Get|Sort'` and `go test -tags integration ./common/ -run 'TestKVGet$|TestKVGetStream'` (tests).
- Manually: `etcdctl get a d --sort-by=VERSION --limit=1` now returns the first key of `etcdctl get a d --sort-by=VERSION`.

**Notes for the reviewer**

- These requests now read the whole range before sorting, as the same request with `SortOrder: ASCEND` already does.
- Alternatives considered:
  - Have `etcdctl` send `ASCEND` when `--sort-by` is given without `--order`. That fixes `etcdctl` only; other clients sending `NONE` with a limit would still get the wrong keys.
  - Make `NONE` mean no sorting, as `rpc.proto` documents. That would change the behavior since #6672, which `TestV3RangeRequest` ("sort ASCEND by default") and `TestCtlV3GetTimeout` (`--sort-by=CREATE`, "ASCEND by default") test.
- `IsDefaultOrdering` is unchanged because `checkRangeStreamRequest` (`api/v3rpc/key.go`) also calls it. Changing it would make `RangeStream` reject requests it accepts today.
- Needs a backport to `release-3.6` and `release-3.5`, where the same condition (`r.SortOrder != NONE`) is in `executeRange` and `applierV3backend.Range` respectively.

This PR was written in part with the assistance of generative AI; I have reviewed and tested every change.
