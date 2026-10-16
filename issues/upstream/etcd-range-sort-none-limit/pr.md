Title: etcdserver/txn: do not apply a range's limit before sorting with SortOrder NONE

A range with a non-key sort target and `SortOrder: NONE` is sorted ascending ([`sortRangeResults`](https://github.com/etcd-io/etcd/blob/ea8b59433d82e8fc3f1365618740395e0028bd03/server/etcdserver/txn/range.go#L125-L129)), but [`rangeLimit`](https://github.com/etcd-io/etcd/blob/ea8b59433d82e8fc3f1365618740395e0028bd03/server/etcdserver/txn/range.go#L86-L95) checked the order as sent and kept the limit, so mvcc read only the first `limit + 1` keys in key order. Use the order the results are sorted in for both.

Fixes #<issue>

`TestRangeSortLimit` runs the issue's example; it fails on `main` and passes with this change.

This PR was written in part with the assistance of generative AI; I have reviewed and tested every change.
