Title: etcdserver: read the whole range before sorting with SortOrder NONE

[`rangeLimit`](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/server/etcdserver/txn/range.go#L86-L95) lets mvcc stop reading after `limit + 1` keys when `IsDefaultOrdering` holds for the request's `SortOrder`, assuming the results stay in key order. With a non-key sort target and `SortOrder: NONE` they do not: [`sortRangeResults`](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/server/etcdserver/txn/range.go#L125-L129) sorts them ascending by the target, so only the first keys in key order are sorted. This PR uses the order the results are sorted in for both `rangeLimit` and `sortRangeResults`.

Fixes #22612

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
