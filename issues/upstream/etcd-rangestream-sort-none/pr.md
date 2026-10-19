Title: v3rpc: reject RangeStream sorted by a non-key target without an order

`RangeStream` starts each chunk just after the previous chunk's last key ([`rangeStream`](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/server/etcdserver/v3_server.go#L245-L248)), so chunks must be in key order. [`checkRangeStreamRequest`](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/server/etcdserver/api/v3rpc/key.go#L173-L175) rejects other orders, assuming that [`IsDefaultOrdering`](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/server/etcdserver/txn/range.go#L97-L103) holds only for key order, but it also holds for `SortOrder: NONE` with a non-key target, which [`sortRangeResults`](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/server/etcdserver/txn/range.go#L125-L129) sorts ascending by that target. This PR makes `checkRangeStreamRequest` reject every non-key sort target.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main`, and stops two tests from streaming such a sort; the second, the fix, makes the new test pass.

Written with the assistance of generative AI; I reviewed and tested every change.
