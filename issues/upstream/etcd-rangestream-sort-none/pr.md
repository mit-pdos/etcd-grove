Title: v3rpc: reject RangeStream sorted by a non-key target without an order

`RangeStream` starts each chunk just after the last key of the previous chunk ([`rangeStream`](https://github.com/etcd-io/etcd/blob/b25719d10cdc41fb707b0d9f819c2529dec5d590/server/etcdserver/v3_server.go#L244-L247)), so every chunk must be in key order. [`checkRangeStreamRequest`](https://github.com/etcd-io/etcd/blob/b25719d10cdc41fb707b0d9f819c2529dec5d590/server/etcdserver/api/v3rpc/key.go#L173-L175) checks this with [`IsDefaultOrdering`](https://github.com/etcd-io/etcd/blob/b25719d10cdc41fb707b0d9f819c2529dec5d590/server/etcdserver/txn/range.go#L97-L103), which is true for `SortOrder: NONE` with any target, but a non-key target with `NONE` is sorted ascending by that target ([`sortRangeResults`](https://github.com/etcd-io/etcd/blob/b25719d10cdc41fb707b0d9f819c2529dec5d590/server/etcdserver/txn/range.go#L125-L129)). This PR makes `checkRangeStreamRequest` reject every non-key sort target, and updates the two tests that expected such a stream to be accepted.

Fixes #<issue>

`TestKVGetStreamSortByCreateRevision` runs the issue's example; it fails on `main` and passes with this change.

Written with the assistance of generative AI; I reviewed and tested every change.
