<!-- Comment for etcd-io/etcd#22615, to post by hand. Drafted 2026-10-23 against its head 017cb18c3. -->

I'd go with this PR over mine (#22616): changing `IsDefaultOrdering` itself is the right layer, because `checkRangeStreamRequest` uses it too. On `main`, `RangeStream` accepts a non-key sort target with `SortOrder: NONE`, sorts each chunk ascending by that target, and starts the next chunk after the chunk's last key, so a stream of more than one chunk returns duplicated and missing keys. With this PR, `RangeStream` rejects those requests (`Unimplemented: RangeStream does not support custom sort orders`), as it already does with `SortOrder: ASCEND`. #22616 changes only `rangeLimit`, so it leaves `RangeStream` as it is.

I checked this at `main` (22cc5d9ac) with this PR's diff applied: [`TestKVGetStreamSortByCreateRevision`](https://github.com/upamanyus/etcd/blob/fix/etcd-rangestream-sort-none/tests/integration/clientv3/kv_test.go#L432-L471) (11 keys created in reverse key order, `GetStream` sorted by create revision with no order) fails on `main` and gets `Unimplemented` with this PR. Feel free to take it into this PR.

One more thing this PR needs: `TestV3RangeRequest/sort` in `tests/integration/v3_grpc_test.go` fails with it, because that test still expects `RangeStream` to accept its last case (`CREATE`, `NONE`):

```
v3_grpc_test.go:1566:
    Error:      Received unexpected error:
                rpc error: code = Unimplemented desc = RangeStream does not support custom sort orders
    Test:       TestV3RangeRequest/sort
```

The test's comment would become "Only ASCEND+KEY (index 0) is supported by RangeStream." and its last `streamUnsupported` entry would become `true` (`[]bool{false, true, true, true, true, true}`). `tests/common`'s `rangeStreamSupports` calls `IsDefaultOrdering`, so it needs no change: it now skips the stream variant of the two "unspecified sort order" cases. The `txn` and `v3rpc` package tests pass with this PR.

If this PR merges, I'll close #22616.

Written with the assistance of generative AI; I reviewed it.
