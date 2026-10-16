Title: Range with a non-key sort target, SortOrder NONE and a limit returns the wrong keys

### What happened?

A range sorted by `VERSION`, `CREATE`, `MOD` or `VALUE` with `SortOrder: NONE` and a `Limit` returns the wrong key-values. With `SortOrder: ASCEND` it returns the right ones.

```console
$ etcdctl put c v1; etcdctl put b v2; etcdctl put b v3
$ etcdctl put a v4; etcdctl put a v5; etcdctl put a v6
$ etcdctl get a d --sort-by=VERSION --limit=1
b
v3
$ etcdctl get a d --sort-by=VERSION --order=ASCEND --limit=1
c
v1
```

`c` has the lowest version (1), but the first command returns `b` (version 2).

The server sorts `NONE` with a non-key target as `ASCEND` ([`sortRangeResults`](https://github.com/etcd-io/etcd/blob/ea8b59433d82e8fc3f1365618740395e0028bd03/server/etcdserver/txn/range.go#L125-L131)). However, [`rangeLimit`](https://github.com/etcd-io/etcd/blob/ea8b59433d82e8fc3f1365618740395e0028bd03/server/etcdserver/txn/range.go#L86-L103) decides whether the results will be re-sorted from the order as sent, and [`IsDefaultOrdering`](https://github.com/etcd-io/etcd/blob/ea8b59433d82e8fc3f1365618740395e0028bd03/server/etcdserver/txn/range.go#L97-L103) treats `NONE` as unsorted. So the limit is passed to mvcc, which returns only the first `limit + 1` keys in key order (`a`, `b`). The server then sorts those two by version and truncates them to `b`. `Count` and `More` are still correct.

`etcdctl get --sort-by=X` without `--order`, and `clientv3.WithSort(target, clientv3.SortNone)`, both send this combination.

### What did you expect to happen?

The same result as with `SortOrder: ASCEND`: the first `limit` key-values of the whole range in ascending order of the target (`c` above).

### How can we reproduce it (as minimally and precisely as possible)?

Run the `etcdctl` commands above against a single-member cluster built from `main` (ea8b59433).

As a unit test (in `server/etcdserver/txn/range_test.go` on the linked branch): put the keys above, then call `Range` over `[a, d)` with `Limit: 1` for each non-key target, with both `NONE` and `ASCEND`. On `main`, every `NONE` case fails:

```
--- FAIL: TestRangeSortLimit/VERSION/NONE    expected: "c"  actual: "b"
--- FAIL: TestRangeSortLimit/CREATE/NONE     expected: "c"  actual: "b"
--- FAIL: TestRangeSortLimit/MOD/NONE        expected: "c"  actual: "b"
--- FAIL: TestRangeSortLimit/VALUE/NONE      expected: "c"  actual: "b"
```

### Anything else we need to know?

The bug has been present since `NONE` began to sort ascending for non-key targets (#6672, 2016), and it is on `release-3.6` and `release-3.5`. Both branches keep the limit when `r.SortOrder == NONE` and then sort ascending, so a fix would need a backport.

I found this while formally verifying etcd's range code.

### Etcd version (please run commands below)

<details>

```console
$ etcd --version
etcd Version: 3.8.0-alpha.0 (main, ea8b59433)

$ etcdctl version
etcdctl version: 3.8.0-alpha.0
API version: 3.8
```

</details>

### Etcd configuration (command line flags or environment variables)

<details>

Defaults, single member.

</details>
