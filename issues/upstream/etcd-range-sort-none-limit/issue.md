Title: Range sorted by a non-key target without an order returns the wrong keys when a limit is set

### What happened?

With `--sort-by` set to a target other than `KEY` and no `--order`, `etcdctl get --limit=N` does not return the first `N` results of the same `get` without a limit:

```console
$ etcdctl put c v1; etcdctl put b v2; etcdctl put b v3
$ etcdctl put a v4; etcdctl put a v5; etcdctl put a v6
$ etcdctl get a d --sort-by=VERSION --keys-only
c

b

a
$ etcdctl get a d --sort-by=VERSION --keys-only --limit=1
b
$ etcdctl get a d --sort-by=VERSION --keys-only --limit=2
c

b
```

The same happens with `CREATE`, `MODIFY` and `VALUE`, and for any client that sends `SortOrder: NONE` with a non-key target and a `Limit` (`clientv3.WithSort(target, clientv3.SortNone)` with `clientv3.WithLimit`). With `--order=ASCEND` the limited results are right.

For `NONE` with a non-key target, the server sorts ascending ([`sortRangeResults`](https://github.com/etcd-io/etcd/blob/ea8b59433d82e8fc3f1365618740395e0028bd03/server/etcdserver/txn/range.go#L125-L131), since #6672). But [`rangeLimit`](https://github.com/etcd-io/etcd/blob/ea8b59433d82e8fc3f1365618740395e0028bd03/server/etcdserver/txn/range.go#L86-L103) decides whether the results will be re-sorted from the order as sent, and [`IsDefaultOrdering`](https://github.com/etcd-io/etcd/blob/ea8b59433d82e8fc3f1365618740395e0028bd03/server/etcdserver/txn/range.go#L97-L103) treats `NONE` as unsorted. So the limit is passed to mvcc, which reads only the first `limit + 1` keys in key order (`a`, `b` for `--limit=1`). The server then sorts those by version and truncates them to `b`. `Count` and `More` are still correct.

### What did you expect to happen?

`--limit=N` returns the first `N` results of the response without a limit: `c` for `--limit=1`, as with `--order=ASCEND`.

### How can we reproduce it (as minimally and precisely as possible)?

Run the `etcdctl` commands above against a single-member cluster built from `main` (ea8b59433).

As a unit test (`TestRangeSortLimit` in `server/etcdserver/txn/range_test.go` on the linked branch): put the keys above; for each sort target and order, compare `Range` over `[a, d)` with limits 1 to 3 against the same `Range` without a limit. On `main`, the `NONE` cases with a non-key target fail at limit 1 (output trimmed):

```
    --- FAIL: TestRangeSortLimit/VERSION/NONE (0.00s)
            	Error:      	Not equal: 
            	            	expected: []string{"c"}
            	            	actual  : []string{"b"}
            	Messages:   	limit 1
    --- FAIL: TestRangeSortLimit/CREATE/NONE (0.00s)
    --- FAIL: TestRangeSortLimit/MOD/NONE (0.00s)
    --- FAIL: TestRangeSortLimit/VALUE/NONE (0.00s)
```

### Anything else we need to know?

The bug has been present since `NONE` began to sort ascending for non-key targets (#6672, 2016), and it is on `release-3.6` and `release-3.5`. Both branches keep the limit when `r.SortOrder == NONE` and then sort ascending, so a fix would need a backport.

`rpc.proto` still documents `NONE` as "default, no sorting". The limited response matches neither that nor the ascending order the server uses without a limit.

I found this while formally verifying etcd's range code.

### Etcd version (please run commands below)

<details>

```console
$ etcd --version
etcd Version: 3.8.0-alpha.0
Git SHA: ea8b59433
Go Version: go1.27.2
Go OS/Arch: linux/amd64

$ etcdctl version
etcdctl version: 3.8.0-alpha.0
API version: 3.8
```

</details>

### Etcd configuration (command line flags or environment variables)

<details>

Defaults, single member.

</details>
