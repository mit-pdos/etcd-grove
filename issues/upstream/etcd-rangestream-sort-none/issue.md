Title: RangeStream sorted by a non-key target without an order returns duplicated and missing keys

### What happened?

With `--sort-by` set to a target other than `KEY` and no `--order`, `etcdctl get --stream` over 11 keys returns 19 keys, `a` missing and `c` to `k` twice, while the same `get` without `--stream` returns the 11 keys, and the same `get --stream` with `--order=ASCEND` is rejected:

```console
$ for k in k j i h g f e d c b a; do etcdctl put $k 1; done
$ etcdctl get a z --sort-by=CREATE --keys-only | xargs
k j i h g f e d c b a
$ etcdctl get a z --sort-by=CREATE --keys-only --stream | xargs
k j i h g f e d c b k j i h g f e d c
$ etcdctl get a z --sort-by=CREATE --keys-only --stream --order=ASCEND | xargs
Error: rpc error: code = Unimplemented desc = RangeStream does not support custom sort orders
```

The same happens for any client calling `RangeStream` (`GetStream` in clientv3) with a non-key sort target and `SortOrder: NONE` on a range of more than 10 keys whose order by that target is not their key order.

### What did you expect to happen?

`get --stream` should return what the same `get` without `--stream` returns, `k j i h g f e d c b a`, or reject the request, as it does with `--order=ASCEND`.

### How can we reproduce it (as minimally and precisely as possible)?

Run the `etcdctl` commands above against a single-member cluster built from `main` (22cc5d9ac).

Integration test: [`TestKVGetStreamSortByCreateRevision`](https://github.com/upamanyus/etcd/blob/fix/etcd-rangestream-sort-none/tests/integration/clientv3/kv_test.go#L432-L471) on branch [`upamanyus/etcd:fix/etcd-rangestream-sort-none`](https://github.com/upamanyus/etcd/tree/fix/etcd-rangestream-sort-none), off `main` (22cc5d9ac). On `main` it fails (output trimmed):

```
--- FAIL: TestKVGetStreamSortByCreateRevision (0.27s)
        	Error:      	Not equal: 
        	            	expected: []string{"k", "j", "i", "h", "g", "f", "e", "d", "c", "b", "a"}
        	            	actual  : []string{"k", "j", "i", "h", "g", "f", "e", "d", "c", "b", "k", "j", "i", "h", "g", "f", "e", "d", "c"}
```

### Anything else we need to know?

#22615 (a fix of #22612) fixes this too: it makes `IsDefaultOrdering` false for a non-key target with `SortOrder: NONE`, and `RangeStream` checks `IsDefaultOrdering`, so with #22615 applied to `main` (22cc5d9ac) the test above gets `Unimplemented: RangeStream does not support custom sort orders`, as with `--order=ASCEND`. #22615 also needs `TestV3RangeRequest/sort`'s expectation for `RangeStream` updated (comment on #22615). #22616, the other fix of #22612, does not fix this.

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Etcd version (please run commands below)

<details>

```console
$ etcd --version
etcd Version: 3.8.0-alpha.0
Git SHA: 22cc5d9ac
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
