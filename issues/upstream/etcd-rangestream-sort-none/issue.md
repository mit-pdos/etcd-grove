Title: RangeStream sorted by a non-key target without an order returns duplicated and missing keys

### What happened?

With `--sort-by` set to a target other than `KEY` and no `--order`, `etcdctl get --stream` over 11 keys returns 19 keys, `a` missing and `c` to `k` twice, while the same `get` without `--stream` is right and the same `get --stream` with `--order=ASCEND` is rejected:

```console
$ for k in k j i h g f e d c b a; do etcdctl put $k 1; done
$ etcdctl get a z --sort-by=CREATE --keys-only | xargs
k j i h g f e d c b a
$ etcdctl get a z --sort-by=CREATE --keys-only --stream | xargs
k j i h g f e d c b k j i h g f e d c
$ etcdctl get a z --sort-by=CREATE --keys-only --stream --order=ASCEND | xargs
Error: rpc error: code = Unimplemented desc = RangeStream does not support custom sort orders
```

The same happens for any client calling `RangeStream` (`clientv3.KV.GetStream`) with `SortOrder: NONE` and a non-key sort target over more than 10 keys whose order by that target is not their key order.

### What did you expect to happen?

`get --stream` either returns what the same `get` without `--stream` returns, `k j i h g f e d c b a`, or rejects the request, as it does with `--order=ASCEND`.

### How can we reproduce it (as minimally and precisely as possible)?

Run the `etcdctl` commands above against a single-member cluster built from `main` (b25719d10).

Integration test: [`TestKVGetStreamSortByCreateRevision`](https://github.com/upamanyus/etcd/blob/fix/etcd-rangestream-sort-none/tests/integration/clientv3/kv_test.go) on branch [`upamanyus/etcd:fix/etcd-rangestream-sort-none`](https://github.com/upamanyus/etcd/tree/fix/etcd-rangestream-sort-none). On `main` it fails (output trimmed):

```
--- FAIL: TestKVGetStreamSortByCreateRevision (0.23s)
    --- FAIL: TestKVGetStreamSortByCreateRevision/SortNone (0.00s)
            	Error:      	Not equal: 
            	            	expected: 0xc
            	            	actual  : 0x0
            	Test:       	TestKVGetStreamSortByCreateRevision/SortNone
            	Messages:   	GetStream returned [k j i h g f e d c b k j i h g f e d c]
```

### Anything else we need to know?

Without `--stream` (the unary `Range` RPC) the same request returns the right keys.

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Etcd version (please run commands below)

<details>

```console
$ etcd --version
etcd Version: 3.8.0-alpha.0
Git SHA: b25719d10
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
