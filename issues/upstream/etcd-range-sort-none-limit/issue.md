Title: Range sorted by a non-key target without an order returns the wrong keys when a limit is set

### What happened?

With `--sort-by` set to a target other than `KEY` and no `--order`, `etcdctl get --limit=N` does not return the first `N` results of the same `get` without a limit:

```console
$ etcdctl put c 1; etcdctl put b 2; etcdctl put a 3
$ etcdctl get a d --sort-by=CREATE --keys-only
c

b

a
$ etcdctl get a d --sort-by=CREATE --keys-only --limit=1
b
$ etcdctl get a d --sort-by=CREATE --keys-only --limit=2
c

b
```

The same happens with the other non-key sort targets, and for any client that sends `SortOrder: NONE` with one and a limit. With `--order=ASCEND` the results are right.

### What did you expect to happen?

`--limit=N` returns the first `N` results of the response without a limit: `c` for `--limit=1`, as with `--order=ASCEND`.

### How can we reproduce it (as minimally and precisely as possible)?

Run the `etcdctl` commands above against a single-member cluster built from `main` (ea8b59433).

Unit test: [`TestRangeSortLimit`](https://github.com/upamanyus/etcd/blob/etcd-range-sort-none-limit/server/etcdserver/txn/range_test.go) on branch [`upamanyus/etcd:etcd-range-sort-none-limit`](https://github.com/upamanyus/etcd/tree/etcd-range-sort-none-limit). On `main` it fails (output trimmed):

```
--- FAIL: TestRangeSortLimit (0.01s)
        	Error:      	Not equal: 
        	            	expected: []string{"c"}
        	            	actual  : []string{"b"}
        	Messages:   	limit 1
```

### Anything else we need to know?

`rpc.proto` documents `NONE` as "default, no sorting", but with a non-key target the server sorts ascending (and `etcdctl get --order`'s help says "ASCEND by default"). Should the documentation of `NONE` be changed to say so?

I found this while formally verifying etcd, working with AI tools. I reproduced the bug and reviewed this report myself.

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
