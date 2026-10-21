Title: Txn with comparisons and no operations returns a stale result from a member that is behind

### What happened?

On a 3-member cluster:

1. A follower is cut off from the other two members.
2. A put of `foo` through the leader returns at revision 2.
3. After the put returns, the follower answers `Txn(ctx).If(Compare(Version("foo"), "=", 0)).Commit()` with `Succeeded: true` at revision 1, as if `foo` did not exist.

The same transaction with `Then(OpGet("foo"))` waits for the leader and fails at the 1s timeout. Output of both at the follower after the put (a temporary test with the setup of the test below):

```
    example_tmp_test.go:25: put: revision 2
    example_tmp_test.go:35: ops 0: succeeded true, revision 1
    example_tmp_test.go:33: ops 1: error context deadline exceeded
```

This affects any client sending a `Txn` without operations to a member that has not applied the latest writes.

### What did you expect to happen?

A `Txn` without operations should be linearizable, as the same `Txn` with a linearizable `Get` is: after the put returned, the follower should either answer with `Succeeded: false` at revision 2 or later, or fail.

### How can we reproduce it (as minimally and precisely as possible)?

Integration test: [`TestTxnCompareOnlyLinearizable`](https://github.com/upamanyus/etcd/blob/fix/etcd-txn-empty-serializable/tests/integration/clientv3/txn_test.go#L186-L208) on branch [`upamanyus/etcd:fix/etcd-txn-empty-serializable`](https://github.com/upamanyus/etcd/tree/fix/etcd-txn-empty-serializable), off `main` (7ff040cb8). On `main` it fails:

```
--- FAIL: TestTxnCompareOnlyLinearizable (0.38s)
    txn_test.go:206: 
        	Error:      	"1" is not greater than or equal to "2"
        	Messages:   	txn answered without the put (succeeded: true)
```

### Anything else we need to know?

Adding a linearizable `Get` to the transaction avoids this.

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Etcd version (please run commands below)

<details>

`main` (7ff040cb8), go1.27.1 linux/amd64; no binaries built (integration test).

</details>

### Etcd configuration (command line flags or environment variables)

<details>

The integration cluster's defaults, 3 members.

</details>
