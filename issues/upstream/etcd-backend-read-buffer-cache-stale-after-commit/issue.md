Title: After a backend commit, a range through ConcurrentReadTx returns a committed key twice

### What happened?

After a key is put through the backend's batch transaction, a range through a `ConcurrentReadTx` returns the key once; after `ForceCommit`, the same range through a new `ConcurrentReadTx` returns the key twice.

This affects any user of the backend that creates a `ConcurrentReadTx` between the end of a batch transaction with writes and the next commit (`ForceCommit` or the periodic batch commit): every `ConcurrentReadTx` created after that commit, until the next batch transaction with writes ends, reads the pre-commit read buffer.

### What did you expect to happen?

A commit does not change what a `ConcurrentReadTx` reads: the range after `ForceCommit` returns `abc` once, as before the commit.

### How can we reproduce it (as minimally and precisely as possible)?

Unit test: [`TestConcurrentReadTxAfterCommit`](https://github.com/upamanyus/etcd/blob/fix/etcd-backend-read-buffer-cache-stale-after-commit/server/storage/backend/backend_test.go) on branch [`upamanyus/etcd:fix/etcd-backend-read-buffer-cache-stale-after-commit`](https://github.com/upamanyus/etcd/tree/fix/etcd-backend-read-buffer-cache-stale-after-commit). On `main` (b25719d10) it fails (output trimmed):

```
--- FAIL: TestConcurrentReadTxAfterCommit (0.01s)
        	Error:      	Not equal: 
        	            	expected: []string{"abc"}
        	            	actual  : []string{"abc", "abc"}
        	Messages:   	after commit
```

### Anything else we need to know?

In other tests, a `ConcurrentReadTx` created after a commit also returned a key the commit deleted, and the old value of a key a pre-commit hook overwrote. `ConcurrentReadTx`'s comment says the copy of the read buffer it uses "is guaranteed to be up-to-date". I have not reproduced a wrong result through mvcc or the etcd API.

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Etcd version (please run commands below)

<details>

No binaries: a unit test of `server/storage/backend` at `main` (b25719d10cdc41fb707b0d9f819c2529dec5d590), Go go1.27.2 linux/amd64.

</details>

### Etcd configuration (command line flags or environment variables)

<details>

A backend from `betesting.NewTmpBackend` with a batch interval of one hour and a batch limit of 10000, so only `ForceCommit` commits.

</details>
