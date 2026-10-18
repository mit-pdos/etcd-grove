Title: Range through ConcurrentReadTx returns a key twice after a commit preceded by another ConcurrentReadTx

### What happened?

On a backend that commits only on `ForceCommit` (batch interval of one hour):

1. A batch transaction puts `abc` into the `Key` bucket and unlocks.
2. After that, a `ConcurrentReadTx` ranges over `[abc, \xff)` and gets `abc` once.
3. `ForceCommit` commits `abc`.
4. After the commit, with no write since, a new `ConcurrentReadTx` ranges over `[abc, \xff)` and gets `abc` twice.

The test below runs these steps (output trimmed):

```
--- FAIL: TestConcurrentReadTxAfterCommit (0.00s)
        	Error:      	Not equal: 
        	            	expected: []string{"abc"}
        	            	actual  : []string{"abc", "abc"}
        	Messages:   	after commit
```

This affects any `ConcurrentReadTx` created after a commit, periodic or forced, and before the next write, if another `ConcurrentReadTx` was created between the last write and that commit.

### What did you expect to happen?

The range after the commit should return `abc` once, as the range before the commit does.

### How can we reproduce it (as minimally and precisely as possible)?

Unit test: [`TestConcurrentReadTxAfterCommit`](https://github.com/upamanyus/etcd/blob/fix/etcd-backend-read-buffer-cache-stale-after-commit/server/storage/backend/backend_test.go#L443-L469) on branch [`upamanyus/etcd:fix/etcd-backend-read-buffer-cache-stale-after-commit`](https://github.com/upamanyus/etcd/tree/fix/etcd-backend-read-buffer-cache-stale-after-commit), off `main` (22cc5d9ac). On `main` it fails as above.

### Anything else we need to know?

Other tests (not on the branch) also read, after a commit, a key the commit deleted and a key's value from before a pre-commit hook overwrote it. I know of no wrong result through etcd's API: etcd reads through `ConcurrentReadTx` one key at a time.

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Etcd version (please run commands below)

<details>

No binaries: a unit test of `server/storage/backend` at `main` (22cc5d9ac), go1.27.2 linux/amd64.

</details>

### Etcd configuration (command line flags or environment variables)

<details>

None: the test opens a temporary backend with a batch interval of one hour and a batch limit of 10000.

</details>
