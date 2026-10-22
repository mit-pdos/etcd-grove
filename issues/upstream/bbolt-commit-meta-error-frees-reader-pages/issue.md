Title: An open read transaction sees later writes after a Commit fails once its meta page is written

### What happened?

A `Commit` that fails after its meta page reached the file lets later writes overwrite pages an open read transaction still reads:

1. A write transaction sets `k` to `v1` and commits.
2. A read transaction begins.
3. A write transaction sets `k` to `v2`; its `Commit` returns an error, raised after the meta page's write reached the file (as when the `fdatasync` after that write fails).
4. A write transaction sets `k` to `v3` and commits.
5. The read transaction of step 2 reads `k` and gets `v3`.

The test below runs these steps (output trimmed):

```
--- FAIL: TestTx_Commit_MetaWriteError_KeepsReaderSnapshot (0.00s)
        	Error:      	Not equal: 
        	            	expected: "v1"
        	            	actual  : "v3"
```

This affects any application that keeps using the database after such a `Commit` error while read transactions are open.

### What did you expect to happen?

The read transaction of step 2 should read `v1` until it is closed, whatever the `Commit` of step 3 returns.

### How can we reproduce it (as minimally and precisely as possible)?

Unit test: [`TestTx_Commit_MetaWriteError_KeepsReaderSnapshot`](https://github.com/upamanyus/bbolt/blob/fix/bbolt-commit-meta-error-frees-reader-pages/db_whitebox_test.go#L116-L156) on branch [`upamanyus/bbolt:fix/bbolt-commit-meta-error-frees-reader-pages`](https://github.com/upamanyus/bbolt/tree/fix/bbolt-commit-meta-error-frees-reader-pages), off `main` (a4ef197). It makes the meta page's write return an error after writing it; on `main` it fails as above.

### Anything else we need to know?

After step 3, new transactions also read `v2`, although that `Commit` returned an error. Is the outcome of a failed `Commit` meant to be unknown, and should its documentation say so?

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### bbolt version

<details>

`main` (a4ef197), go1.26.9 linux/amd64.

</details>

### Configuration

<details>

Default options, with `InitialMmapSize` large enough that no remap waits for the open read transaction.

</details>
