Title: A require-leader stream's context returns a non-nil Err while its Done channel is still open

### What happened?

For a stream opened with the require-leader metadata (`clientv3.WithRequireLeader`), when the member cancels the stream because it has no leader, the stream's `Context().Err()` returns the no-leader error for a short time before the context's `Done()` channel is closed. `context.Context` requires the opposite order: "If Done is not yet closed, Err returns nil."

The unit test below calls `Err()` at the moment the member is cancelling the context, before `Done()` is closed (output trimmed):

```
--- FAIL: TestCancellableContextErrBeforeDone (0.00s)
    interceptor_test.go:37: Err() = test reason before Done is closed
```

This affects any stream handler that reads the require-leader stream's `Context().Err()` while the member cancels the stream for lack of a leader.

### What did you expect to happen?

`Err()` should return nil until `Done()` is closed, and the no-leader error afterwards.

### How can we reproduce it (as minimally and precisely as possible)?

Unit test: [`TestCancellableContextErrBeforeDone`](https://github.com/upamanyus/etcd/blob/fix/etcd-stream-interceptor-err-before-done/server/etcdserver/api/v3rpc/interceptor_test.go#L24-L49) on branch [`upamanyus/etcd:fix/etcd-stream-interceptor-err-before-done`](https://github.com/upamanyus/etcd/tree/fix/etcd-stream-interceptor-err-before-done), off `main` (3aaab3479). On `main` it fails as above.

### Anything else we need to know?

etcd's own watch and lease handlers read `Err()` only after `Done()` is closed or after a stream error, where the early error can at most change how that error is logged and counted. Go's `context` package fixed the same ordering in its own contexts (golang/go#75533).

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Etcd version (please run commands below)

<details>

`main` (3aaab3479), go1.27.3 linux/amd64.

</details>

### Etcd configuration (command line flags or environment variables)

<details>

None: a unit test.

</details>
