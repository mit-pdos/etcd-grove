Title: Mutex.Lock returns while another session holds the lock, after a failed TryLock on the same session

### What happened?

With `m2` and `m2b` two `Mutex` values on one session and prefix, a failed `m2b.TryLock` while `m2.Lock` waits, then `m3.Lock` (another session) and `m2b.Lock`, make `m2.Lock` return nil while `m3` holds the lock:

```go
m1.Lock(ctx)     // m1, m2, m3 on sessions s1, s2, s3; m2b on s2
go m2.Lock(ctx)  // waits for m1
m2b.TryLock(ctx)
go m3.Lock(ctx)  // waits for m1
go m2b.Lock(ctx) // waits for m3
m1.Unlock(ctx)
```

Each call's result, in order, at `main`:

```
m1.Lock: <nil>
m2b.TryLock: mutex: Locked by another session
m1.Unlock: <nil>
m3.Lock: <nil>
m2.Lock: <nil>
```

The same happens for any two `Mutex` values on one session and prefix when one deletes the session's key (`Key()`) while the other waits in `Lock` (a failed `TryLock`, or a canceled `Lock`) and a `Lock` on that session creates the key again after another session's key.

### What did you expect to happen?

`m2.Lock` does not return nil while `m3` holds the lock. If `m2b.Lock` is not called, `m2.Lock` returns `mutex: session is expired`.

### How can we reproduce it (as minimally and precisely as possible)?

Integration test: [`TestMutexLockKeyRecreated`](https://github.com/upamanyus/etcd/blob/fix/mutex-lock-recreated/tests/integration/clientv3/concurrency/mutex_test.go) on branch [`upamanyus/etcd:fix/mutex-lock-recreated`](https://github.com/upamanyus/etcd/tree/fix/mutex-lock-recreated), which runs the calls above. On `main` (b25719d10) it fails:

```
--- FAIL: TestMutexLockKeyRecreated (0.26s)
    mutex_test.go:125: 
        	Error:      	Expected error with "mutex: session is expired" in chain but got nil.
        	Test:       	TestMutexLockKeyRecreated
        	Messages:   	m2 locked while m3 holds the lock
```

### Anything else we need to know?

After `m2.Lock` returns, `m2.IsOwner()` is false, so a transaction guarded by it fails; code that relies on `Lock` returning nil is not mutually excluded.

Should `m2.Lock` return an error here, as it does when the key is gone, or keep waiting until `m3` unlocks?

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Etcd version (please run commands below)

<details>

`main` at b25719d10cdc41fb707b0d9f819c2529dec5d590, `go test` with go1.27.2 linux/amd64; no `etcd` or `etcdctl` binaries.

</details>

### Etcd configuration (command line flags or environment variables)

<details>

The integration test's single-member cluster, defaults.

</details>
