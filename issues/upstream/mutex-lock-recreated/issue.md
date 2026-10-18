Title: Mutex.Lock returns while another session holds the lock when a Mutex on the same session recreates the session's key

### What happened?

With `m2` and `m2b` on one session, and `m1` and `m3` on two others, all on one prefix:

1. `m1` locks.
2. `m2.Lock` starts and waits for `m1`.
3. While `m2.Lock` waits, `m2b.TryLock` fails with `mutex: Locked by another session`.
4. `m3.Lock` starts and waits for `m1`; then `m2b.Lock` starts and waits.
5. After `m1.Unlock`, `m3.Lock` returns nil, then `m2.Lock` too, while `m3` holds the lock.

The test below runs these steps (output trimmed):

```
--- FAIL: TestMutexLockKeyRecreated (0.10s)
        	Error:      	An error is expected but got nil.
        	Messages:   	m2 locked while m3 holds the lock
```

The same happens whenever another `Mutex` on the session and prefix of a waiting `Lock` deletes the session's key (a failed `TryLock` or a canceled `Lock`) and a `Lock` on that session recreates the key after another session's key.

### What did you expect to happen?

`m2.Lock` should not return nil while `m3` holds the lock.

### How can we reproduce it (as minimally and precisely as possible)?

Integration test: [`TestMutexLockKeyRecreated`](https://github.com/upamanyus/etcd/blob/fix/mutex-lock-recreated/tests/integration/clientv3/concurrency/mutex_test.go#L64-L115) on branch [`upamanyus/etcd:fix/mutex-lock-recreated`](https://github.com/upamanyus/etcd/tree/fix/mutex-lock-recreated), off `main` (22cc5d9ac). On `main` it fails as above.

### Anything else we need to know?

`m2.IsOwner()` is then false, so transactions guarded by it fail, but code relying on `Lock` alone is not mutually excluded.

Should `m2.Lock` fail here (without step 4's `m2b.Lock`, `m2.Lock` returns `mutex: session is expired`), or keep waiting until `m3` unlocks?

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Etcd version (please run commands below)

<details>

`main` (22cc5d9ac), `go test` with go1.27.2 linux/amd64; no `etcd` or `etcdctl` binaries.

</details>

### Etcd configuration (command line flags or environment variables)

<details>

The integration test's single-member cluster, defaults.

</details>
