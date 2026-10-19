Title: cache never becomes ready again after a compaction cancels its upstream watch

### What happened?

1. The cache's Get returns revision 5, and its watch from revision 6 is created. The cache is ready.
2. A compaction at revision 10 then cancels that watch. The cache becomes not ready and retries.
3. After the retry's back-off, the cache's Get returns revision 10, and its new watch from revision 11 is created.
4. From then on the cache stays not ready: `Ready()` returns false, `WaitReady` does not return, and `Watch` blocks until its context ends.

The test below runs these steps (output trimmed):

```
=== RUN   TestCacheReadyAfterCompactionResync
getWatch failed, will retry after 50ms: etcdserver: mvcc: required revision has been compacted
    cache_test.go:541: cache not ready after the resync
--- FAIL: TestCacheReadyAfterCompactionResync (0.00s)
```

This affects any cache whose upstream watch fails, unless the cache had received an event before the failure and the retry's Get returns the revision of the last such event.

### What did you expect to happen?

The cache should become ready again once its new watch from revision 11 is created, as it did when its first watch was created.

### How can we reproduce it (as minimally and precisely as possible)?

Unit test: [`TestCacheReadyAfterCompactionResync`](https://github.com/upamanyus/etcd/blob/fix/cache-ready-after-retry/cache/cache_test.go#L509-L544) on branch [`upamanyus/etcd:fix/cache-ready-after-retry`](https://github.com/upamanyus/etcd/tree/fix/cache-ready-after-retry), off `main` (22cc5d9ac). On `main` it fails as above.

### Anything else we need to know?

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Etcd version (please run commands below)

<details>

`main` (22cc5d9ac), `go.etcd.io/etcd/cache/v3`, go1.27.2 linux/amd64. No etcd binaries: the test uses the package's fake watcher and KV.

</details>

### Etcd configuration (command line flags or environment variables)

<details>

Default cache configuration (`cache.New(client, "")`).

</details>
