Title: cache never becomes ready again after its upstream watch is retried, if etcd has moved past the cache's last event

### What happened?

After its upstream watch is canceled, the cache retries with a Get and a new watch, and becomes ready again only if that Get returns the revision of the last event the cache received. In the test below, the watch from revision 6 receives an event at revision 6 and is canceled: with the retry's Get at revision 6 the cache is ready again, with the Get at revision 7 `Ready()` stays false.

The same happens for any cache whose upstream watch fails before receiving an event, or whose retry's Get sees a write to etcd (under the cache's prefix or not) made after the last event the cache received: `Ready()` stays false, `WaitReady` never returns, and `Watch` blocks until its context ends, for as long as the new upstream watch stays open.

### What did you expect to happen?

The cache becomes ready again once the retried upstream watch is established, whatever revision the retry's Get returns.

### How can we reproduce it (as minimally and precisely as possible)?

Unit test: [`TestCacheReadyAfterWatchRetry`](https://github.com/upamanyus/etcd/blob/fix/cache-ready-after-retry/cache/cache_test.go) on branch [`upamanyus/etcd:fix/cache-ready-after-retry`](https://github.com/upamanyus/etcd/tree/fix/cache-ready-after-retry). On `main` (b25719d10) it fails (output trimmed):

```
=== RUN   TestCacheReadyAfterWatchRetry/retry_Get_at_revision_7
    cache_test.go:527: Phase 1: the watch from revision 6 receives an event at revision 6
    cache_test.go:535: Phase 2: the watch is canceled and retried after a Get at revision 7
getWatch failed, will retry after 50ms: rpc error: code = FailedPrecondition desc = canceled
    cache_test.go:541: cache not ready after the retried watch
--- FAIL: TestCacheReadyAfterWatchRetry (0.00s)
    --- PASS: TestCacheReadyAfterWatchRetry/retry_Get_at_revision_6 (0.00s)
    --- FAIL: TestCacheReadyAfterWatchRetry/retry_Get_at_revision_7 (0.00s)
```

### Anything else we need to know?

I found this while formally verifying etcd, working with AI tools. I reproduced the bug and reviewed this report myself.

### Etcd version (please run commands below)

<details>

`main` (b25719d10), `go.etcd.io/etcd/cache/v3`, go1.27.2 linux/amd64. No etcd binaries: the test uses a fake watcher and KV.

</details>

### Etcd configuration (command line flags or environment variables)

<details>

Default cache configuration (`cache.New(client, "")`).

</details>
