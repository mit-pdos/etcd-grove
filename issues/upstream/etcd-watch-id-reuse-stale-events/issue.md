Title: A watch created with the ID of a canceled watch receives the canceled watch's events

### What happened?

A watch created with the `WatchId` of a canceled watch on the same stream receives events of the canceled watch still queued on the server:

1. create watch `WatchId: 1` on `a`;
2. without reading the stream, put `a` ten times with a 100 KiB value;
3. cancel watch 1; create watch `WatchId: 1` on `b` from the next revision; put `b`;
4. read the stream: after the second created response, watch 1 receives events of `a`, then the event of `b`.

The same happens for any client that sets `WatchId` to the ID of a watch it canceled on the stream while that watch's events are queued.

### What did you expect to happen?

`rpc.proto` says of a canceled response: "No further events will be sent to the canceled watcher." The new watch on `b` should receive only the event of `b`.

### How can we reproduce it (as minimally and precisely as possible)?

Integration test [`TestV3WatchReuseCanceledID`](https://github.com/upamanyus/etcd/blob/fix/etcd-watch-id-reuse-stale-events/tests/integration/clientv3/watch/v3_watch_test.go) on branch [`upamanyus/etcd:fix/etcd-watch-id-reuse-stale-events`](https://github.com/upamanyus/etcd/tree/fix/etcd-watch-id-reuse-stale-events) runs these steps. On `main` (b25719d10) it failed in 10 of 10 runs:

```
--- FAIL: TestV3WatchReuseCanceledID (0.31s)
        	Error:      	Not equal: 
        	            	expected: []string{"b"}
        	            	actual  : []string{"a", "a", "a", "a", "a", "a", "a", "b"}
        	Messages:   	events received after watcher 1 was created on b
```

### Anything else we need to know?

`etcdctl` and the Go client never set `WatchId`, so they are not affected.

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Etcd version (please run commands below)

<details>

Integration test at `main` (b25719d10), go1.27.2 linux/amd64; no binaries.

</details>

### Etcd configuration (command line flags or environment variables)

<details>

Defaults, single member (the integration test framework).

</details>
