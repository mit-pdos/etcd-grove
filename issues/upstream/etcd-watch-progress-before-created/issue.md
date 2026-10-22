Title: A watch created after a progress request can receive the progress response before its earlier events

### What happened?

On one watch stream, while the member still has responses queued for the stream:

1. The client puts `b` (revision 2), creates a watch on `a`, and puts `a` ten times with a 100 KiB value, without reading the stream.
2. The client sends a progress request, then creates a watch on `b` from revision 2.
3. The client reads the stream: the progress response (revision 12) comes after the created response of the watch on `b`, before that watch's event at revision 2.

The test below runs these steps (output trimmed):

```
--- FAIL: TestV3WatchProgressBeforeCreated (0.23s)
        	Error:      	Should be false
        	Messages:   	progress response at revision 12 after the created response of the watcher on b, before its event at revision 2
```

The Go client passes such a progress response to every watch it has created, so the watch on `b` is notified of progress at revision 12 before its event at revision 2. The Go client, which reads the stream at once, hits this too, less often.

### What did you expect to happen?

The progress response should come before the created response of the watch on `b`: it answers a request sent before that watch was created.

### How can we reproduce it (as minimally and precisely as possible)?

Integration test: [`TestV3WatchProgressBeforeCreated`](https://github.com/upamanyus/etcd/blob/fix/etcd-watch-progress-before-created/tests/integration/clientv3/watch/v3_watch_test.go#L1536-L1597) on branch [`upamanyus/etcd:fix/etcd-watch-progress-before-created`](https://github.com/upamanyus/etcd/tree/fix/etcd-watch-progress-before-created), off `main` (bf9cadf04). On `main` it fails as above, in 20 of 20 runs.

### Anything else we need to know?

`rpc.proto` says that after a progress response "all future events received in this stream" have a higher revision, which a watch created later from an earlier revision cannot satisfy. Should it say this of the watches created before the progress request?

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Etcd version (please run commands below)

<details>

Integration test at `main` (bf9cadf04), go1.27.3 linux/amd64; no binaries.

</details>

### Etcd configuration (command line flags or environment variables)

<details>

Defaults, single member (the integration test framework).

</details>
