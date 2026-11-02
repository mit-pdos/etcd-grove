---
upstream: none
checked: 2026-11-01
links:
  - etcd-io/etcd#10131 issue closed: related, different (2019): watchers stopped recovering after permission-denied refusals; never diagnosed, not this teardown hang
  - etcd-io/etcd#14296 pr merged: related: the member answers a refused create with WatchId -1, the response whose handling this hang follows
blocks-proof: no
---

# clientv3: Watcher.Close can hang forever after the member refuses a watch

When the member refuses a watch's create (with auth enabled, a watch on a key the user may not read
gets `permission denied`), a `Watcher.Close` (or a `Client.Close`) issued before the client's watch
goroutine has finished tearing the refused watch down never returns, and neither does the refused
`Watch` call if it is still waiting for its channel.

**Expected:** `Close` should return, as "Close closes the watcher and cancels all watch requests"
([`Watcher.Close`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/watch.go#L97-L98));
a refused watch's channel should be closed after its cancel response.

**Impact:** clients with auth enabled that watch keys they are not permitted to read and close the
watcher or the client shortly after (a short-lived tool, a component shutting down); the window is
the time between the refusal's arrival and the client's goroutine taking the refused watch's
teardown, so the hang is intermittent. Liveness only: no wrong result. A stream ending for another
reason in the same window (a halting error, the last other watch closing) hangs the same way.

**Reproduction:** `TestWatchCloseAfterRefusedCreate` in
[`issues/etcd-watch-close-hang-refused-create/watch_close_refused_test.go`](etcd-watch-close-hang-refused-create/watch_close_refused_test.go),
copied into `client/v3` at etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28),
go1.27.3 linux/amd64. A fake `pb.WatchClient` (through the public `NewWatchFromWatchClient`) answers
the create as the member does for a denied watch
([`WatchId: -1, Created, Canceled, CancelReason`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/api/v3rpc/watch.go#L304-L310)),
and the test calls `Close` meanwhile; up to 2000 trials.

```
$ go test . -run '^TestWatchCloseAfterRefusedCreate$' -count=1
--- FAIL: TestWatchCloseAfterRefusedCreate (2.01s)
    watch_close_refused_test.go:77: trial 0: watcher.Close() hangs
FAIL
```

**Cause:** on a refused create, `addSubstream` closes the watch's receive channel and registers it
nowhere
([L466-L476](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/watch.go#L466-L476)),
and `run` drops it from `resuming`
([L607](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/watch.go#L607)).
The watch's goroutine then exits and waits to post itself on `closingc` before calling `wg.Done()`
([L797-L805](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/watch.go#L797-L805)).
If `run` stops before taking that post, its teardown receives one post per watch in `substreams`,
`resuming` and `closing` only, then waits in `w.wg.Wait()`
([L520-L540](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/watch.go#L520-L540)),
forever, since nothing receives the refused watch's post.

## Proof

no: a liveness bug; the client's watch specs are partial correctness, which a teardown that waits
forever satisfies (found reading `run`'s teardown for the reconnection's proof,
`notes/decisions.md`, D25).

## Fix

When `addSubstream` refuses a watch, `run` should add it to `closing`, as its `Canceled` case does
after closing a channel, so that the teardown waits for its post (not tried).
