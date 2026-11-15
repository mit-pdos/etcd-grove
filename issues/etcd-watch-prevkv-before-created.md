---
upstream: none
checked: 2026-11-09
links:
  - kubernetes/kubernetes#121285 issue closed: possibly this bug: "etcd event received with PrevKv=nil" right after creating a Deployment, never diagnosed
  - kubernetes/kubernetes#100112 issue closed: possibly this bug: a flaky watch test with the same error
  - etcd-io/etcd#6120 issue closed: related, different (2016): PrevKv nil because the client did not ask for it
blocks-proof: no
---

# watch: a PrevKv watch's first events can arrive without PrevKv when the key is written while the watch is created

A watch created with `PrevKv` on a key that is being written concurrently can receive its first
update events with `PrevKv` unset, although the previous key-value exists and is not compacted.
Kubernetes' API server fails such a watch ("etcd event received with PrevKv=nil", `k8s.io/apiserver/pkg/storage/etcd3/event.go:65`).

**Expected:** every event of a `PrevKv` watch should carry the previous key-value unless the event
creates the key or that revision is compacted, as `WatchCreateRequest.prev_kv` documents ("If
prev_kv is set, created watcher gets the previous KV before the event happens. If the previous KV
is already compacted, nothing will be returned").

**Impact:** any client creating `PrevKv` watches on keys under writes (Kubernetes' etcd3 watcher
uses `WithPrevKV` for every watch); intermittent, the window is the time between the member
registering the watcher and recording its options. The client sees an update or delete with no
previous value; Kubernetes ends the watch with an internal error and the watch is re-established.
Default configuration, any cluster size.

**Reproduction:** `TestV3WatchPrevKVBeforeCreated` in
[`issues/etcd-watch-prevkv-before-created/watch_prevkv_before_created_test.go`](etcd-watch-prevkv-before-created/watch_prevkv_before_created_test.go),
run at the verified fork's pin (`upamanyus/etcd` `a4d2bb17`, the code of `watch.go` around the race
is upstream `main`'s) through this repository's `examples` module (its `go.mod` replaces etcd by the
pin; the test in a package of `examples/` with `package` renamed, `go mod tidy` in a scratch copy),
go1.27.3 linux/amd64; to be rerun in `tests/integration/clientv3/watch` at upstream `main` before
filing. Sixteen raw watch streams each create 1500 `PrevKv` watches on `k` while eight goroutines
put `k`:

```
$ GOMAXPROCS=2 go test ./specreq/v3rpcwatch/ -run TestV3WatchPrevKVBeforeCreated -count=1
--- FAIL: TestV3WatchPrevKVBeforeCreated (8.29s)
    zz_prevkv_race_test.go:86: iteration 32: event at revision 246 (version 245) of a PrevKv watch without PrevKv
FAIL
```

(It also failed at `GOMAXPROCS=4`; it passed at `GOMAXPROCS=1` and with one stream.)

**Cause:** `recvLoop` records a new watch's `PrevKv` option (`sws.prevKV[id] = true`) only after
mvcc's `Watch` has returned (`server/etcdserver/api/v3rpc/watch.go`, `recvLoop`, the create case),
but mvcc may queue a response for the new watcher as soon as it is registered (a concurrent write's
notification, or the unsynced watchers' sync). `sendLoop`'s `sendWatch` reads `prevKV[id]` before it
checks whether the id was announced, builds the events without `PrevKv`, buffers them as pending,
and sends them unchanged after the `Created` response.

## Proof

no: the specs-only branch's watch contract (1b's `wireStep`, 2b's `sendLoop`) admits a missing
`PrevKv` on a watch's first responses (a weakened `WatchReq.prevOk` for the window before the
`Created` response); with the fix below in the fork it could be the strong one again.

## Fix

Not written. Either `sendLoop` buffers the raw mvcc response and looks up `prevKV` (and builds the
response, with its `Range`s) when it flushes the pending responses after the `Created` response; or
`recvLoop` holds `sws.mu` across mvcc's `Watch` and the option writes (no deadlock: mvcc never
blocks on the stream's channel, `watcher.send` uses `select … default`).

## Notes

Found by code reading (the specs-only branch's review of batch 2b), then reproduced. Open question
for the user: fix it on the fork (then the strong `prevOk` holds for Kubernetes' watches) or keep
the weakened contract.
