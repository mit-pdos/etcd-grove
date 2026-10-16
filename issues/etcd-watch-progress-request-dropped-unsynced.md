---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#17557 pr merged: introduced this behavior (fix of #17507); a review comment (scpmw) asks that `WatchProgressRequest`'s documentation say the server may send no response and the client should retry; not done
  - etcd-io/etcd#17507 issue closed: the regression #17557 fixed (requests ignored for good after one made while a watcher was unsynced)
  - etcd-io/etcd#15220 issue closed: why a progress response waits for every watcher to be synced (#15237)
---

# A watch progress request made while a watcher is unsynced gets no response

- **Status**: documentation (behavior the API's documentation does not state). Intended by
  upstream since #17557: Kubernetes re-requests; other clients waiting on the documented response
  wait forever.
- **Where**: at the etcd pin of `etc/goose.py` (`107edf7e4`): `serverWatchStream.recvLoop`
  (`server/etcdserver/api/v3rpc/watch.go:395-399`: `sws.watchStream.RequestProgressAll()`, result
  ignored), `watchableStore.progressIfSync` (`server/storage/mvcc/watchable_store.go:517-543`:
  returns `false` without sending if any watcher of the map is not in `s.synced`). Documentation:
  `clientv3.Watcher.RequestProgress` (`client/v3/watch.go:94`: "requests a progress notify
  response be sent in all watch channels"), `WatchProgressRequest` (`api/etcdserverpb/rpc.proto:830`:
  "Requests the a watch stream progress status be sent in the watch response stream as soon as
  possible"). `mvcc.WatchStream.RequestProgressAll`'s comment (`watcher.go:64-68`) does say
  "if all watchers are synced".
- **What happens**: a progress request on a stream any of whose watchers is unsynced (a watcher
  just created with a past start revision, a slow watcher, a victim) is dropped: no response, no
  retry when the watchers sync. The client's `RequestProgress` returns `nil` (it only sends the
  request). Not reproduced here (the code path is read at the pin); a reproduction: create a
  watch with `WithRev(1)` on a range with many old events, call `RequestProgress` at once, and
  observe no `IsProgressNotify()` response until a second request.
- **Expected**: either the documentation says the request may go unanswered while a watch is
  catching up (and that the client should retry), or the server answers once all watchers sync.
- **How the proof handles it**: the specs are partial correctness and say nothing about an
  answer: `RequestProgressAll.spec` returns an unconstrained boolean
  (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/watchStream__RequestProgressAll.lean:27`),
  `progressIfSync.spec`'s postcondition does not mention the send
  (`.../watchableStore__progressIfSync.lean:29`), `recvLoop.spec` answers create and cancel
  requests only (`Spec/.../v3rpc/serverWatchStream__recvLoop.lean:38`). Triage:
  `notes/bug-triage/etcd-17507.md` (proposal `watch-progress-answered`).
- **Possible fixes**: document it (the wording suggested in #17557's review); or keep one pending
  progress request per stream and answer it from `syncWatchers` when the stream's last unsynced
  watcher becomes synced (what #15237 tried with `deferredProgress`, retried only from
  `sendLoop`).
- **Found**: 2026-10-16, bug triage of etcd-io/etcd#17507 against the watch specs.
