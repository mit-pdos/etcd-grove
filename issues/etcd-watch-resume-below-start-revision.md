---
upstream: none
checked: 2026-10-23
links:
  - etcd-io/etcd#20221 issue closed: related, different trigger: a watch from a future revision got old events through a periodic progress notification from a lagging member (closed by #20229)
  - etcd-io/etcd#20229 pr merged: the server fix (973847aa24, `progressIfSync`'s `rev < w.startRev` refusal); does not cover a broadcast computed before the watch was registered
  - etcd-io/etcd#20263 pr closed: proposed a client panic on `nextRev` below `initReq.rev`; closed on the belief that #20229 makes the decrease unreachable, which the reproduction below contradicts
  - etcd-io/etcd#15248 pr merged: the client's `nextRev` from a progress notification (the line that lowers it here)
---

# A watch from a future revision can resume below its start revision after a reconnect

- **Server step corrected** (2026-10-21): step 1 below does not happen on a real server. Every
  supported branch's `progressIfSync` (`server/storage/mvcc/watchable_store.go`: `main`, release-3.4
  to 3.6, the fork pin) returns without a progress notification when a watcher's start revision is
  above the store's (`if rev < w.startRev { return false }`), for `WithProgressNotify` (`progress`)
  and `RequestProgress` (`progressAll`) alike. Not yet checked: a `RequestProgress` broadcast
  computed before this watch's create but sent (watch stream) after its `Created` (control stream),
  which the client would broadcast to the new substream. (2026-10-23: that path exists and
  reproduces at upstream `main`; see the note at the end.)
- **Reachable against etcd's own server** (2026-10-23, upstream `main` `3aaab3479b`): yes, through the
  progress-before-created ordering (`issues/etcd-watch-progress-before-created.md`). Integration
  test below, 3 failures in 3 runs. The client hardening is needed; see the dated note at the end.
- **Status**: bug (a watch delivers events below the start revision it asked for), reproduced
  against a real server at upstream `main` `3aaab3479b` (2026-10-23), and in the same client code
  at the pinned `upamanyus/etcd` `a8a459955`. Reproduced deterministically
  (3 runs of 3); fixed on the fork branch `watch-resume-fixes` (`16f73d6eb`, on `a8a459955`; not
  pushed, not yet the pin), whose regression test passes with the fix and fails without it.
- **Where**: `client/v3/watch.go` at `upamanyus/etcd` `8a24be2a3` (`a8a459955` has the same lines,
  shifted by 8): `serveSubstream` (792–913: `nextRev` starts at `initReq.rev`; for a non-created
  response, 866–867, `nextRev = wr.Header.Revision + 1`; 875, `ws.initReq.rev = nextRev`), the
  resumed create (`run`'s `errc` case, 679: `ws.initReq.toPB()`, `StartRevision: wr.rev`). The
  server's progress notification of a synced watcher (`server/storage/mvcc/watchable_store.go`,
  `progressIfSync`: `Revision: s.rev()` for every synced watcher; `watch` puts a watcher whose
  start revision is above the store's in `synced`).
- **What happens**: `Watch(ctx, key, WithRev(10), WithProgressNotify())` while the store is at
  revision 5:
  1. the server registers the watcher as synced (its start revision is in the future) and, with
     `WithProgressNotify` (or on `RequestProgress`, whose broadcast reaches every substream),
     sends it a progress notification at the store's revision 5;
  2. `serveSubstream` sets the resume revision to 6, below the watch's start 10;
  3. the stream fails with a transient error (`Unavailable`); `run` reconnects and re-creates the
     watch from revision 6: it delivers the events of revisions 6 to 9.

  Reproduction: `TestWatchResumeNotBelowStartRevision` (`client/v3/watch_resume_below_start_test.go`
  on the fork branch `watch-resume-fixes`, commit `16f73d6eb`): a fake `pb.WatchClient` plays the
  server (store at 5, the progress notification, then `Unavailable`) and checks the resumed
  create's `StartRevision`. Without the fix:

  ```
  watch_resume_below_start_test.go:95: the watch from revision 10 resumed from revision 6
  --- FAIL: TestWatchResumeNotBelowStartRevision (0.00s)
  ```
- **Expected**: a watch from revision `r` never delivers an event below `r` (`WithRev`'s
  documentation, `client/v3/op.go`: "the start revision of 'Watch' request").
- **How the proof handles it**: the client's watch was verified under `noRetryableStreamErr` (no
  reconnection) until 2026-10-20. Its contract (`rangeWatchEvOk`: every event at or above the
  watch's start revision) holds across a reconnect only over the fixed code: the resume revision
  stays above the contract's position (`notes/decisions.md`, D25), which the reconnection's proof
  now shows; the premise is gone.
- **Possible fixes**: move the resume revision only forward (the fork's fix: `else if
  wr.Header.Revision+1 > nextRev`); or keep `max(nextRev, initReq's original rev)` at the resumed
  create.
- **Reachability against etcd's own server** (noted 2026-10-21, `notes/watch-cut-plan.md`): step 1
  does not happen as written. Since upstream `973847aa24` (2025-06-26, "Skip sending progress
  notification for watch with starting revision in the future"; in both pins), `progressIfSync`
  sends no progress notification while a watcher of the stream has a start revision above the
  store's (`if rev < w.startRev { return false }`). The reproduction uses a fake server. Whether
  another ordering reaches it (a progress broadcast to a substream the server has not registered
  yet, as in `issues/etcd-watch-progress-before-created.md`) is unchecked. The client fix stays
  harmless either way, and the proof now relies on the guard, not on the client's start read (W2).
  (Settled 2026-10-23: another ordering reaches it; see the note below.)
- **Found**: 2026-10-20, designing the resume revision's invariant (D25, stage S1b: after a
  progress notification `rev - 1` must be at least the contract's position, which for a watch from
  a future revision is its start minus one, above the notification's revision).
- **Reachability with a real server** (2026-10-23, upstream `main` `3aaab3479b`): reachable, and the
  user sees a wrong result: an event below the watch's start revision.
  - The path: a client watch stream holds a watcher A, already synced. The client calls
    `RequestProgress(ctx)` and then `Watch(ctx, k, WithRev(start))`, with `start` above the store's
    revision. Both go through the stream's `reqc`, in that order (`client/v3/watch.go` 413–429, 304–359).
  - `recvLoop` answers the progress request at once (`server/etcdserver/api/v3rpc/watch.go` 395–398,
    `RequestProgressAll`). `progressIfSync` (`server/storage/mvcc/watchable_store.go` 517–543) checks
    only the watchers the stream has then; B is not one of them, so #20229's `rev < w.startRev` guard
    (528) never sees it. The `-1` response at the store's revision `p` goes on the mvcc channel.
  - Then the create registers B as synced, since its start revision is in the future
    (`watchable_store.go` 141–147), and puts `Created` on `ctrlStream` (`v3rpc/watch.go` 340, 357–367).
  - `sendLoop`'s select (411 ff.) can send `Created` first. The client adds B to `substreams` (`watch.go`
    601–606), then broadcasts the `-1` progress to every substream, B included (737–738, 745–753).
  - `serveSubstream` sets `nextRev = p + 1` (864) and `ws.initReq.rev = nextRev` (871), below `start`.
    No guard keeps `nextRev` from going down.
  - When the stream fails (`Unavailable`), `run` reconnects (666–679, `newWatchClient` 928–972) and
    re-creates B from `p + 1`. The server then delivers B's events from `p + 1` to `start - 1`. B's
    user also first sees a progress notification at `p`, below its own start revision.

  Reproduction: `TestWatchResumeBelowStartRevision`, in
  `~/etcd-fixes/watch-resume-below-start-investigate/tests/integration/clientv3/watch/zz_resume_below_start_test.go`
  (branch `investigate/watch-resume-below-start` off upstream `main` `3aaab3479b`, uncommitted, not
  pushed). It uses a 1-member cluster with `UseBridge`, and a fresh `clientv3.NewWatcher` per trial.
  Each trial does this:
  1. start a busy prefix watch with concurrent puts, so `sendLoop` has both channels ready;
  2. call `RequestProgress`, then `Watch("k", WithRev(rev+100))`;
  3. on a stale progress, put `k` (below the start revision) and `Bridge().DropConnections()`.

  Run from `tests/` with `go test ./integration/clientv3/watch -run TestWatchResumeBelowStartRevision
  -count=1 -v`. It failed in 3 runs of 3, at trials 52, 69 and 48, in about 4 s each:

  ```
  trial 52: the watch from revision 1661 received a progress notification at revision 1562
  after a reconnect, the watch from revision 1661 delivered an event at revision 1592 (the put at 1592)
  --- FAIL: TestWatchResumeBelowStartRevision (3.35s)
  ```

  So the client fix (only move `nextRev` forward, or never resume below the original start revision)
  is needed against etcd's own server, not just hardening. Fixing the server ordering
  (`etcd-watch-progress-before-created`) would also close this path. Upstream: #20263 proposed a
  client check on this decrease, and was closed because #20229 was believed to make it unreachable.
  #20221 reported the same symptom with a different trigger (a lagging member). Nothing upstream
  reports this path.
