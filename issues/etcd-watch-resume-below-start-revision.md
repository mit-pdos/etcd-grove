---
upstream: unchecked
checked: 2026-10-20
links: []
---

# A watch from a future revision can resume below its start revision after a reconnect

- **Status**: bug (a watch delivers events below the start revision it asked for), in the same code
  at upstream `main` and at the pinned `upamanyus/etcd` `a8a459955`. Reproduced deterministically
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
- **Found**: 2026-10-20, designing the resume revision's invariant (D25, stage S1b: after a
  progress notification `rev - 1` must be at least the contract's position, which for a watch from
  a future revision is its start minus one, above the notification's revision).
