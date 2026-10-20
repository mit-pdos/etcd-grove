---
upstream: unchecked
checked: 2026-10-20
links:
  - etcd-io/etcd#22191 pr open: its fix (delete the substream from substreams after close(recvc)), the same as the verified fork's 107edf7e4, introduces this bug: the dropped substream keeps its watch id
---

# After a reconnect, a server-canceled watch's stale id can delete the resumed watch that reuses it

- **Status**: bug (a lost watch: no more events, its channel never closed, and possibly `run`
  stuck in its teardown), introduced by the fix of
  [etcd-watch-progress-closed-substream](etcd-watch-progress-closed-substream.md) (the verified
  fork's `107edf7e4`, cherry-picked from `1ac646214`; etcd-io/etcd#22191 proposes the same fix
  upstream), so present at the pinned `upamanyus/etcd` `8a24be2a3` and not in upstream `main`
  (where the same window is the panic of
  [etcd-watch-resume-closing-substream](etcd-watch-resume-closing-substream.md)). Reproduced
  (3 runs of 3 hit it, within 5 to 54 trials); fixed on the fork branch `watch-resume-fixes`
  (`04375baaa`, on the pin; not yet the pin, not pushed), whose regression test passes with the
  fix and fails without it (3 of 3).
- **Where**: `client/v3/watch.go` at `upamanyus/etcd` `8a24be2a3`: `watchGRPCStream.run`'s
  `Canceled` case (620–632: `close(ws.recvc)`, `closing[ws]`, `delete(w.substreams,
  pbresp.WatchId)`, the substream's `id` kept), the `closingc` case (688–707: `closeSubstream`,
  then `return` if no substream is left, else a cancel request for `ws.id`), `closeSubstream`
  (487–509: `delete(w.substreams, ws.id)` when `ws.id != InvalidWatchID`), `newWatchClient`
  (932–976: resets the ids of the substreams in `substreams` only), the teardown (`w.wg.Wait()`,
  539).
- **What happens**: watch `A` (id 0) and watch `B` (id 1) share a gRPC watch stream.
  1. `A`'s context is canceled: its goroutine exits (`closing`) and waits on `closingc`; `run`
     is busy;
  2. an event for id 0 cannot be dispatched (`A`'s `donec` is closed), so `run` sends a cancel
     request for 0; the server answers it with a `Canceled` response, on which `run` closes `A`'s
     `recvc` and drops `A` from `substreams` (the fork's fix), but `A.id` stays 0;
  3. the stream fails with a transient error (`Unavailable`); `run` reconnects before it takes
     `A` from `closingc` (both ready: Go picks at random); `B` is resumed, and the new stream
     registers it as id 0 (the server's ids are per stream, from 0);
  4. `run` takes `A` from `closingc`: `closeSubstream(A)` deletes `substreams[0]`, which is `B`.
     If no substream is left, `run` returns; its teardown closes nothing of `B` (it is in neither
     `substreams` nor `resuming`) and waits forever in `w.wg.Wait()` for `B`'s goroutine, so
     `watcher.Close()` hangs too. Otherwise it sends a cancel request for id 0 on the new stream,
     which cancels `B` on the server. Either way `B` never receives another event and its channel
     is never closed.

  Reproduction: `TestWatchResumeStaleCanceledID` (`client/v3/watch_resume_stale_id_test.go` on the
  fork branch `watch-resume-fixes`, commit `04375baaa`): a fake `pb.WatchClient` plays the server
  (its stream's `Send` blocks until the test releases it, to make `run` busy while two of its
  select's cases become ready), 300 trials of the steps above; a trial hits the bug when `B` does
  not get the event the new stream sends for id 0. Without the fix (the test file alone, by `go
  test -overlay` at `8a24be2a3`):

  ```
  watch_resume_stale_id_test.go:200: trial 5: the resumed watch lost its event (run deleted it under the canceled watch's stale id); trials lost at each stage: [0 0 0 0 1 0 4 1]
  --- FAIL: TestWatchResumeStaleCanceledID (2.20s)
  ```

  With the fix, 300 trials pass (about 230 of them reach the final check).
- **Expected**: a watch's teardown removes only that watch; a reconnect keeps every watch still
  served.
- **How the proof handles it**: the client's watch was verified under `noRetryableStreamErr` (no
  reconnection: `notes/STATUS.md`, "W-C"), which excludes step 3. The reconnection's verification
  (`notes/decisions.md`, D24) is to be over the fixed code.
- **Possible fixes**: in `run`'s `Canceled` case, reset the substream's id to `InvalidWatchID`
  after dropping it from `substreams` (the fork's fix: the server has forgotten the id;
  `closeSubstream` then finds the substream in neither `substreams` nor `resuming`, and `run`
  sends no cancel request for it); or have `closeSubstream` delete `substreams[ws.id]` only when
  it is `ws`. For etcd-io/etcd#22191: either change belongs with its fix.
- **Found**: 2026-10-20, designing the verification of the reconnection (D24, stage S0: what a
  resumed substream's id means across streams).
