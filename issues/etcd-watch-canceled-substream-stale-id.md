---
upstream: unchecked
checked: 2026-10-17
links:
  - etcd-io/etcd#22191 pr open: its fix (delete the canceled substream from substreams) introduces this upstream; the same fix is the verified fork's 107edf7e4
  - etcd-io/etcd#21969 issue closed: the panic the fix is for (issues/etcd-watch-progress-closed-substream.md); related, different bug
---

# After a server cancel and a reconnect, the watch client closes another watch that reuses the canceled one's id

- **Status**: a bug (a watch that silently stops receiving events, and `Watcher.Close()` that
  never returns), introduced by the fix of `etcd-watch-progress-closed-substream.md` (fork
  `goose-lean` `107edf7e4`, the pinned code; the same fix as etcd-io/etcd#22191). Not in upstream
  `main`, which instead panics on the same interleaving (`etcd-watch-resume-closing-substream.md`).
- **Where**: `client/v3/watch.go` at the pin `09669450f`: `run`'s `Canceled` case (620–630:
  `close(ws.recvc)`, `closing[ws]`, `delete(w.substreams, pbresp.WatchId)`; `ws.id` is left as
  it was), the `closingc` case (688–708: `closeSubstream(ws)`, then the early `return` when
  `len(w.substreams)+len(w.resuming) == 0`, else a cancel request for `ws.id`),
  `closeSubstream` (487–508: `delete(w.substreams, ws.id)` when `ws.id != InvalidWatchID`),
  `newWatchClient` (932–949: resets `id` only for the substreams in `substreams`), `run`'s
  deferred teardown (520–541: closes the `recvc` of the substreams in `substreams`/`resuming`
  only, drains `closingc` once per entry of `closing`, then `w.wg.Wait()`).
- **What happens**: watches A (id 0) and B (id 1) on one gRPC stream.
  1. The server cancels A (a `Canceled` response, e.g. the answer to a cancel request `run` sent
     for an event it could not dispatch); `run` closes A's `recvc` and removes A from
     `substreams`, but A keeps `id = 0`. A's goroutine exits and offers A on `closingc`.
  2. Before `run` takes A from `closingc`, the stream fails with a retryable error
     (`Unavailable`): `newWatchClient` moves B (the only substream in the map) to `resuming`,
     resetting B's id, but not A's (A is in no list); the new stream is opened and B's create
     sent.
  3. The new server stream numbers its watches from 0 again (etcd's `watchStream.nextID`): B is
     created with id 0, `substreams[0] = B`.
  4. `run` takes A from `closingc`: `closeSubstream(A)` deletes `substreams[A.id] =
     substreams[0]`, which is B. B is now in no list. If it was the last watch, `run` returns;
     its teardown closes no `recvc` of B and waits for B's goroutine (`w.wg.Wait()`), which
     blocks forever, and when the watcher is closed, B's goroutine blocks on `closingc`, which
     nobody reads: **`Close()` hangs**. Otherwise `run` sends a cancel request for id 0, the server
     cancels B, and B's `Canceled` finds no substream: B's channel is never closed and receives
     nothing more. Either way **B's events are dropped**.

  A third outcome: the stale cancel request for id 0 reaches the new stream after B's create, and
  the server cancels B: B's channel is closed with no error although the user never canceled it.

  Reproductions (tests of package `clientv3` with fake `pb.WatchClient`s; `cp` both files into
  `client/v3/`, the second uses the first's types):
  - `notes/pr-verify/etcd-22191/watch_stale_id_etcdlike_test.go`, `go test -run
    TestWatchStaleIDEtcdLike .`: an etcd-like fake server (per-stream ids from 0, `Canceled` only
    in answer to a cancel request for a live id), the realistic trigger (the user cancels A with an
    event in flight, so `run` sends the cancel request; concurrent `RequestProgress` calls keep
    `run` busy in `Send`), then `Unavailable`. At the PR head `34aa7c606` (the same `run` as the
    pin): of 300 trials, 6 lose B's event and hang `Close()`, 2 close B's channel silently
    (`notes/pr-verify/etcd-22191/etcdlike-at-pr-head.log`); with the fix below, 0
    (`etcdlike-with-suggested-fix.log`).
  - `notes/pr-verify/etcd-22191/watch_cancel_reconnect_test.go`, `go test -run
    TestWatchServerCancelThenReconnectKeepsOtherWatch .`: a scripted server (an unsolicited
    `Canceled` for A), 23 of 200 trials lose B's event and hang `Close()`
    (`reconnect-at-pr-head.log`; a stack dump shows `run` in `w.wg.Wait()` at the teardown, B's
    `serveSubstream` on `w.closingc <- ws`, the test in `Close`); with the fix, 0 of 200.
- **Expected**: a watch stays served (or is closed with an error) across a reconnect; `Close()`
  returns.
- **How the proof handles it**: `run`'s proof (`Proof/go_etcd_io/etcd/client/v3/watchGRPCStream__run.lean`)
  rests on `noRetryableStreamErr` (`Proof/go_etcd_io/etcd/client/v3/InvWatch.lean:169`): no stream
  error is retryable, so `newWatchClient` after `errc` is dead code in the verified behaviour and
  ids are never reused (the model's `CI`, `WatchClientModel.lean`, keeps ids distinct within one
  stream). The premise was introduced for `etcd-watch-resume-closing-substream.md`; this finding is
  a second reason it cannot be dropped without a further fix.
- **Possible fixes**: in the `Canceled` case, also set `ws.id = InvalidWatchID` after removing
  the substream (`notes/pr-verify/etcd-22191/suggested-fix.diff`): `closeSubstream` then scans
  `resuming` (not finding A, it does nothing) and the `closingc` case sends no cancel request for
  an id the server has already dropped (on the same stream that request was redundant anyway).
  The reproduction passes with it, as do the package's tests.
- **Related, not reproduced** (from reading the code, the reviewer of the PR's verification): a
  `Canceled` for a substream whose goroutine is still alive (etcd's server never sends one; the
  gRPC proxy, `server/proxy/grpcproxy/watcher.go`, forwards a backend's `Canceled` and may): `run`
  closes `recvc` and drops the substream from `substreams`; if the stream fails before the
  goroutine selects, `newWatchClient` closes `resumec`, the goroutine may take that case and exit
  as resuming (no `closingc` send), and it is not restarted (not in the map), while `closing` still
  counts it: the teardown's `closingc` drain waits forever. A fix: in `serveSubstream`'s `resumec`
  case, exit as non-resuming when `recvc` is already closed (a non-blocking receive first).
- **Found**: 2026-10-17, verifying etcd-io/etcd#22191 (`notes/pr-verify/etcd-22191.md`): following
  the removed substream's `id` through the reconnect path the proof's premise excludes.
