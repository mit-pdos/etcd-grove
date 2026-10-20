---
upstream: unchecked
checked: 2026-10-20
links: []
---

# A watch canceled during a reconnect can be handed a nil `WatchChan`

- **Status**: bug (`Watch` may return a nil channel, on which a receive blocks forever, instead of a
  closed one), in the same code at upstream `main` and at the pinned `upamanyus/etcd` `8a24be2a3`.
  Reproduced deterministically for the part `run` does (3 runs of 3); the last step, `Watch`'s
  `select` picking `retc`, needs `Watch`'s goroutine to reach its receive late, which the test
  plays itself. Fixed on the fork branch `watch-resume-fixes` (`a8a459955`, on `04375baaa`; not
  yet the pin, not pushed), whose regression test passes with the fix and fails without it.
- **Where**: `client/v3/watch.go` at `upamanyus/etcd` `8a24be2a3`: `waitCancelSubstreams`
  (978–1012: for a resuming substream whose watch's context is done, `close(ws.outc)`, `ws.outc =
  nil`, then `closingc`; the same for an already closing one, 985–991), `closeSubstream` (487–494:
  `select { case ws.initReq.retc <- ws.outc: default: }`), `watcher.Watch`'s receive (373–386:
  `select` on `wr.retc`, `ctx.Done()`, `donec`; `return ret`).
- **What happens**: a watch whose create is in flight (no `Created` yet, so its `retc` is still
  empty) when the gRPC stream fails with a transient error:
  1. `run` reconnects; while `openWatchClient` retries, the watch's context is canceled;
     `waitCancelSubstreams` marks the substream closing, closes its `outc` and sets it to `nil`,
     and posts it on `closingc`;
  2. `run` takes it from `closingc`: `closeSubstream` sends `ws.outc`, now `nil`, on `retc`
     (buffered, empty: the send succeeds);
  3. `Watch` (the caller's goroutine, if it reaches its second `select` only now) finds both
     `retc` and `ctx.Done()` ready; if Go picks `retc`, it returns the nil channel. A `for range`
     over it, or a receive, blocks forever instead of seeing the channel closed (the documented
     signal of a canceled watch).

  Reproduction: `TestWatchResumeNilChannelOnRetc` (`client/v3/watch_resume_nil_retc_test.go` on
  the fork branch `watch-resume-fixes`, commit `a8a459955`): a fake `pb.WatchClient` plays the
  server (its `Watch` blocks until the test takes the new stream, holding `run` in
  `openWatchClient`); watch `B` keeps the stream alive; the test plays the late `Watch` goroutine
  of watch `A` (it sends `A`'s `*watchRequest` on the stream's `reqc` itself), fails the stream
  before `A` is created, cancels `A`'s context while `run` reconnects, and reads `A`'s `retc`.
  Without the fix:

  ```
  watch_resume_nil_retc_test.go:106: retc carries a nil WatchChan: Watch() may return a channel that never closes
  --- FAIL: TestWatchResumeNilChannelOnRetc (0.10s)
  ```

  With the fix nothing is sent on `retc` (and `Watch` returns its own closed channel at
  `ctx.Done()`).
- **Expected**: `Watch` returns a channel that is closed when the watch's context is canceled; never
  a nil one.
- **How the proof handles it**: the client's watch was verified under `noRetryableStreamErr` (no
  reconnection, so `waitCancelSubstreams` never saw a substream) until 2026-10-20. The contract
  `isEtcdRangeWatcher` returns an SPSC channel (`isSpsc`), which a nil channel is not: the
  reconnection is now verified over the fixed code (`notes/decisions.md`, D25;
  `closeSubstream`'s nil-`outc` case), and the premise is gone.
- **Possible fixes**: in `closeSubstream`, send `outc` on `retc` only when it is not nil (the
  fork's fix: a nil `outc` means the context is done, which `Watch` reports with its own closed
  channel); or have `waitCancelSubstreams` keep `outc` and let `closeSubstream` close it.
- **Found**: 2026-10-20, designing the verification of the reconnection (D25, stage S0:
  `waitCancelSubstreams` writes `outc`, which the proof had read-only).
