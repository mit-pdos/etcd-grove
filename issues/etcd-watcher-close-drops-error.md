---
upstream: known
checked: 2026-10-17
links:
  - etcd-io/etcd#19935 pr open: reports this bug and fixes it, but its new test `errors.Is(err, context.Canceled)` is of the accumulated error instead of the stream's, which makes `Close` return `context.Canceled` (wrapped) for a stream that was merely canceled, and still drop a real error that follows one (`notes/pr-verify/etcd-19935.md`)
  - etcd-io/etcd#10420 pr merged: introduced the "consider context.Canceled as a successful close" check this bug is in
---

# `Watcher.Close` drops a stream's real error when another stream reports `context.Canceled`

- **Status**: a bug (a wrong result): `Close` can return `nil` although closing one of its gRPC
  watch streams failed.
- **Where**: `client/v3/watch.go`, `(*watcher).Close` (lines 395–410 at the pinned `09669450f`;
  upstream `main` `b25719d10` has the same code at 395–410):
  ```go
  for _, wgs := range streams {
      if werr := wgs.close(); werr != nil {
          err = werr
      }
  }
  // Consider context.Canceled as a successful close
  if errors.Is(err, context.Canceled) {
      err = nil
  }
  ```
  A watcher has one stream per distinct outgoing-metadata context (`streamKeyFromCtx`). `err` keeps
  only the last stream's error, and the check is applied once, to that last error.
- **What happens**: with two streams, one whose `close` returns a real error `X` and one whose
  `close` returns `context.Canceled` (the usual result of closing a stream: `close` cancels the
  stream's context and `ContextError` maps grpc's `Canceled` to it), `Close` returns `nil` whenever
  the map iteration visits the canceled stream last, and `X` otherwise: the result depends on Go's
  random map order, and `X` is lost about half the time. Reproduction:
  `notes/pr-verify/etcd-19935/watch_close_errors_test.go`, `TestWatcherCloseKeepsRealError`
  (deterministic streams built in-package; fails at upstream `6d5eb7b5f` and at the pin, typically
  on the first iteration).
- **Expected**: the comment's intent: a canceled stream counts as closed successfully, the others'
  errors are returned (the doc of `Watcher.Close` only says "closes the watcher and cancels all
  watch requests").
- **How the proof handles it**: the spec `watcher.Close.spec`
  (`Spec/go_etcd_io/etcd/client/v3/watcher__Close.lean`) says nothing of the returned error
  (postcondition `True`), so the bug is outside what is verified. The branch `pr-verify/etcd-19935`
  states the canceled half of the intent (`watcher.Close.spec_canceledIsSuccess`) and proves it of
  this code, conditionally on every stream's `close` reporting `nil` or `context.Canceled`; the other half (a real error is kept) is what fails here.
- **Possible fixes**: skip a canceled stream's error per stream, and keep the others:
  ```go
  if werr := wgs.close(); werr != nil && !errors.Is(werr, context.Canceled) {
      err = errors.Join(err, werr)
  }
  ```
  (etcd-io/etcd#19935 with `werr` for `err` in the `errors.Is`; the three tests of
  `notes/pr-verify/etcd-19935/` pass with it.)
- **Found**: 2026-10-17, verifying etcd-io/etcd#19935 (`notes/pr-verify/etcd-19935.md`), by
  writing the intended spec of `Close` and testing both halves of it.
