# etcd-stream-interceptor-err-before-done

- **Finding**: `issues/etcd-stream-interceptor-err-before-done.md`
- **Target**: etcd-io/etcd, `main`
- **Branch**: `fix/etcd-stream-interceptor-err-before-done` in `~/etcd-fixes/etcd-stream-interceptor-err-before-done`.
  two commits: 9bc0dc213 adds the test, which fails there; 8330458d9 is the fix. Not pushed; the issue's test link
  (`#L24-L49`, the doc comment to the closing brace in the local file) is to be checked on GitHub after the push.
- **Base**: upstream `main` 3aaab3479b6c4f5fe1b2b8f33437093c2caae88a (2026-10-22); `interceptor.go` is the same as
  at the finding's revision (lines 286-304 as quoted there).
- **State**: draft (2026-10-23)
- **Upstream issue**: —
- **PR**: —

Commit messages to rewrite (drafts): `etcdserver: test the stream context's Err before Done` (no body); `etcdserver: do not report a stream's cancel reason before it is
done`, body "Err could return the cancel reason while Done was still open." (prefix: the package's history uses
`etcdserver:` and `v3rpc:`; #12196, which added the type, is under `etcdserver:`.)

## Security

A wrong `Err()` for a short window on a stream being cancelled by the member itself: no crash, hang, data loss or
auth bypass. A public issue.

## Precedent (Go's `context`)

Go fixed the same ordering in its own `cancelCtx`: golang/go#75533, "context: Err can return non-nil before Done
channel is closed" (closed), fixed by CL 705235, commit
[8ca209ec39](https://github.com/golang/go/commit/8ca209ec3962874ad1c15c22c86293edf428c284) "context: don't return a
non-nil from Err before Done is closed" (2025-09-18). CL 653795 (golang/go#72040) had made `Err` an atomic load of
the error, stored before `Done` was closed, so `Err` could be non-nil slightly before `Done` closed; the fix makes
`Err` wait on `Done` when the error is set ("Ensure the done channel has been closed before returning a non-nil
error", `context.go`), accepting a 3x slower non-nil `Err` to keep the documented contract. The Go team treated the
window as a bug although it lasts only a few instructions, which answers "is this worth fixing". A later commit,
785f9d843a (golang/go#80914), kept the guarantee while making it cheaper. Cited briefly in the issue's "Anything
else" at the user's request (the skill otherwise keeps other issues out of the issue).

## Duplicates checked (2026-10-23)

Searches (5, etcd-io/etcd): `cancellableContext` (2), `WithCancelCause` (2), `monitorLeader` (16),
`is:pr is:open interceptor` (8), `ErrGRPCNoLeader context Err Done` (8). No duplicate; no open PR touches
`cancellableContext`. Related, different:

- #12196 (merged PR, 2021): added `cancellableContext`, to tell a no-leader cancel from a client cancel in the
  watch metrics; silent on the `Err`/`Done` order. The window dates from it.
- #9739 (closed issue): client cancels logged as "no leader", what #12196 fixed.
- #21122 (merged PR, 2026-02): cause-aware handling of client cancels in lease keepalive forwarding; does not touch
  `interceptor.go`.
- Open PRs changing `interceptor.go` (#21764, #22259, #21401: audit logging, client IP in auth logs, debug logging)
  do not touch `cancellableContext`.

## Why the fix works

At the base, `Cancel(reason)` takes the write lock, stores the reason, unlocks, then calls the `WithCancel` cancel
function, which closes `Done()`. `Err()` takes the read lock and returns the reason if set. A call to `Err()` after
the unlock and before the cancel sees the reason while `Done()` is open.

With the fix, `Cancel` calls the cancel function before unlocking. `Err()` sees a non-nil reason only after taking
the read lock after `Cancel`'s unlock, by which time `Done()` is closed. The cancel function takes no lock of
`cancellableContext`: the inner `cancelCtx` cancels its children synchronously (a `WithCancel(c)` registers with the
inner `cancelCtx`, found through `Value`, and its cancel does not call `c.Err`), and children that cannot register
(custom contexts, `AfterFunc`) are cancelled from their own goroutines, which may call `c.Err()` and wait for the
unlock without blocking `Cancel`. So no deadlock.

## Test

`TestCancellableContextErrBeforeDone` replaces the `cancel` field `newCancellableContext` sets with a wrapper that,
at the moment `Cancel` calls it (before `Done()` is closed), calls `Err()` from another goroutine and waits up to
100 ms for its result; a non-nil result fails. At the base `Err()` returns the reason at once (fails
deterministically unless the goroutine is delayed 100 ms). With the fix `Err()` blocks on the lock until `Cancel`
returns, the wrapper times out and cancels, and `Err()` then returns the reason. It then checks that `Err()` is the
reason once `Done()` is closed (the wrapper's purpose). The finding's version called `Err()` directly in the wrapper,
which would deadlock with the fix (the wrapper runs under the lock). A black-box variant (a goroutine spinning on
`Err()` against a concurrent `Cancel`, checking `Done()` once `Err()` is non-nil) needs no field hook but hits the
window only sometimes; not measured. Cost of the chosen test: the 100 ms timeout at every run with the fix.

## Verification (go1.27.3 linux/amd64, 2026-10-23, at base 3aaab3479)

- At the tests commit 9bc0dc213: `cd server && go test ./etcdserver/api/v3rpc/ -run
  TestCancellableContextErrBeforeDone -count=20 -v`: 20 of 20 FAIL, each `interceptor_test.go:37: Err() = test
  reason before Done is closed`.
- At the fix commit 8330458d9: the new test `-count=100` ok (10 s: each run waits the 100 ms timeout);
  `-race -count=20` ok; `go test ./etcdserver/api/v3rpc/... -count=1` ok. From `tests/`: `go test ./integration/
  -run RequireLeader` (`TestGRPCRequireLeader`, `TestGRPCStreamRequireLeader`) ok; `./integration/clientv3/watch/
  -run TestWatchWithRequireLeader -count=3` ok; `./integration/clientv3/lease/ -run RequireLeader -count=3` ok;
  `./integration/clientv3/connectivity/` (whole package, 121 s) ok; `./integration/ -run 'TestV3Lease'` (144 s) ok.
- `gofmt -l etcdserver/api/v3rpc/` empty; `go vet ./etcdserver/api/v3rpc/` clean.

Not run: e2e, robustness, `make verify`.

`check.py`: no FAIL. WARN kept: the fix's one comment, which says why the cancel is under the lock (an ordering a
later edit could undo).

## If a reviewer asks

- Candidate fixes:
  1. Cancel under the lock (chosen): one line moved; the same structure as Go's `cancelCtx.cancel`, which sets the
     error and closes `Done` under one mutex. `Err` keeps its fast path.
  2. Cancel before storing the reason (the simplest reorder): a reader could see `Done()` closed and `Err()` the
     inner context's `context.Canceled`, the reason lost, which is what the type exists to avoid; rejected without
     running.
  3. `Err` checks the inner context first (`if err := c.Context.Err(); err == nil { return nil }`), or waits on
     `Done` when the reason is set (Go's own fix, 8ca209ec39): also correct; more lines than (1).
  4. Replace the type by `context.WithCancelCause` and `context.Cause`: `Err()` would then return
     `context.Canceled`, not the reason, changing what `watch.go`'s and `lease.go`'s `isClientCtxErr(...Err(), ...)`
     see; a refactor beyond this bug.
- Callers: `newStreamInterceptor` (the deferred `Cancel(nil)`) and `monitorLeader` (`Cancel(ErrGRPCNoLeader)` then
  `<-ss.Context().Done()`, under `smap.mu`): neither depends on the unlock happening before the cancel.
- Impact in etcd itself: `watch.go` reads `Err()` after `Done()` (no window) or after a stream error
  (`isClientCtxErr`), where the window changes at most how the error is logged and counted. Not reproduced through
  a server.
- The deferred `Cancel(nil)` after the handler returns overwrites a stored reason with nil; only goroutines the
  handler left running could see the change. Not part of this fix.
