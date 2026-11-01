---
upstream: none
checked: 2026-11-01
links:
  - etcd-io/etcd#12196 pr merged: added cancellableContext (the window dates from it); not about the Err/Done order
  - golang/go#75533 issue closed: the same Err-before-Done window in Go's own cancelCtx, fixed by golang/go@8ca209ec39
blocks-proof: yes
---

# server: a require-leader stream's context returns a non-nil Err while its Done channel is still open

For a gRPC stream opened with require-leader metadata (`clientv3.WithRequireLeader`), when the member
cancels the stream because it has lost its leader, the stream's `Context().Err()` returns the
no-leader error for a short time before the context's `Done()` channel is closed.

**Expected:** `Err()` should return nil until `Done()` is closed, as `context.Context` requires ("If
Done is not yet closed, Err returns nil"), and the no-leader error afterwards.

**Impact:** stream handlers that read `Context().Err()` while the member cancels a require-leader
stream for lack of a leader. etcd's own watch and lease handlers read `Err()` only after `Done()` is
closed or after a stream error, where the early error can at most change how that error is logged and
counted; no wrong result in etcd is known.

**Reproduction:** `TestCancellableContextErrBeforeDone` in
[`issues/etcd-stream-interceptor-err-before-done/interceptor_test.go`](etcd-stream-interceptor-err-before-done/interceptor_test.go),
copied into `server/etcdserver/api/v3rpc` at etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef
(2026-10-28), go1.27.3 linux/amd64. It wraps the context's internal cancel function to call `Err()`
from another goroutine at the moment `Cancel` (as `monitorLeader` calls it) reaches it:

```
$ go test ./etcdserver/api/v3rpc/ -run '^TestCancellableContextErrBeforeDone$' -count=1
--- FAIL: TestCancellableContextErrBeforeDone (0.00s)
    interceptor_test.go:37: Err() = test reason before Done is closed
FAIL
```

**Cause:** `cancellableContext.Cancel` stores the reason under its lock, releases the lock, and only
then closes `Done()`
([L288-L293](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/api/v3rpc/interceptor.go#L288-L293)),
while `Err` returns the stored reason without looking at `Done()`
([L295-L304](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/api/v3rpc/interceptor.go#L295-L304)).

## Proof

yes: the require-leader branch is excluded by the premise `v3rpc.runsNoRequireLeader` (no client asks
for a leader on a stream), which etcd's clients do not meet
(`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvStreamInterceptor.lean`): with the window
the wrapper cannot meet Perennial's `isContext`.

## Fix

**Branch**: `fix/etcd-stream-interceptor-err-before-done` in `~/etcd-fixes/etcd-stream-interceptor-err-before-done` (upamanyus/etcd, not pushed): 9bc0dc213 test, 8330458d9 fix
**Base**: etcd-io/etcd@3aaab3479b6c4f5fe1b2b8f33437093c2caae88a

**PR draft**:

Title: etcdserver: do not report a stream's cancel reason before it is done

[`cancellableContext.Cancel`](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/etcdserver/api/v3rpc/interceptor.go#L286-L293) stores the reason under its lock, releases the lock, and only then closes `Done()`, while [`Err`](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/etcdserver/api/v3rpc/interceptor.go#L295-L304) returns the stored reason without looking at `Done()`. In between, `Err` is non-nil on a context that is not done, which `context.Context` forbids. This PR closes `Done()` before releasing the lock, as Go's own `cancelCtx` does.

Fixes: the issue, once filed.

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

**If a reviewer asks**: canceling before storing the reason would lose the reason (`Err()` the inner
`context.Canceled`); `Err` checking `Done` first (Go's own fix, golang/go@8ca209ec39) is also correct,
with more lines; `context.WithCancelCause` would change what `Err()` returns to `context.Canceled`,
which the handlers' `isClientCtxErr` reads.

## Notes

The test reaches the window through the context's internal `cancel` field, not through a server:
the window is a few instructions wide. The user's 2026-10 review chose to report it (Go fixed the same
window in its own contexts).
