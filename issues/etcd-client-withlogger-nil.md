---
upstream: unchecked
links:
---

# client/v3: `Client.WithLogger(nil)` makes the client's later logging panic

- **Status**: open (a precondition the API does not state; not filed). Found while verifying PR
  etcd-io/etcd#20731 (`notes/pr-verify/etcd-20731.md`); the PR does not change it.
- **Where**: `client/v3/client.go` at 09669450f (`etc/goose.py`'s etcd pin): `WithLogger(lg)`
  stores `lg` as the client's logger unchecked (`c.lg.Store(lg)`), and `GetLogger()` returns it;
  the client's internals log through it without a nil check: the retry interceptor
  (`retry_interceptor.go`, `Debug`/`Warn` on every retry), `isSafeRetry`, the round-robin backoff
  function (`roundRobinQuorumBackoff`'s closure, `Debug` on every attempt), the watcher.
- **What happens**: after `c.WithLogger(nil)` (public, deprecated), the first of these to log
  dereferences a nil `*zap.Logger` and panics (zap's methods do not accept a nil receiver).
  `newClient` itself never stores nil (it falls back to a default logger), so only this setter
  reaches it.
- **In the proofs**: the premise `isClientLogger` (`Proof/go_etcd_io/etcd/client/v3/InvClient.lean`:
  the stored logger is never nil), part of `retryClientOk`, is where the proofs assume it.
- **Reproduction**: `notes/pr-verify/etcd-20731/review_pr20731_test.go`,
  `TestReviewNilLoggerPanics` (at the PR head; the same holds at the pin): it recovers
  `runtime error: invalid memory address or nil pointer dereference` from the backoff function
  of a client given `WithLogger(nil)`.
- **Fix**: ignore nil in `WithLogger` (or store `zap.NewNop()`), or document that `lg` must not
  be nil.
