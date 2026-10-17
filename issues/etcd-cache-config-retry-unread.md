---
upstream: unchecked
checked: 2026-10-17
links:
  - etcd-io/etcd#22408 pr open: reads all three fields from the cache's Config (verified on branch pr-verify/etcd-22408)
---

# cache: `InitialBackoff`, `MaxBackoff` and `GetTimeout` are never read

**Status**: documentation the code contradicts. Three `Config` fields of the `cache` package are
documented and settable (`WithInitialBackoff`, `WithMaxBackoff`, `WithGetTimeout`) but have no
effect.

**Where**: `cache/cache.go` at the pinned etcd revision (`etc/goose.py`, 09669450f):
`getWatchLoop` (line 312) takes its backoff from a fresh `defaultConfig()` (line 313), not `c.cfg`,
and waits a constant `time.After(backoff)` (line 326); `get` (line 339) runs the bootstrap
`c.kv.Get` on the cache's internal context with no timeout. `cache/config.go` lines 28-33 document
`InitialBackoff` ("the first delay to wait before retrying an upstream etcd Watch"), `MaxBackoff`
("caps the exponential back-off between successive upstream watch retries") and `GetTimeout` ("the
timeout applied to the first Get() used to bootstrap the cache").

**What happens**: the watch loop retries every 50ms whatever `WithInitialBackoff`/`WithMaxBackoff`
say, with no exponential back-off; a bootstrap `Get` that never answers blocks the loop (and every
`WaitReady`) until `Close`. Reproduction: the tests of etcd-io/etcd#22408
(`TestCacheRetriesUpstreamWatchWithConfiguredBackoff`, `TestCacheBoundsBootstrapGetByGetTimeout`,
`TestNewCacheRejectsUnusableRetrySettings` in its `cache/cache_test.go`) fail against the upstream
base fd8581e04 (log: `notes/pr-verify/etcd-22408/base-pr-tests.log`).

**Expected**: the documented back-off (first delay `InitialBackoff`, doubling, capped at
`MaxBackoff`) and a `GetTimeout` bound on the bootstrap `Get`.

**In the proof**: `Spec/go_etcd_io/etcd/cache/v3/Cache__getWatchLoop.lean` does not constrain the
backoff (the model has no time), so the pinned code meets it; the branch `pr-verify/etcd-22408`
verifies the PR's version, with the schedule as a pure model (`backoffAt`).
