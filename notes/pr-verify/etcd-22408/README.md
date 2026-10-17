# Files for the verification of etcd-io/etcd#22408

The report is `notes/pr-verify/etcd-22408.md`. Revisions: PR head `baf38e97b` (etcd-io/etcd), its
upstream base `fd8581e04`, the fork branch `mit-pdos/etcd-grove` branch `pr-etcd-22408-goose-lean`
(commit `23ae96a4f`, the PR on the fork's `goose-lean` at `09669450f`).

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `backoff_probe_test.go` | `TestCacheBackoffStaysPositiveWithLargeMaxBackoff`: with `InitialBackoff = MaxBackoff = 1<<62` (accepted by `New`) the retry timers are `1<<62`, then `-1<<63`, then `0` (the doubling wraps). `TestCacheBootstrapsWithSlowGet`: a bootstrap `Get` that takes 6s never completes under the default 5s `GetTimeout` (10 attempts in a minute of virtual time, none completed); at the base the first one completes | PR head (both fail); base (the second passes; the first needs the PR's `Clock` use) | `cp backoff_probe_test.go <checkout>/cache/ && cd <checkout>/cache && GOTOOLCHAIN=go1.27.1 go test -run 'TestCacheBackoffStaysPositiveWithLargeMaxBackoff\|TestCacheBootstrapsWithSlowGet' -v .` |
| `backoff_probe-head.log` | the output of both tests at the PR head | PR head | as above |
| `backoff_probe-base.log` | `TestCacheBootstrapsWithSlowGet` at the base: passes | base `fd8581e04` | as above, `-run TestCacheBootstrapsWithSlowGet` |
| `base-pr-tests.log` | the PR's own three tests fail at the base (the fields are unread: `issues/etcd-cache-config-retry-unread.md`) | base `fd8581e04` with the PR's `cache/cache_test.go` | `git show baf38e97b:cache/cache_test.go > cache/cache_test.go && go test -run 'TestCacheRetriesUpstreamWatchWithConfiguredBackoff\|TestCacheBoundsBootstrapGetByGetTimeout\|TestNewCacheRejectsUnusableRetrySettings' ./cache` |
| `backoff_reset_test.go` | `TestReviewBackoffNeverResetsAfterHealthyWatch` (the reviewer's): after watches that stay healthy for 1h and are then cancelled, the retry downtime grows to `MaxBackoff` and stays there (`[50ms 100ms 200ms 400ms 800ms 1.6s 2s 2s 2s 2s]`): the backoff is never reset | PR head (fails); base (passes) | `cp backoff_reset_test.go <checkout>/cache/ && cd <checkout>/cache && GOTOOLCHAIN=go1.27.1 go test -run TestReviewBackoffNeverResetsAfterHealthyWatch -v .` |
| `backoff_reset-head.log`, `backoff_reset-base.log` | its output at the PR head and at the base (the logs name the file `review_backoff_reset_test.go`, its name when run) | PR head; base | as above |
