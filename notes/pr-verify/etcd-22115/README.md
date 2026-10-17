# Tests and logs for etcd-io/etcd#22115

The report is `../etcd-22115.md`. Revisions:
- **PR head**: `06eca942c` (etcd-io/etcd `pull/22115/head`).
- **Upstream base**: `6006f4058`.
- **Fork branch**: `mit-pdos/etcd-grove` branch `pr-etcd-22115-goose-lean`, `0ab4ed980`. That is the
  fork's `goose-lean` `09669450f` plus the PR's non-test diff.

Go tests run from an etcd checkout's `tests/` directory, with `GOTOOLCHAIN=go1.27.1`.

| File | What it shows | Revision | Command |
|---|---|---|---|
| `up-base.log` | The PR's own `TestMutexStaleUnlockDoesNotDeleteSameSessionRelock` fails without the fix: the newer incarnation is deleted (`mutex_test.go:162`). | upstream base, with the PR's `tests/integration/clientv3/concurrency/mutex_test.go` copied in | `go test ./integration/clientv3/concurrency -run '^TestMutexStaleUnlockDoesNotDeleteSameSessionRelock$' -count=1` |
| `up-head.log` | The same test passes with the fix. | PR head | same |
| `fork-tests.log` | The package's integration tests, the PR's included, pass on the verified fork code. | fork branch, with the PR's `mutex_test.go` copied in | `go test ./integration/clientv3/concurrency -count=1` |
| `mutex_trylock_unfenced_probe_test.go`, `probe.log` | `TestProbeTryLockDeleteUnfenced`: `TryLock`'s cleanup delete is still unfenced. Another `Mutex` of the same session re-creates the key just before the delete; the delete removes it, and that mutex's `Lock` returns `ErrSessionExpired`. The probe passes when the bug is present. | PR head | `cp mutex_trylock_unfenced_probe_test.go <etcd>/tests/integration/clientv3/concurrency/ && go test ./integration/clientv3/concurrency -run TestProbeTryLockDeleteUnfenced -count=1 -v` |
| `mutex_unlock_review_probe_test.go`, `review-probe.log` | The reviewer's probes. The log names the file by its original name, `review_probe_test.go`. `TestReviewProbeSameSessionStaleHandle`: a stale handle's fenced `Unlock` returns `nil` and leaves the newer key (create revision 4 against 2). `TestReviewProbeUnlockNeedsRead`: a write-only user's fenced `Unlock` gets `permission denied`, where the plain `Delete` succeeds; `Lock` also needs read. | PR head | `cp mutex_unlock_review_probe_test.go <etcd>/tests/integration/clientv3/concurrency/ && go test ./integration/clientv3/concurrency -run TestReviewProbe -count=1 -v` |
