# etcd-io/etcd#22387: files the report relies on

Revisions:
- **PR head**: `31197665285b7fc8b150684868adec32fbbee02b` (etcd-io/etcd#22387).
- **Upstream base**: `e9e56564d` (the PR's merge base with upstream `main`).
- **Fork branch**: `mit-pdos/etcd-grove` branch `pr-etcd-22387-goose-lean` (`c429f7597`): the fork's
  `goose-lean` (`09669450f`) plus the PR's non-test diff.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `election_campaign_getfail_test.go` | `Election.Campaign`'s new existence check: when the context is canceled during it (the wait already succeeded), `Campaign` returns `context canceled` but leaves its key in place with the leader session cleared, so `Resign` deletes nothing, and another candidate's `Campaign` blocks (both tests fail). On the base, `Campaign` returns nil there (no check) and both tests skip. | PR head; base as control | `cp election_campaign_getfail_test.go <checkout>/tests/integration/clientv3/concurrency/ && cd <checkout>/tests && go test ./integration/clientv3/concurrency -run TestElectionCampaignCanceledAfterWait -count=1 -v` |
| `campaign_canceled_after_wait.pr-head.log` | Output of the command above at the PR head: both tests `FAIL`. | PR head | (as above, filtered to the test's own lines) |
| `campaign_canceled_after_wait.base.log` | Output at the base: both tests `SKIP` (`Campaign` returned nil). | upstream base | (as above) |
| `mutex_recreated_after_wait_test.go` (reviewer) | `TestMutexLockRecreatedAfterWait`: a sibling `Mutex` of the same session deletes and re-creates the shared key after B's wait returned and before its final `Get`. D (another session) gets the lock, and B's `Lock` also returns nil. Fails at the PR head and at the base: the pinned code's `issues/mutex-lock-recreated.md`, which the PR does not fix. | PR head; base | `cp mutex_recreated_after_wait_test.go <checkout>/tests/integration/clientv3/concurrency/ && cd <checkout>/tests && go test ./integration/clientv3/concurrency -run TestMutexLockRecreatedAfterWait -count=1 -v` |
| `mutex_sibling_cancel_test.go` (reviewer) | `TestMutexLockSiblingCanceledSessionAlive`: a sibling `Mutex` on the same session is canceled and unlocks the shared key. With the PR, B returns `ErrSessionExpired` at once while the session is alive (TTL 59). At the base, B keeps waiting. Fails at the PR head, passes at the base. | PR head; base | same, `-run TestMutexLockSiblingCanceledSessionAlive` |
| `reviewer_tests.pr-head.log`, `reviewer_tests.base.log` | The two reviewer tests' output at the PR head and at the base. | PR head; base | `-run 'TestMutexLock(RecreatedAfterWait\|SiblingCanceledSessionAlive)'` |

The PR's own tests (`TestMutexLockSessionExpired`, `TestElectionCampaignSessionExpired`) and the
package's unit and integration tests pass in the fork worktree: `go test ./concurrency` from
`client/v3`, and `go test ./integration/clientv3/concurrency` from `tests/` with the PR's test diff
applied (not committed on the fork branch).
