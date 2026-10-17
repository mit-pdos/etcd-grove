# Files for etcd-io/etcd#18779 (`DLocker`)

The report is `notes/pr-verify/etcd-18779.md`.

Revisions:

- **fork**: `mit-pdos/etcd-grove` branch `pr-etcd-18779-goose-lean`, commit `995ced462`. This is the fork's `goose-lean` (`09669450f`) plus the PR's non-test diff.
- **PR head**: upstream `9786c9e1c` (`git fetch https://github.com/etcd-io/etcd pull/18779/head`).

Both test files belong in `tests/integration/clientv3/concurrency/` of the checkout. To run them:

```
cp <file> <checkout>/tests/integration/clientv3/concurrency/
cd <checkout>/tests
go test ./integration/clientv3/concurrency -run '<Names>' -v -count=1
```

Use `GOTOOLCHAIN=go1.27.1` for the fork and `GOTOOLCHAIN=go1.23.2` for the PR head.

| File | What it shows | Runs against | Log |
|---|---|---|---|
| `dlocker_fence_test.go` | `TestDLockerRevFencing`: successive `NewDLocker` holders get increasing `Rev()` values. `Rev()` is `-1` before `Lock` and after `Unlock`. After holder 1's lease is revoked, holder 2's `Rev()` (10) is above holder 1's (8), and holder 1 keeps its stale 8. | fork, PR head (both pass) | `probe-fork.log`, `probe-pr-head.log` |
| `dlocker_fence_test.go` | `TestDLockerRevKeyRecreated`: the schedule of `issues/mutex-lock-recreated.md`. B's `Lock` returns nil after D's, while D holds the lock, and `B.Rev()=3 < D.Rev()=5`. The later caller gets the smaller token, so "monotonically incremental" fails here. A fenced storage still rejects B once D has written. | fork, PR head (both pass, which confirms the behaviour) | same |
| `dlocker_review_test.go` | Written by the reviewer. `TestReviewSameSessionEqualTokens`: two DLockers on one session both hold, with equal tokens. `TestReviewSharedLockerGoroutines`: one DLocker shared by two goroutines gives no exclusion; both see the same `Rev()`, and after one `Unlock` the other sees `-1`. `TestReviewSessionExpiredStaleRev`: after `ErrSessionExpired`, `Rev()` is still a positive, stale value. | fork, PR head (all pass) | `review-probe-fork.log`, `review-probe-pr-head.log` |
