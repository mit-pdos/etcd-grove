# Reproduction and Probe Artifacts for `etcd-io/etcd#22650`

This directory contains standalone Go unit tests and test logs for [`etcd-io/etcd#22650`](https://github.com/etcd-io/etcd/pull/22650) (`server: propagate raftRequest error from lease Checkpointer`).

## Files

- `checkpointer_error_test.go`: Unit test (`TestNewServerCheckpointerPropagatesRaftRequestError` in `package etcdserver`) exercising the `SetCheckpointer` closure wired in `NewServer` (`server/etcdserver/server.go:398-407`) when `features.LeaseCheckpoint` is enabled and `srv.raftRequest` returns an error (`errors.ErrTooManyRequests`) during `srv.lessor.Renew`.
  - On base (`bc9c3868ced67e518fb2fecba44ce0fa70b7303b`), the closure discards both return values of `srv.raftRequest` and returns `nil`, so `Renew` succeeds (`ttl=100, err=nil`) while leaving the lease's expiry shortened to the stale `remainingTTL` (`20s`).
  - With PR `#22650` (`9cb80879d8f7d2a97a8c8b2120034d6bf0b5872b`), the closure returns the `err` from `srv.raftRequest` and `Renew` fails with `errors.ErrTooManyRequests`.
- `test-base.log`: Output of running `TestNewServerCheckpointerPropagatesRaftRequestError` against base `server/etcdserver/server.go` (`FAIL`).
- `test-pr.log`: Output of running `TestNewServerCheckpointerPropagatesRaftRequestError` against PR `#22650` (`PASS`).
- `renew_checkpoint_race_test.go`: Unit test (`TestLessorRenewConcurrentCheckpointShortensExpiry` in `package lease`) demonstrating the remaining race in `lessor.Renew` (`server/lease/lessor.go:412-455`) when a scheduled `Checkpoint(id, r)` (`0 < r < l.ttl`) applies between `Renew`'s `le.mu.RUnlock()` at line 414 and `Renew`'s `le.mu.Lock()` at line 442:
  1. `ScheduledCheckpointAppliesDuringClear`: `l.remainingTTL > 0` initially (`clearRemainingTTL == true`); during `le.cp`, `Checkpoint(id, 0)` applies first and then an in-flight scheduled `Checkpoint(id, 5)` applies before `Renew` re-acquires `le.mu.Lock()`. `Renew` calls `l.refresh(0)` without clearing `l.remainingTTL`, shortening `l.expiry` to `now + 5s` while returning `(100, nil)` to the caller and leaving `RemainingTTL: 5` in memory and in bbolt.
  2. `ScheduledCheckpointAppliesBetweenRUnlockAndLock`: `l.remainingTTL == 0` initially (`clearRemainingTTL == false`); after `Renew` releases `le.mu.RUnlock()` at line 414 and before it acquires `le.mu.Lock()` at line 442, a scheduled `Checkpoint(id, 5)` applies. `Renew` skips `le.cp`, acquires `le.mu.Lock()`, and calls `l.refresh(0)` without clearing `l.remainingTTL`, shortening `l.expiry` to `now + 5s` while returning `(100, nil)` and leaving `RemainingTTL: 5` in memory and in bbolt.
- `test-renew-checkpoint-race.log`: Output of running `TestLessorRenewConcurrentCheckpointShortensExpiry` against PR `#22650` (`FAIL` on both subtests).

## How to Run

From the Goose etcd worktree (`/root/etcd-pr/etcd-22650/server`):

```bash
# 1. Test PR #22650's Checkpointer error propagation fix:
cp /shared/etcd-grove-pr/etcd-22650/notes/pr-verify/etcd-22650/checkpointer_error_test.go etcdserver/
GOTOOLCHAIN=go1.27.1 go test -v -run '^TestNewServerCheckpointerPropagatesRaftRequestError$' ./etcdserver/
rm etcdserver/checkpointer_error_test.go

# 2. Reproduce the remaining concurrent Checkpoint/Renew race in lessor.Renew:
cp /shared/etcd-grove-pr/etcd-22650/notes/pr-verify/etcd-22650/renew_checkpoint_race_test.go lease/
GOTOOLCHAIN=go1.27.1 go test -v -run '^TestLessorRenewConcurrentCheckpointShortensExpiry$' ./lease/
rm lease/renew_checkpoint_race_test.go
```
