# etcd-apply-lease-checkpoint-sections

- **Finding**: `issues/etcd-apply-lease-checkpoint-sections.md`
- **Target**: etcd-io/etcd, `main`; backport to `release-3.6`, `release-3.5` (same code there, not run)
- **Branch**: `fix/etcd-apply-lease-checkpoint-sections` in `~/etcd-fixes/etcd-apply-lease-checkpoint-sections`, two commits:
  9dc872522 (`apply: test that lease checkpoints are committed with their index`) adds the test, which fails there;
  60d7c705e (`lease: persist all checkpoints of a request in one backend transaction`) is the fix. Force-pushed 2026-10-19 to `upamanyus/etcd` (replacing a246d135a); the issue's test link (`#L34-L100`) checked on GitHub: the test, doc comment to closing brace.
- **Base**: upstream `main` 22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4 (2026-10-18); the code the fix touches is
  unchanged since b25719d10.
- **State**: draft, rebuilt to the skill's standard (2026-10-18). Replaces the fork's older drafts
  `lease-checkpoint-one-section` (2a163496c, off f061acd09) and a246d135a, both left on the fork.
- **Upstream issue**: —
- **PR**: —

## Duplicates checked (2026-10-16, rechecked 2026-10-18)

Searches: `lease checkpoint consistent index`, `lease checkpoint atomic`, `LeaseCheckpoint persistTo` (2026-10-16);
`lease checkpoint consistent index`, `lease checkpoint persist atomic`, open issues and PRs mentioning
`LeaseCheckpoint` (2026-10-18: nothing new, nothing open). No duplicate, no open PR. Hits, all closed and different:
#15247 (leases revoked when the leader is stuck on fdatasync), #17232 (unit test failures), #13988 (consistent index
vs snapshot index check), #13508 (merged: adds checkpoint persistence, the persistence whose atomicity fails here).
Already in the finding: #17132 (closed: TTLs reset on restart because checkpoints were not persisted at all).

## Security judgment

Not treated as a security report. A client cannot send a lease checkpoint request (the leader's lessor proposes it),
and the effect needs a member crash between two backend commits during one checkpoint request, then that member
becoming leader before the leases are checkpointed again. The effect is a lease living past its TTL by at most what
the last lost checkpoint would have removed (bounded by the TTL), which is what every leader change did before
checkpoints were persisted. No acknowledged data is lost or corrupted.

## Why the fix works

- At the base: the server sets `ConsistentApplyingIndex` to the entry before applying it; the post-lock hook
  (`EtcdServer.getTxPostLockInsideApplyHook`) runs at every `LockInsideApply` and moves the consistent index to it;
  the backend's pre-commit hook (`storage.BackendHooks`) saves the consistent index in every commit. That makes an
  entry's writes atomic with its index only if they are made under one `LockInsideApply`. `LeaseCheckpoint` calls
  `lessor.Checkpoint` per lease, and each call persists its lease with `Lease.persistTo` under its own
  `LockInsideApply`/`Unlock`. A commit at the first `Unlock` (batch limit) or between two of them (the periodic
  commit, every 100 ms by default) persists the entry's index with the first leases only; on restart, entries at
  or below the persisted index are skipped, so the others keep their old remaining TTL.
- The fix: `Lessor.Checkpoint(cps []*pb.LeaseCheckpoint)` takes the request's checkpoints; `lessor.Checkpoint`
  takes `lessor.mu`, then (when checkpoints are persisted) the batch lock once, and writes each known lease with
  `Lease.unsafePersistTo(tx)` (split out of `persistTo`, which `Grant` still uses). A commit can no longer fall
  between two leases of one entry. `LeaseCheckpoint` calls it once.

## Verification (go1.27.2 linux/amd64)

`TestLeaseCheckpointCommittedWithConsistentIndex` (`server/etcdserver/apply/backend_test.go`, a new file; lines
34-100) is the issue's example: a backend with batch limit 1 (it commits at every `Unlock` with a pending write)
whose pre-commit hook saves the consistent index (`ci.UnsafeSave`, the first thing `storage.BackendHooks` does) and
records the remaining TTLs of leases 1 and 2 in every commit that persists consistent index 3; a lessor with
`CheckpointPersist`, leases 1 and 2 granted with TTL 600; the server's post-lock hook (its body copied, since it is
a method of `EtcdServer`); applying index 3; then `applierV3backend.LeaseCheckpoint` for both leases with remaining
TTL 100. It asserts only the guarantee: every commit persisting index 3 holds both checkpoints (and, as the setup
check, that some commit persisted index 3). Deterministic: the batch limit forces the commit, and no commit has
pending writes before the first lock.

The test calls `verify.DisableVerifications()`, as `server_test.go`'s apply and snapshot tests do: etcd's unit
tests run with `ETCD_VERIFY=all` (`scripts/test.sh`), and with the post-lock hook set, `LockInsideApply` panics
unless called from `EtcdServer.applyEntries`. The previous draft's test (a246d135a) lacked this and hangs under
`ETCD_VERIFY=all` (checked: `lg.Panic("Called outside of APPLY!")` with the batch lock held, then the cleanup's
`backend.Close` blocks until the 30 s timeout).

- At the tests commit 9dc872522 (`cd server && ETCD_VERIFY=all go test ./etcdserver/apply/ -run
  TestLeaseCheckpointCommittedWithConsistentIndex -count=1`): fails, `expected: []int64{100, 100}`,
  `actual  : []int64{100, 0}` (`remaining TTLs of leases 1 and 2 committed with consistent index 3`).
- At the fix commit 60d7c705e: the same test passes with `ETCD_VERIFY=all -count=3 -race` and without
  `ETCD_VERIFY`; `ETCD_VERIFY=all go test -count=1 ./lease/... ./etcdserver/apply/`: ok (lease, leasehttp, apply).
- `gofmt -l server/lease server/etcdserver/apply etcdutl/etcdutl`: empty. `cd server && go build ./... && go vet
  ./lease/... ./etcdserver/apply/`: ok. `cd etcdutl && go build ./... && go vet ./etcdutl/`: ok.

Not run: `tests/integration` (`TestV3LeaseCheckpoint`), `tests/e2e`, `make verify`, the backports. Not reproduced:
a crash and restart of a member, or a lease expiring late on a cluster; the issue says so. That the restarted member
does not reapply the entry is from reading the server's apply loop (entries at or below the persisted consistent
index are skipped), not from a run.

## If a reviewer asks

- Why change the `Lessor` interface; a smaller fix? Tried in thought, against the code (2026-10-18):
  - Hold the batch lock in the applier around the per-lease calls: `Lease.persistTo` takes the same lock again
    (`sync.Mutex`, not reentrant), so it deadlocks unless the lessor changes anyway.
  - A new lessor method beside `Checkpoint(id, remainingTTL)`: the applier holds a `Lessor`, so the method goes in
    the interface too (three implementations either way), and the old method would be left with no caller.
  - So the signature change is the smallest. It touches `FakeLessor` and `etcdutl`'s `SimpleLessor` (both no-ops)
    and three call sites in `lessor_test.go`; no other implementation or caller in the repository.
- Lock order: `lessor.Checkpoint` takes `lessor.mu` then the batch lock, as `Grant` does and as the old
  `Checkpoint` did through `persistTo`. (mvcc puts take the batch lock and then `lessor.mu` in `Attach`; all of these
  run on the apply goroutine.)
- Error semantics: `lessor.Checkpoint` ignored unknown leases and always returned nil, so the applier's early return
  on error never ran; the batch still ignores unknown leases and the applier returns its (nil) error.
- Cost: the batch lock and `lessor.mu` are held across the whole request (up to `maxLeaseCheckpointBatchSize` = 1000
  lease puts) instead of once per lease; a `Txn` with many puts holds the batch lock the same way.
- Alternative: make the post-lock hook not advance the consistent index until the entry is done. That changes how
  every entry is persisted (#13766's design), not only checkpoints.
- The test copies the server's post-lock hook and disables `ETCD_VERIFY` (see Verification). The alternative,
  driving `EtcdServer.apply` with a real uber applier, needs most of a server (`server_test.go`'s harnesses use
  `uberApplierMock`); the apply-level test is deterministic and shows the same commit.
- Backports: `release-3.6` and `release-3.5` have the same `lessor.Checkpoint` (per-lease `persistTo`) and the
  post-lock hook; on 3.5 persistence is behind `--experimental-enable-lease-checkpoint-persist`. Not run there.
