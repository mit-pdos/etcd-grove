# etcd-apply-lease-checkpoint-sections

- **Finding**: `issues/etcd-apply-lease-checkpoint-sections.md`
- **Target**: etcd-io/etcd, `main`; backport to `release-3.6`, `release-3.5` (same code there, not run)
- **Branch**: `fix/etcd-apply-lease-checkpoint-sections` in `~/etcd-fixes/etcd-apply-lease-checkpoint-sections` (commit a246d135a), pushed 2026-10-18 to `upamanyus/etcd`
  (`https://github.com/upamanyus/etcd/tree/fix/etcd-apply-lease-checkpoint-sections`), the branch the links in `issue.md` name.
- **Base**: upstream `main` b25719d10cdc41fb707b0d9f819c2529dec5d590 (2026-10-16)
- **State**: draft (2026-10-16). Replaces the fork's older draft `lease-checkpoint-one-section` (2a163496c, off
  f061acd09, left untouched): same fix, one minimal test instead of three, no lessor-level test.
- **Upstream issue**: —
- **PR**: —

## Duplicates checked (2026-10-16)

Searches (this run): `lease checkpoint consistent index`, `lease checkpoint atomic`, `LeaseCheckpoint persistTo`.
No duplicate, no open PR. Hits, all closed and different: #15247 (leases revoked when the leader is stuck on
fdatasync), #17232 (unit test failures), #13988 (consistent index vs snapshot index check), #13508 (merged: adds
checkpoint persistence, the persistence whose atomicity fails here). Already in the finding: #17132 (closed: TTLs reset
on restart because checkpoints were not persisted at all).

## Security judgment

Not treated as a security report. A client cannot send a lease checkpoint request (the leader's lessor proposes it),
and the effect needs a member crash between two backend commits during one checkpoint request, then that member
becoming leader before the leases are checkpointed again. The effect is a lease living past its TTL by at most what
the last lost checkpoint would have removed (bounded by the TTL), which is what every leader change did before
checkpoints were persisted. No acknowledged data is lost or corrupted.

## Verification

`TestLeaseCheckpointCommittedWithConsistentIndex` (`server/etcdserver/apply/backend_test.go`) is the issue's example:
a backend with batch limit 1 (it commits at every `Unlock` with a pending write) whose pre-commit hook saves the
consistent index (as `storage.BackendHooks` does) and records the remaining TTLs of leases 1 and 2 in every commit
that persists consistent index 3; a post-lock hook as `EtcdServer.getTxPostLockInsideApplyHook`; a lessor with
`CheckpointPersist`, leases 1 and 2 granted with TTL 600; then `applierV3backend.LeaseCheckpoint` for both leases with
remaining TTL 100 at applying index 3. Deterministic (no timing: the batch limit forces the commit).

- At the base (fix stashed, test kept): `cd server && go test ./etcdserver/apply/ -run
  TestLeaseCheckpointCommittedWithConsistentIndex -count=3 -race` fails 3/3 with `expected: []int64{100, 100}`,
  `actual: []int64{100, 0}`.
- With the fix: the same command passes (`-race`).
- `cd server && go test -count=1 ./lease/... ./etcdserver/apply/`: ok.
- `cd server && go build ./...`: ok. `gofmt -l lease etcdserver/apply ../etcdutl/etcdutl`: clean. `go vet
  ./lease/... ./etcdserver/apply/`: clean. `cd etcdutl && go build ./... && go vet ./etcdutl/`: ok.
- Toolchain go1.27.2 (auto-selected), linux/amd64.

Not run: `tests/integration` (`TestV3LeaseCheckpoint`), `tests/e2e`, `make verify`, the backports. Not reproduced: a
crash and restart of a member, or a lease expiring late on a cluster; the issue says so. That the restarted member
does not reapply the entry is from reading the server's apply loop (entries at or below the persisted consistent
index are skipped), not from a run.

## If a reviewer asks

- Why change the `Lessor` interface: the applier cannot hold the batch lock around per-lease `Checkpoint` calls,
  because `Lease.persistTo` takes the same (non-reentrant) lock, and taking the batch lock before `lessor.mu` would
  invert `Grant`'s lock order (`lessor.mu`, then the batch lock), which `Checkpoint` now follows too. The interface
  change touches `FakeLessor` and `etcdutl`'s `SimpleLessor` (both no-ops) and three call sites in `lessor_test.go`.
- Error semantics: `lessor.Checkpoint` ignored unknown leases and always returned nil, so the applier's early return
  on error never ran; the batch still ignores unknown leases and the applier returns its (nil) error.
- Cost: the batch lock is held across the whole request (up to `maxLeaseCheckpointBatchSize` = 1000 lease puts)
  instead of being taken once per lease; a `Txn` with many puts holds it the same way.
- Alternative: make the post-lock hook not advance the consistent index until the entry is done. That changes how
  every entry is persisted (#13766's design), not only checkpoints.
- Backports: `release-3.6` and `release-3.5` have the same `lessor.Checkpoint` (per-lease `persistTo`) and the
  post-lock hook; on 3.5 persistence is behind `--experimental-enable-lease-checkpoint-persist`. Not run there.
