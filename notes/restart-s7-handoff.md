# Restart S7 (restart1): handoff (2026-11-14)

Worktree `/shared/etcd-grove-rs56`, branch `restart-s7` (off `lean`). Plan: `notes/restart-s7-scope.md`
(approved 2026-11-14, its "Approved" section). Probe report: `notes/restart-s7-probe.md`.

## Done
- The approvals recorded (`notes/restart-s7-scope.md`, `questions.md`); `notes/restart-scope.md`'s table: S7 is
  restart1, R2s-A keeps its name.
- **S7.0 (CP-a):** `examples/etcd/restart1/restart1.go` (one member, `NPuts = 11` in-process `Put`s of keys
  `"k"+byte(i)`, the `AppliedIndex()` wait, `HardStop`, `BuildServer` + `Start` again, a `Leader() != 0` wait,
  one in-process linearizable `Range` of `["k", "l")` checked exactly), `restart1_test.go` (`TestMemberID`,
  `TestRun`: counts the restart's log messages and fields), project `restart1` in `etc/goose.py`, the
  translation `Code/.../examples/etcd/restart1.lean`, `GeneratedProof/.../restart1.lean` (built).
  Test: 20/20 runs pass in separate processes; WAL snapshot record at index 14, backend kept at consistent
  index 15 (19/20; 1/20 at 14 = the last entry), commit 15, no snapshot sent.
- **S7.1 (CP-b):** `Scratch/S7Probe.lean` (untracked; probes P1-P4, checked) and the report.

- **Landed** S7.0 + notes: `lean` `19cd2cb540` (2026-11-14).
- **S7.2' (P3), done** (`7560eecea4`): `memberBuiltR` in `NewServer.specR`'s post shape; `wp_Start_builtR`
  proved from `Start.spec`; `Start_builtR_spec` deleted (restart3's `startMember.wp_proofRestart` uses
  `wp_Start_builtR`). Restarted-lessor check: `srvLeaseRd` in the mode `none` also accepts `lease.srvInvAt`
  at the recovered snapshot (laws `srvLeaseRd_of_srvInv`, `_of_srvInvAt`, `_srvInv`).
- **P4-a statement, done** (same commit): `memberRestartFacts` in `BuildServer.specRestart`'s precondition,
  `memberBoot_restartFacts`; restart3's draft `startMember.specRestart`/`restartCheck.spec` carry it.
  `BuildServer.specRestart`'s proof is S7.4, not started.
- **P2-a**: Go check done, law designed (`notes/restart-s7-p2a.md`), not yet written.

- **srvLeaseRd consumer check** (etcd-grove-81's condition on the change, 2026-11-14):
  `etc/importers.py --uses srvLeaseRd` lists `etcdstart.{Defs,Restart,Served,ServedLease,newServerMode}`;
  with the laws' users (`srvLeaseRd_lessorRd`, `srvLeaseRd_srvInv`, `lease.srvInv_first`): `Served` passes it
  through (`memberUp_served`); `newServerMode` and `Restart` build it; `ServedLease`'s mode-`none` branch takes
  only the reader side (`srvLeaseRd_lessorRd`), its `mono`/`revocable` branches go through
  `srvLeaseRd_srvInv` (`m ≠ none`, the empty start); the lease-expiry example (`revocable`) reads the empty
  first snapshot through `srvLeaseRd_srvInv` then `lease.srvInv_first`. **No mode-`none` consumer relies on the
  empty start.**

## Next, in order
1. P2-a: the law in `isRaftMsg` (raft side, then `srvRestartRows_single`); stop at the raft interface diff
   for etcd-grove-81's review.
2. S7.4: `BuildServer.specRestart`'s proof (allocate the per-incarnation names, `idIncarnation_alloc`).
3. S7.5: the example's proofs (P1's three lemmas), link, adequacy, `Results.lean`, collection; Freeze of the
   theorem before its proof is linked. `etc/gen-init.py`'s `ROOTS` gets the package then.

## Pitfalls
- Run the Go test once per process (`go test -c`, then the binary per run): Run leaves the restarted member
  running, and a second `TestRun` in the same process deletes its directory under it (`failed to release wal`).
- Without the `Leader()` wait, the restarted member's first linearizable read fails with `leader changed`.
- GOWORK=off for the Go tests only; never for `etc/goose.py`/`etc/land.sh`.

## Commands
- Go test: `cd examples && GOWORK=off systemd-run --scope -q -p MemoryMax=32G go test -count=1 -v ./etcd/restart1/`
- Translation: `etc/goose.py --project restart1` (GOWORK unset).
- Build: `systemd-run --scope -q -p MemoryMax=64G lake build --packages=/shared/tmp/manifest-ddc.json <module>`.
- Probe check: `LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json etc/lean-check.py Scratch/S7Probe.lean`.
