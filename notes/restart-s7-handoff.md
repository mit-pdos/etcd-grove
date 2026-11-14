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

## Next, in order (after etcd-grove-81's decisions on the report)
1. S7.2 (P3): `memberBuiltR`'s body in `specR`'s post shape; `wp_Start_builtR` from `Start.spec` (copy of
   `wp_Start_built`, `srvBuiltR_C`, `srvStop.slot_intro`); delete `Start_builtR_spec`.
2. S7.4 (P4-a): `BuildServer.specRestart`'s precondition gains the persistent part of `memberBoot` at the stopped
   names; its proof (allocate the per-incarnation names, `idIncarnation_alloc`).
3. S7.3 (P2-a): the raft law, then `srvRestartRows_single`.
4. S7.5: the example's proofs (P1's three lemmas), link, adequacy, `Results.lean`, collection; Freeze of the
   theorem before its proof is linked. `etc/gen-init.py`'s `ROOTS` gets the package then (not yet: no proof).

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
