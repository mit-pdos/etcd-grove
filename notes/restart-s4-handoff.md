# Restart S4 handoff (branch `restart-s4`, worktree `/shared/etcd-grove-rs4`, from `lean` `51e51adb99`)

Stage: S4 of the restart Scope (`/shared/tmp/restart-scope/scope.md`, "S4"; r2db batch 3): the hubs at
the restart point, `run` at `⟨|P|, A₀⟩`.

## Phase: plan approved (D1-D4, etcd-grove-81 under the user's delegation, 2026-11-12; `questions.md`, decisions.md "Restart S4"); baseline build, then the probe, then CP1

- Plan: `/shared/tmp/restart-s4/plan.md` (the statements old → new, §2 the frozen/exported table,
  §3 the order and checkpoints CP1-CP3, §4 decisions D1-D4, §5 the crash rungs).
- r2db's Scope copied to `/shared/tmp/restart-s4/r2db-scope.md` (from branch `r2db`).
- No Lean edited, nothing built yet.

## Done

- Baseline build at `b877c74340` (lean `51e51adb99` + notes): clean, 14035 jobs, exit 0
  (`/shared/tmp/restart-s4/base.log`).
- Probe (CP1), `Scratch/S4Probe.lean` (untracked; copy `/shared/tmp/restart-s4/S4Probe.lean`),
  `etc/lean-check.py -a` (kernel included): 0 errors, no `sorry`:
  - P1 `srvRunRows_of_rn` (Q38 (a)): `isRaftNode E γn r ⊢ ⌜(∀ m ∈ γn.a0, typ 0 ∨ 1) ∧ 0 + |a0| + 1 < 2^64⌝`
    (row 8 from `rnRestartOk`, `readyFits` from `rnEnvOk`'s `srvClusterOk`, `isCommittedLogLb_length`);
  - P2 `applyBuiltR` (drafted, plan §1.3) and `applyBuiltR_first`; `srvSnapOwn_of_boot` at `W64 |P|`
    and `acRes_read` at any auth state (both already generic);
  - P3 `goIdx_P`: `uint.Z (W64 |P|) = 0 + |P|` from row 6 and `P <+: A₀`;
  - P4 by reading: `stopCleanupImage.spec`, `stop_split`, `applyResR_start`, `srvRestR_start`,
    `restReplay(_closeI)`, `kvBatchR`, `restReplay_snoc` are generic in `rp`/`P`; `run`'s stop arithmetic
    (`EtcdServer__run.lean:1614-1630`) does not read `rp.b`; `raftNode.start.spec` is generic in `L`.

## Next, in order

1. CP1 reported to etcd-grove-81; on its go, plan §3 steps 2-6 (move `applyBuiltR`, P1 into
   `AuthCompRows.lean`; then `start`, `run`, the callers).

## Build

`flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake build --packages=/shared/tmp/manifest-ddc.json`
(targeted: the same without `flock`, with targets). `export TMPDIR=/shared/tmp`.

## Pitfalls (known before starting)

- `.lake/packages` must be the symlink to `/shared/etcd-grove/.lake/packages` (a fresh worktree's own
  clone makes lake compile Iris from scratch). Do not merge `lean` before CP3 (the SpecPlan/ sync).
- `Scratch/` is untracked: never `git add -A`.

- `isServerBuiltC`'s intro patterns name every conjunct (`isServerBuiltM_C`'s four `iintro`s): moving
  `Hsnap`/`Hloop`/`Happly`/`Happ` into `HBr` changes them all.
- Keep `isServerBuiltC`'s signature: `interface/.../etcdstart/Start.txt` prints its `congr_simp`.
- `run`'s one graceful dependency (S1's, not S4's): the snapshot arm's `|a0| < snapIdx`
  (`rnRestartOk_winAbove`); do not add another (crash-design §4.2).
