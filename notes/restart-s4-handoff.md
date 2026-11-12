# Restart S4 handoff (branch `restart-s4`, worktree `/shared/etcd-grove-rs4`, from `lean` `51e51adb99`)

Stage: S4 of the restart Scope (`/shared/tmp/restart-scope/scope.md`, "S4"; r2db batch 3): the hubs at
the restart point, `run` at `⟨|P|, A₀⟩`.

## Phase: plan written, waiting for etcd-grove-81's approval (2026-11-12)

- Plan: `/shared/tmp/restart-s4/plan.md` (the statements old → new, §2 the frozen/exported table,
  §3 the order and checkpoints CP1-CP3, §4 decisions D1-D4, §5 the crash rungs).
- r2db's Scope copied to `/shared/tmp/restart-s4/r2db-scope.md` (from branch `r2db`).
- No Lean edited, nothing built yet.

## Next, in order

0. Baseline build (the worktree's `.lake/build` came from `49fff2f95c`; stage B's changes rebuild).
1. After the go: the probe P1-P4 (`Scratch/S4Probe.lean`, untracked, never committed), CP1.
2. Then plan §3 steps 2-6.

## Build

`flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake build --packages=/shared/tmp/manifest-ddc.json`
(targeted: the same without `flock`, with targets). `export TMPDIR=/shared/tmp`.

## Pitfalls (known before starting)

- `isServerBuiltC`'s intro patterns name every conjunct (`isServerBuiltM_C`'s four `iintro`s): moving
  `Hsnap`/`Hloop`/`Happly`/`Happ` into `HBr` changes them all.
- Keep `isServerBuiltC`'s signature: `interface/.../etcdstart/Start.txt` prints its `congr_simp`.
- `run`'s one graceful dependency (S1's, not S4's): the snapshot arm's `|a0| < snapIdx`
  (`rnRestartOk_winAbove`); do not add another (crash-design §4.2).
