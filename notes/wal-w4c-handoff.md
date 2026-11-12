# WAL W4c: handoff

Branch `wal-w4c`, worktree `/shared/etcd-grove-walw3`, cut from lean `219ddbbb83` (W4b landed;
`wal-w4b` deleted). Coordinator: etcd-grove-81. Scratch: `/shared/tmp/wal-spec/w4c/`.

Goal (the user, 2026-11-11): the first rung of the crash ladder. Prove that the WAL robustness tester
(`examples/etcd/wal`) never panics under kill, power loss and kill-then-power-loss crashes, over
the crash-aware WAL spec (W4a, W4a.1, W4a.2, W4b). The closed theorems are `etcd_wal_adequate` and
`etcd_wal_safe`.

## State (2026-11-12)

- Plan `/shared/tmp/wal-spec/w4c/plan.md` approved by etcd-grove-81 (Q1, Q2, Q3, Q5) and the user (Q4,
  `walCreateOk` as a listed world-assumption premise; its docstring names Create's cleanup I/O,
  wal.go:294-309). Recorded in `questions.md` (untracked, gitignored).
- **Tell etcd-grove-81 before touching `GooseLang/Ext/Durable`** (Q1 is shared with rung 3).
- Step 0 done in `c9840f1022`:
  - the tester is in `examples/etcd/wal` with T-1..T-9;
  - the driver beside it (`*_test.go`, `crashtest/`) sets `SegmentSizeBytes` (`segSizeFor`), and
    `walSaveOk` moved there;
  - goose project `etcd-wal` and `wal.toml` (`purgeRound` names-only); the translation builds
    (`GeneratedProof...examples.etcd.wal`).
- CP1 matrix: `/shared/tmp/wal-spec/w4c/runs/matrix.sh`, logs in `runs/cp1/*.log`, binary
  `/shared/tmp/wal-spec/w4c/wal.test` (built at the commit, before a doc-only edit and gofmt).
  - 9 runs: the W3b matrix seeds plus `l-*`, 10 incarnations x 40 ops.
  - Read each log's `violations N` line. **Any violation is a soundness finding: stop.**
- R1 (gen-init) finding: `etc/gen-init.py` needs an `IsPkgInit` instance module for the tester (a
  `Base.lean` as `examples/etcd/restart/Base.lean`, fact `True`) and one for `fileutil` (none exists:
  the "instance modules" W4a hit). With them, add the root
  `github_com.mit_pdos.etcd_grove.examples.etcd.wal` to `ROOTS` and run
  `etc/gen-init.py github_com.mit_pdos.etcd_grove.examples.etcd.wal go_etcd_io.etcd.client.pkg.v3.fileutil`.
  Tried, then reverted (it crashes on the missing instance: `gen`, `imods[0]`). Do this at step 2
  (Lean), with the other `Defs`.
- Not done in step 0: the count of restarts the bounds accept only through a purged prefix (needs
  instrumentation; optional); R4's `entRoC` probe (deferred to step 2).

- **CP1 result (2026-11-12): 9/9 runs PASS, 0 violations, 0 harness errors.**
  - Runs: kill, ordered, posix x2, kill-then-power posix and ordered (W3b seeds), and l-kill,
    l-posix, l-ordered (10 incarnations x 40 ops).
  - About 11,000 restarts checked.
  - CP1 reported to etcd-grove-81.

## Next, in order

1. (CP1 done.)
2. The purgeRound Freeze (hard stop): **written, at `7d75b77fa7`; STOPPED for etcd-grove-81's
   axiom-skill review.**
   - `Spec/.../examples/etcd/wal/purgeRound.lean` (the spec), `Proof/.../wal/purgeRound.lean` (the
     axiom), `Proof/.../wal/PurgeBody.lean` (the body, proved: `purgeRound_commit`, and `cut ≤ pur`
     in every reachable state, `absCutLePur_*`);
   - `examples/etcd/wal/purge_test.go` (five tests, PASS);
   - `etc/goose.py`: `etcd-wal`'s `lean_roots` gained `os=`, `io/fs=` (step 0's translation imported
     Perennial's `os`, which clashes with this repository's when imported with the WAL specs);
     retranslated;
   - Freeze package `/shared/tmp/wal-spec/w4c/freeze-purge.md`.
   - The purge-biased run (81's addition): `runs/purgebias.sh`, patch `runs/purgebias.patch` (not
     committed: applied, binary `/shared/tmp/wal-spec/w4c/purgebias.test` built, reverted), logs
     `runs/purgebias/*.log`; read `violations N` and `strict-rejected/relaxed-accepted N` (the count
     of restarts accepted only through a purged prefix). Result in the Freeze package §6.
   - After the review: apply its fixes; then step 2.
3. Steps 2-4 as in plan §8. Step 2 starts with Q1 (`GooseLang/Ext/Durable`): **tell etcd-grove-81
   first** (rung 3). R1: the tester's `Base.lean` (IsPkgInit, fact `True`) fails today on
   `raftpb`'s missing instance: it needs the instance modules of its imports first.

## Pitfalls

- **The crash obligation runs at `⊤` and cannot refute `crashed`.** So the old generation's invariant
  must be closed with its contents kept (crashlog's `cfInv_crash_keep`). This is why the durable
  extension's identity crash interpretation does not work for an invariant that also holds the WAL
  (plan §0.4).
- The landed `"WalPurge"` takes `k` by value: no `TrustedCode` model can perform it (plan §0.5).
- Since W4a revision 3, `Open` raises `unl` (persisting across crashes, clamped), so the tester's old
  `released`-based check is stronger than the spec (plan §0.3).
- The tester's oracle stores must precede the calls they cover: the `unl` bound before
  `ReleaseLockTo`, `pur` before `purgeRound`, `opens` before each `Open`.
- GOWORK=off only for our own Go test runs; never in the shell of `etc/goose.py`/`gates.sh`/`land.sh`.
- `notes/status-history.md` is append-only.

## Build command

```
export TMPDIR=/shared/tmp
systemd-run --scope -q -p MemoryMax=64G lake --packages=/shared/tmp/manifest-ddc.json build <module>
# full: flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake --packages=/shared/tmp/manifest-ddc.json build
```
