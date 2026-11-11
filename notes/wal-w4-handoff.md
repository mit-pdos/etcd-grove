# WAL W4: handoff

Branch `wal-w4`, worktree `/shared/etcd-grove-walw3` (W3's worktree, reused), cut from lean
`e891d049fc` (W3 landed: F-Z/F-N1/F-N2 in the etcd pin `71f99a4bf`). Coordinator: etcd-grove-81.
Scratch: `/shared/tmp/wal-spec/w4/`.

## State (2026-11-11)

Phase 1 (the Draft) done and stopped at its hard stop: `/shared/tmp/wal-spec/w4/draft.md`. No Lean
edited, built or committed; this note is the only commit.

## The Draft in one paragraph

The trusted core is a local Goose extension `absDiskExt` (`GooseLang/Ext/AbsDisk/`, shared with
rung 3's bbolt arm) whose state maps a WAL directory to `WalDur` (history `H`, synced mark, purge
positions `unl`/`pur`/`cut`, metadata, `named`, `sized`) and whose crash relation is `walCrash`
(`walImg` per directory). The WAL stays names-only: one axiom per wal function the tester calls (11),
`TouchDirAll`, and the purge law (the tester's `purgeRound`, `trusted`, modelled by the extension's
purge step). The reader is the relaxed `walReadCut I k` (`walRead` at `k = 0`, `walReadFrom` with a
header correction at `k ≥ 1`). `walRecs`/`walFiles` become definitions (−2 axioms), the five laws keep
their statements; `walFiles` now means "the restart reads σ or a compaction of it" (C-W2). The closed
theorem is over `goose_crash_adequacy` with `[durableExt, absDiskExt]`.

## Next, in order

1. The coordinator's answers to the Draft's §9 decisions, and to finding K-N (§6).
2. If K-N goes ahead: W3b (targeted `-killpl` runs with `/shared/tmp/wal-spec/w3/tester` at the first
   start and at cuts; fork fix F-N4; nonissues; pin move: a hard stop).
3. W4a: the extension, `WalHist.lean`, the specs as axioms, walpb/fileutil names-only, `isWalStorage`
   restated, `walFiles` → definition; Freeze (`spec-reviewer` fresh + `axiom` skill).
4. W4b, W4c as the Draft's §8.

## Pitfalls

- `EntryM` takes `[GooseExts]`: the extension's state cannot mention it (Draft §1.1: raw `WalEnt`).
- Restart S3 (`/shared/etcd-grove-rs3`) edits `InvWal.lean`/`InvRestart.lean`: keep `walRecs`/
  `walFiles`/the laws' names and statements so W4 needs no edit there.
- The tester's `released` must be stored before its purge round (the oracle invariant's `pur` bound).
- `notes/status-history.md` is append-only.

## Build command

```
export TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json
flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake --packages=/shared/tmp/manifest-ddc.json build
```
