# WAL W4: handoff

Branch `wal-w4`, worktree `/shared/etcd-grove-walw3` (W3's worktree, reused), cut from lean
`e891d049fc` (W3 landed: F-Z/F-N1/F-N2 in the etcd pin `71f99a4bf`). Coordinator: etcd-grove-81.
Scratch: `/shared/tmp/wal-spec/w4/`.

## State (2026-11-11, W4a in progress; stopped at a design question)

W3b and the Draft's §9 decisions 1-8 approved (K-N confirmed, F-N4 pushed: goose-lean b18c2d500).
W4a so far:
1. lean merged (a259c0efd1: restart S3) — `2b86bf5f2f`.
2. etcd pin → b18c2d500 (translated from GitHub, no file changes; go.mod/go.sum of examples,
   k8s/etcd3, k8s/compactor from the published modules, `go mod verify`; `goose.py --check` clean
   without `--src`); W3b's two nonissues with `kn_test.go` — `edb11c84da`.
3. Trusted core, first part (built, not used by any result: tcb unchanged):
   `GooseLang/Ext/AbsDisk/Impl.lean` (`WalOpG`, `WalEnt`, `walImg`, `WalDur`, `walDurFresh`,
   `AbsDiskState`, `absDiskExt`, `walCrash`, `AbsDiskStep`, `absDisk_semantics`, the world
   assumptions in the module docstring) and `Proof/.../storage/WalHist.lean` (Draft §1.3: `WalOp`,
   `WalHist`, the `WalEnt`/`EntryM` bijection, `walLastHS`, `walMustSync`, `readEnt`,
   `walFoldChkFrom`, `walKeep`, `walRead`, `walNewest`, `walReadFrom`, `walReadCut`, `walReadR`).
   Forms decided (questions.md): `WalDur.meta` → `metadata` (`meta` is a Lean keyword); the steps'
   operation/mark/position chosen by the step (only `#dir`/`#md` passed), the axioms say which.

**Stopped at Q-W4a-1 (questions.md):** the Draft makes `walDisk` the extension's points-to and
`walRecs`/`isWalStorage`/`wal.bootOk` definitions over it, but does not say how the server (generic
in `GooseExts`, no `HasExt absDiskExt`) sees it, nor where `wal.bootOk`'s `walDisk dir []` comes
from: minted by a trusted slot it contradicts the extension's own `localStart` ownership (two
points-to for one directory, so `False`) in any closure that includes `absDiskExt`.

## Next, in order (after Q-W4a-1)

4. `GooseLang/Ext/AbsDisk/Specs.lean`: ghost state (one auth map, per-directory fragments; marks
   `walSyncedLb` as mono-nat per directory), `ExtInterp`, the specs of the steps, `ExtCrashInterp`
   (`walDisk_crash`), durableExt's `ExtCrashInterp` (identity).
5. walpb/fileutil names-only in the etcd project (`TouchDirAll`; walpb types for `walSnapAt`), then
   the 13 specs of Draft §1.4-1.5 as axioms (`Spec/.../storage/wal/*.lean`, `Proof/...` axioms).
6. `walRecs`/`walFiles` as definitions, the five laws re-proved, `isWalStorage` restated, per the
   answer to Q-W4a-1; split WalRecs's pure model out if `WalHist` ↔ `WalRecs` would cycle.
7. Checks (full build, tcb `--check --update` expect +12 −2, collections, interfaces, gen-init,
   goose), Freeze package `/shared/tmp/wal-spec/w4/freeze-w4a.md`; STOP before land.sh.

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

## After W4a

W4b, W4c as the Draft's §8 (Freeze review of W4a first: `spec-reviewer` fresh + the `axiom` skill).

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
