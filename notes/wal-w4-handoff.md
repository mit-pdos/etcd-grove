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

**Q-W4a-1 decided: option B** (etcd-grove-81, user's delegation, 2026-11-11; questions.md). The
server's `walRecs`/`walFiles`/`isWalStorage`/`wal.bootOk` stay as today; W4a adds the extension,
the reader and the axioms for the tester only. The tcb diff is the new axioms only (≈ +13, none
removed; report it exactly). The Freeze package must say: until C6 the WAL has two parallel models
(the server's `walRecs`, the extension's `walDisk`) with nothing linking them, and no closed etcd
theorem uses the new axioms.

**Option A, deferred to C6 (its starting design):** `trivialExts := [idIssueExt, absDiskExt]` (the
examples' closures gain `AbsDiskGpreS` and `HasExt absDiskExt`); `walDisk`/`walAbsent` defined
without the instance, as `idIssueFragD` (`if h : HasExt absDiskExt then <points-to> else False`), so
server definitions take no `HasExt`; the sealed slot `wal.bootRes` takes `walAbsent
(config.walDirOf dd "")` (and `wal.bootRes_intro` gains it), each example's start passing it from
the extension's `localStart`, so no trusted slot mints a points-to (else two points-to for one
directory, `False`); then `walRecs`/`walFiles` become definitions over `walDisk` (−2 axioms), the five
laws re-proved, `isWalStorage` restated (Draft §2-§3). Same for the restart (`walFiles` carries
`walDisk`, consumed, not minted).

## Next, in order

4. `GooseLang/Ext/AbsDisk/Specs.lean`: ghost state (one auth map of `Option WalDur` per directory with
   exclusive per-directory fragments, `walSyncedLb` a mono-nat per directory, `dirDurable` persistent),
   `ExtInterp` (localStart: the whole map, as `durableOwn`), WP specs of the steps, `ExtCrashInterp`
   (`walDisk_crash`, Draft §1.2); durableExt's `ExtCrashInterp` (identity; precedent:
   `examples/osfs/crashlog`, Perennial `GooseLang/CrashAdequacy.lean`).
5. walpb (types) and `client/pkg/v3/fileutil` names-only in the etcd goose project (`Code/**.toml`,
   `etc/goose.py` package list), then the 13 specs of Draft §1.4-1.5 as axioms
   (`Spec/go_etcd_io/etcd/server/v3/storage/wal/*.lean`, axioms in `Proof/...`; TouchDirAll under
   `client/pkg/v3/fileutil`; the purge model's `purgeRound.impl` comes with the tester in W4c, so in
   W4a its law is stated over the extension's step: decide the form, report it).
6. Checks: full build (lock + 64G), `tcb-report --check --update` (report the exact diff),
   collections, `gen-interface --check` (new APIs?), `gen-init --check`, `goose --check`;
   notes/decisions.md "WAL W4a" + STATUS entry (oldest to status-history, append-only);
   Freeze package `/shared/tmp/wal-spec/w4/freeze-w4a.md`; STOP before land.sh.

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
