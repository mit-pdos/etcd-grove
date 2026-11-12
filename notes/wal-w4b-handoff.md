# WAL W4b: handoff

Branch `wal-w4b`, worktree `/shared/etcd-grove-walw3`, cut from lean `491baacae1` (W4a landed;
`wal-w4` deleted). Coordinator: etcd-grove-81. Scratch: `/shared/tmp/wal-spec/w4b/`.

## State (2026-11-12, first agent)

- Plan written: `/shared/tmp/wal-spec/w4b/plan.md`. **Waiting for etcd-grove-81's approval.** No Lean
  written, no probe run.
- Two findings in W4a's landed trusted text (strength, not soundness; they block W4c), reported with
  proposed fixes as a separate trusted delta W4a.1 (plan §1):
  - F-W4b-1: `walDisk` (`∃ d, walDiskAt dir d ∗ ⌜H, sized⌝`) hides `unl`/`pur`/`cut`/`metadata`, so
    `Save`/`SaveSnapshot`/`Close` lose them; fix `walDiskM` (hides only the mark, as a lower bound;
    `atomic_acc` aborts to the same binder, which is why the mark must stay hidden).
  - F-W4b-2: `ValidSnapshotEntries`' prefix `H.take j` (review 2's B1) also after a crash, where
    `ReadAll`'s premise needs the whole history; fix: a second conjunct with `walUnlockedTok` giving
    the whole history.

## Next, in order (after approval)

Plan §4: A1-A3, A4-A6 (CP1), B (+ B1's `walDiskM` half after W4a.1), probes R1/R2 (CP2), C1-C4,
checks (CP3), STOP before `etc/land.sh`. New modules: `Proof/go_etcd_io/etcd/server/v3/storage/
WalHistLemmas.lean` (pure), `WalViews.lean`. W4b changes no trusted or exported text.

## Pitfalls

- `walImg` is over raw `WalOpG WalEnt` in the extension, the readers over `WalHist` (`EntryM`): state
  lemmas generically, with `walImg_map` / `toM_toRaw`.
- The server's `walRecs`/`walFiles`/`isWalStorage` stay (option B) until C6: do not edit them.
- `notes/status-history.md` is append-only.

## Build command

```
export TMPDIR=/shared/tmp
systemd-run --scope -q -p MemoryMax=64G lake --packages=/shared/tmp/manifest-ddc.json build Proof.go_etcd_io.etcd.server.v3.storage.WalHistLemmas
# full (CP3): flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake --packages=/shared/tmp/manifest-ddc.json build
```
