# WAL W4b: handoff

Branch `wal-w4b`, worktree `/shared/etcd-grove-walw3`, cut from lean `491baacae1` (W4a landed;
`wal-w4` deleted). Coordinator: etcd-grove-81. Scratch: `/shared/tmp/wal-spec/w4b/`.

## State (2026-11-12, second agent: checkpoint 1 reached)

- Plan approved (etcd-grove-81; `/shared/tmp/wal-spec/w4b/plan.md`). Its findings F-W4b-1/2 are fixed
  in W4a.1 (branch `wal-w4a1`, under the delta Freeze review; do not check it out here while the
  review runs). Part B's `walDiskM` views (B1) wait for W4a.1 to land.
- This worktree serves both branches: switching only rebuilds `WalDisk.lean` and four axiom files.
- Part A complete in `Proof/go_etcd_io/etcd/server/v3/storage/WalHistLemmas.lean` (no `sorry`; targeted
  build clean; `#print axioms` of the main lemmas: `propext`, `Quot.sound` only):
  - A1: `walImg_refl/_mono/_length_le/_snoc/_full/_prefix/_trans`, `walImg_map`, `walImg_getElem?`,
    `walImg_toM_iff`, `walImg_toM_ex`.
  - A2: `walReadCut_hs` (+ `walHsStep`, `walFoldChkFrom_hs`, ...).
  - A3: `walNewestPair_mem/_max/_last/_none`, `walNewestPair_fold_self`, `walNewest_pair`,
    `walNewest_eq_newestPair`, `walFoldChkFrom_base`, `walReadCut_base`, `walReadCut_snap`.
  - A4: `walEntsWf`, `walReadCut_wf`; `walIdxLe`, `walReadCut_last_le`.
  - A5: `walReadCut_ents_sub`, `walReadCut_ents_sub_raw`.
  - A6: `walLastSnapPos_le`, `walLastSnapPos_snoc`, `walLastSnapPos_img`, `walReleasePos_le_length`,
    `walRelGuard_snoc`.
- CP1 report sent to etcd-grove-81; waiting for its go.

## Next, in order (after CP1)

1. Part B (`WalViews.lean`): B2 `walDiskAt_crash_img` (+ `_any`), `walDiskAt_crash_graceful`; B3
   `walImg_snoc_cases`, `walImg_append_cases`; B1's `walDisk` half. B1's `walDiskM` half after W4a.1 lands.
2. Probes R1, R2 (Go, scratch under `/shared/tmp/wal-spec/w4b/`); CP2.
3. Part C (C1-C4); full checks; CP3.

## Pitfalls

- `walImg` is over raw `WalOpG WalEnt` in the extension, the readers over `WalHist` (`EntryM`): state
  lemmas generically, with `walImg_map` / `toM_toRaw`.
- The server's `walRecs`/`walFiles`/`isWalStorage` stay (option B) until C6: do not edit them.
- `notes/status-history.md` is append-only.
- `etc/lean-check.py` without `-a` can print a stale error list from before the edit; check with `-a`.

## Build command

```
export TMPDIR=/shared/tmp
systemd-run --scope -q -p MemoryMax=64G lake --packages=/shared/tmp/manifest-ddc.json build Proof.go_etcd_io.etcd.server.v3.storage.WalHistLemmas
# full (CP3): flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake --packages=/shared/tmp/manifest-ddc.json build
```
