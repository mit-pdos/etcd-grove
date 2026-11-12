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
- CP1 approved by etcd-grove-81 (forms included).
- Part B (`ecb6bfac64`): B3 `walImg_append_cases`, `walImg_snoc_cases` (pure, in `WalHistLemmas.lean`,
  no mark premise needed); new module `WalViews.lean`: `walCrashKeeps`, `walDiskAt_crash_img`,
  `walDiskAt_crash_img_any`, `walDiskAt_crash_graceful`, `walDiskAt_walDisk`, `walDisk_excl`.
- Probes R1/R2: instrumented copy of the W3 tester (`tester-fixed` + `r2.go`) under
  `/shared/tmp/wal-spec/w4b/r2/` (`run.sh`; logs `*.log`, `*.r2log`). Findings (CP2 report):
  R2 (full runs, 3 models x 150 chains, per candidate history): `ReleaseLockTo` 8018 OK / 116 fail
  (clause 2, dormant records); `Open` 4166 OK / 6982 fail (6946 clause 1 at `j = p+1`: a received snapshot's record precedes the Save
  that commits it; 3 clause 2). R1: C2 as stated is false (entries above `a` saved before the
  snapshot record, purged with `k ≤ p`; the model's `walReleasePos` is coarser than Go's file naming).
- CP2 report sent (R1: C2 holds in every run under guard + Go file-naming bound `enti(H.take k)+1 < a`; R2: Open clause-1 failures at `j = p+1`); waiting for etcd-grove-81.

## Next, in order (after CP2)

1. B1's `walDiskM` half after W4a.1 lands.
2. Part C per CP2's decision on R1; full checks; CP3.

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
