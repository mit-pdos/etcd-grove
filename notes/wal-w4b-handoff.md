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

## Paused (2026-11-12, by etcd-grove-81, after CP2 approval, forms included)

- R1 and R2 go into the W4a.1 revision (separate worktree), together with W4a.1's soundness fix
  (`Create`'s exact `named = false` together with `walNamed`; post-commit syncs no body can realize).
  The lower bounds on `m` and `named` change `walDiskM`'s shape.
- The 116 clause-2 `ReleaseLockTo` cases (dormant records) are accepted as a documented limitation.
- W4b resumes after W4a.1 (including R1, R2) lands. Then, in order:
  1. merge lean; rebuild `WalHistLemmas`/`WalViews` against the new `walReleasePos`/`walRelGuard`
     (A6's `walReleasePos_le_length` and `walRelGuard_snoc` will need restating);
  2. B1's `walDiskM` half, in the new `walDiskM` shape;
  3. Part C (C1-C4), with C2's premises from W4a.1's R1 fix (guard plus the file-naming bound);
  4. full checks; `notes/decisions.md` "WAL W4b"; STATUS entry; CP3.

## Resumed (2026-11-12, etcd-grove-81): W4a.1 landed (lean `9b00c0c988`)

- `walDiskM` is gone: `walDiskAt` itself is now the lower-bound view (mark and `named` as lower
  bounds). `Close` and VSE are atomic; new proved steps `wp_WalSyncLen`, `wp_WalNamedLen`,
  `walOpening_lenLb`; new `WalBodies.lean`. R1/R2 are now W4a.2 (designed in another worktree);
  Part C's C2 premises wait for it.
- The second agent stopped at about 2/3 of its context before starting this; a fresh agent does:
  1. merge lean `9b00c0c988` into `wal-w4b` (common-rules.md's GOWORK rule);
  2. rebuild `WalHistLemmas` and `WalViews`, adapting to the lower-bound `walDiskAt`
     (`walDiskAt_crash*` in `Specs.lean` may have new shapes: re-read them; `walCrashKeeps`'s
     `d'.m = d.m` / `d'.named = d.named` likely become `≤`/implications);
  3. B1's half over `walDiskAt` (whatever conversions the new view needs: `walDiskAt_walDisk`,
     `walDisk_excl`, and any monotonicity of the lower bounds);
  4. the parts of C that do not depend on `walReleasePos` (C1 `walReadR_mono`, `walReadCut_zero`;
     `StorCompacts` and its basic laws; C4's identity shape where it needs no release bound);
  5. targeted builds of both modules; checkpoint report to etcd-grove-81 and stop.

## Resumed steps 1-5 done (2026-11-12, third agent; CP3a report sent, waiting for etcd-grove-81)

- Step 1: lean `9b00c0c988` merged (`bbe8f1c484`, clean).
- Step 2: `WalHistLemmas`/`WalViews` built against the lower-bound `walDiskAt` with no change: the
  crash lemmas (`walDiskAt_crash*`) kept their statements (they speak of the program's copy, whose
  `m`/`named` the crash keeps), and `walReleasePos`/`walRelGuard` did not change in W4a.1 (R1/R2 are
  W4a.2's), so A6 needs no restating yet.
- Step 3 (B1, `WalViews.lean`): `walDisk_walDiskAt`, `walDiskAt_lower_m`, `walDiskAt_forget_named`,
  `walDiskAt_excl`; and `walCrashKeeps_trans` (kill then power loss).
- Step 4 (C first half, end of `WalHistLemmas.lean`): `walReadCut_zero`, `walReadCut_pos`,
  `walReadR_mono`, `walReadR_zero`, `walReadR_of_read`, `walReadCut_b_le_commit`, `walSnapAtBase`,
  `walReadCut_snapAtBase`, `StorCompacts` (+ `_refl`, `_trans`, `_eq` = C4's identity shape, `_wf`),
  `walRead_compacts_self` (C3's `k = 0` case).
- Step 5: targeted `lake build ...WalViews` clean; `#print axioms` of the new lemmas: `propext`,
  `Quot.sound`, `Classical.choice` only. Nothing imports either module.
- Next (after W4a.2 lands with the release bound): C2 `walReadFrom_compacts` (premises: guard +
  file-naming bound, as W4a.2 states them), C3 `walReadCut_compacts`/`walReadR_compacts`, C4 in full
  (`walNoDormant`); A6 restated if `walReleasePos`/`walRelGuard` change; then plan step 6 (full checks,
  decisions.md "WAL W4b", STATUS, CP3).

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
