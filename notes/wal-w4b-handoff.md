# WAL W4b: handoff

Branch `wal-w4b`, worktree `/shared/etcd-grove-walw3`, cut from lean `491baacae1` (W4a landed;
`wal-w4` deleted). Coordinator: etcd-grove-81. Scratch: `/shared/tmp/wal-spec/w4b/`.

## State (2026-11-12, first agent; handoff at about 2/3 of its context)

- Plan approved (etcd-grove-81; `/shared/tmp/wal-spec/w4b/plan.md`). Its findings F-W4b-1/2 are fixed
  in W4a.1 (branch `wal-w4a1`, `91e927b08f` + `58817cfeaa`, under the delta Freeze review; see
  `notes/wal-w4a1-handoff.md` on that branch). Part B's `walDiskM` views (B1) wait for W4a.1 to land.
- This worktree serves both branches: switching only rebuilds `WalDisk.lean` and four axiom files.
- Part A in `Proof/go_etcd_io/etcd/server/v3/storage/WalHistLemmas.lean` (checked with
  `etc/lean-check.py -a`, 0 errors):
  - A1 done: `getElem?_some_lt`, `walImg_refl`, `walImg_mono`, `walImg_length_le`, `walImg_snoc`,
    `walImg_full`, `walImg_prefix`, `walImg_trans`.
  - A2 done: `walHsStep`, `walLastHS_eq`, `walSaveSnap_hs`, `walFoldChkFrom_hs`, `walHsStep_filter`,
    `walReadCut_hs`.
  - A4 first half done: `walEntsWf`, `readEnt_wf`, `readEnts_wf`, `walSaveSnap_wf`,
    `walFoldChkFrom_wf`, `walReadCut_wf` (no premise).
  - A3 `walReadCut_base`: stated, `sorry` (the only one).

## Next, in order (to checkpoint 1)

1. A3 `walReadCut_base` (plan §2 A3): newest-pair lemmas (`walNewestPair_mem/_max/_last`),
   `walNewest_eq_newestPair` (the filtered rest's `walNewest` vs `walNewestPair (walValidSnaps I k)`
   for `k ≥ 1`), then the fold keeps the running maximum (`k = 0`: start `walFresh` at `(0,0)`, which
   is `walValidSnaps`'s head). Watch: `walSaveSnap` resets base at `idx ≥ b` (equal indexes too: the
   last of equal wins, as `walNewestPair`'s `≤`).
2. A4 second half: `walIdxLe B I` (every entry/snapshot index of `I` at most `B`) and
   `walReadCut_last_le` (`σ.last ≤ B`), from `walReadCut_wf` plus "entries come from `I`" (A5).
3. A5 `walReadCut_ents_sub`; A6 `walLastSnapPos_snoc`, `walLastSnapPos_img`,
   `walReleasePos_le_length`, `walRelGuard_snoc`; A1's `walImg_map` / `walImg_toM_iff`.
4. Remove the draft header line ("DRAFT (unchecked)") from the module docstring; targeted build
   (`lake build Proof.go_etcd_io.etcd.server.v3.storage.WalHistLemmas`); CP1 report.

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
