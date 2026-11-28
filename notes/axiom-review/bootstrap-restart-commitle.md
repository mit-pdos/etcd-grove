# `bootstrapRestartContract` and `walFiles`: a commit above the last index (C1)

Date: 2026-11-28. Session WCL-1 (coordinator etcd-grove-03), on the etcd_safe lead's finding C1 (#50,
2026-11-28 05:02Z). Follows [bootstrap-restart-eagerfold](bootstrap-restart-eagerfold.md).

## The premise

`bootstrapRestartContract` (`InvRestart.lean`), a premise of `etcd_robust_single_process`, takes the stopped
member's files `srvFiles`, whose WAL part is `walFiles a id cid σ true` (`WalRecs.lean`), and promises
`wal.restartOk`'s `walRecs h σ`: the history's eager fold (`walFoldChkFrom walFresh`) is `σ`. After
walfiles-fold (`c4b79f5406`) `walFiles` states both `walRead H = some σ` and the eager fold `= some σ`, and
the restart contract's post is read with `σ` as the records a `ReadAll` returns.

## The gap

`walFiles` still admitted histories whose real `ReadAll` returns other entries than `σ`. Minimal case
(`examples/axiomcx/restartcommitle`, run at the etcd pin `d26dd5da6f`):

```
Save(hs{Term 1, Commit 1}, entries 1..6)
SaveSnapshot(3)           -- above the commit 1: the eager fold's records become base 3, no entries
Save(hs{Term 1, Commit 4}, [])   -- commit 4 above the fold's last index 3
SaveSnapshot(4)           -- base 4, no entries
Close
```

The model (both `walRead` and the eager fold) has no entries; `ValidSnapshotEntries` keeps the record at 4,
and `Open(4)` + `ReadAll` returns `err = nil`, commit 4, entries `[5 6]`:

```
=== RUN   TestCommitAboveLast
    restartcommitle_test.go:84: newest valid snapshot 4; ReadAll err=nil commit 4 entries [5 6]; the eager fold has base 4 and no entries
--- PASS: TestCommitAboveLast (0.04s)
```

The lead's random runs: in 100k random histories every mismatch had a prefix whose commit was above its
last index; with those excluded, 0 of 7,350 mismatched.

Not a soundness problem of today's theorems: raft's node loop, the only WAL writer, keeps
`committed ≤ lastIndex` (`ReadyRestFacts`: the hard state's commit is within the last index after the
`Ready`'s entries). But no Lean statement recorded it, and `walFiles` (so the restart premise) admitted the
history above.

## The fix (approved: the lead's proposal, #50; WCL-1)

- `walRecs` and `walFiles` gain `walCommitLeFrom walFresh (walSrvHist d.H)`: every prefix of the history's
  eager fold has its commit within its last index (the definition of `WalHistLemmas.lean`, which the crash
  line's `wal.restartOk` also carries, `etcd-safe-crash-delta-now/2026-11-27`).
- `Save`'s law (`isWalStorage`, `walSaveSized_spec`, `walSaveRn_spec`, `rnNewStorageOk`'s `walSave_law`)
  requires `WalSaveCommitLe σ hs es` (`(walSave σ hs es).commit ≤ (walSave σ hs es).last`) beside
  `WalSaveOk`, and `walRecs_saveAU` keeps the conjunct with it (`walCommitLeFrom_snoc`);
  `walRecs_saveSnapAU` keeps it without a premise (`walCommitLeFrom_snoc_snap`), `walRecs_releaseAU`
  changes no history, `walRecs_closeAU` hands it to `walFiles`.
- The node driver supplies it: `WalSaveStep` gains it, `walSaveStep_ready` and `walSnapSteps_ready` prove it
  from `ReadyRestFacts` (`walSaveCommitLe_of_holds`: the saved records hold the durable state after the
  batch, whose last index is at least the commit).

What the restart premise now assumes: `walFiles` is stronger, so `bootstrapRestartContract` (whose pre is
`srvFiles`) promises its post of fewer files: it claims less. `wal.Create.specSrv` (a premise of
`bootstrapNewWAL`) claims the conjunct of the fresh WAL, where it holds (an empty history).

## Handoff WCL-1 (2026-11-28)

Done (branch `walcommitle/2026-11-28`, off lean `2018327946`):
- the predicate: `walRecs`/`walFiles` gain `walCommitLeFrom walFresh (walSrvHist d.H)`; `WalSaveCommitLe σ h es :=
  (walSave σ h es).commit ≤ (walSave σ h es).last` (`WalRecs.lean`) beside `WalSaveOk` in `Save`'s atomic update
  (`WalApi.lean` 4 laws, `RnNewStorage.lean` `walSave_law`, `InvWal.lean` `rnDur_save_au`);
- proofs edited, **not yet compiled**: `walRecs_unsize`, `walRecs_saveAU` (`walCommitLeFrom_snoc`),
  `walRecs_saveSnapAU` (new `walCommitLeFrom_snoc_snap`, `WalLinkPure.lean`), `walRecs_closeAU`; the driver:
  `WalSaveStep` gains the conjunct (second), proved in `walSaveStep_ready`/`walSnapSteps_ready` by the new
  `storageHolds_last_le` and `walSaveCommitLe_of_holds` (`InvWal.lean`) from `ReadyRestFacts`' second conjunct;
  `raftNode__start` needs no edit (it takes `.1` of the step);
- Go: `examples/axiomcx/restartcommitle` passes at the etcd pin (`ReadAll` err=nil, commit 4, entries [5 6]);
- docstrings `walRecs`, `walFiles`, `srvFiles`; ledger entry; README row;
- Perennial e2eda8223 built on fk-lean1 (`/home/ubuntu/eg/perennial-e2eda8223`, `pbuild-e2eda8223.sh`, EXIT 0);
- vocabulary diff (source-level `etc/theorem-tcb.py`, `cmp7.py`'s method; `/shared/tmp/wcl-delta/premdiff-1f0a06f925.txt`):
  changed only `etcd_robust_single_process`, `etcd_leaseexpiryN_robust_single_process`, `k8s_robust_single_process`
  (premise vocabulary: `walRecs` changed, `walCommitLeFrom` added; the first also `srvFiles`/`walFiles`) and
  `etcd_kv_safe_nocrash`, `putget_safe` (axiom vocabulary: `walRecs`, `walFiles`, `srvFiles`, `walCommitLeFrom`;
  `etcd_kv_safe_nocrash` also `isWalStorage`, `WalSaveCommitLe`); every other theorem unchanged. Five names of the
  list gave no TCB on either tree (`crash_robust`, `etcd_robust`, `etcd_robust_nocrash`, `hraft_nocrash_robust`,
  `putgetK_safe`): not compared.

Left: the build (`etc/lean-check.py`/remote `fkcheck.sh` on fk-lean1, the branch's first build seeds from
lean-warm at another pin, so near-full); fix what fails; regenerate/`--check` `etc/copy-part.py`,
`etc/gen-raft-tla.py`, `etc/gen-init.py` (no copies of the edited modules were found); `GATES_FAILFAST=0
etc/gates.sh`; `etc/tcb-report.py --check`; the STATUS entry; the directions below confirmed against the built
statements.

Directions (to confirm): a premise whose pre is `walFiles`/`srvFiles` (`bootstrapRestartContract`) assumes less;
a premise whose post is `walRecs`/`walOpened` (`wal.Create.specSrv`, the restart's post) claims more, the conjunct
holding of the fresh WAL and following from the pre's `walFiles` of the same history; `isWalStorage`'s `Save`
(axiom vocabulary of `etcd_kv_safe_nocrash`) requires more of its caller, so claims less.
