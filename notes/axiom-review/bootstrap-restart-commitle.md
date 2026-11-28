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
