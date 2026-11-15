# Unit `closefailed`: `WAL.Close.specFailed` (branch `wal-c-closefailed`, base `origin/wal-int`)

Plan: `notes/wal-units/locks.md` session 3, item 5; the W4c U5 log's fifth session ("What is left for
`Close.wp_proofFailed`").

## Session 1 (2026-11-15; merged `origin/wal-int` at `718b26cbc5`, purge stage 1)

**Proved** (all `lake build`: the WAL `Link`, the tester's `Link`, `durable`'s `Link` -- see "Build" below):

- **`walReadFailedF`'s real body** (`ReadDefs.lean`, sealed): `walReadFailed w dir ∗ walFailH Mr w dir`, the
  fields `Close` reads (logger, `dir`, locks over `gs0 ++ [gL]`, the pipeline, `unsafeNoSync`, mutex, `dirFile`,
  the call permission's quarter, the claim's half, out record, `walNamesFrag none`, the key, the non-tail segments'
  halves and files) and the tail in one of two forms:
  - `walFailIdle`: unregistered, its halves (`segRes`), file and fd, the encoder nil or an encoder over it with
    nothing pending (`!match`'s);
  - `walFailLent`: registered, `walTailP … k false TailMetaZ` (the fdatasync's error) or `walTailPE`
    (`ZeroToEnd`'s error), the encoder nil, the layout facts for `walCloseLeft` (`CloseLeftOk`).
  It takes the marshaller now (`walReadFailedF Mr w dir`: the lent tail's write position is `tailStream Mr …`).
- **`ReadAll`'s ten error exits** re-proved to give it (`ReadAllFail.lean`):
  - E1-E5 (the loop's four arms, the decoder's error at the mode check): every file's stream
    (`streams_loop`/`streams_loop0`, `decPostB_streams`), the tail unregistered on the spot by its pending token
    (`walInv_untailPend`, over `walInvBody_untailL`, with the registration look's exported `zf ≥ size` and
    durability), `readAll_failPend`;
  - E8, E9, E10 (`Fsync(dirFile)`, `syncDir`, `!match` after `newFileEncoder`): the tail kept as `walTailW …
    TailMetaS` (the `TailMeta` weakening moved into the success branch), unregistered by its key
    (`walInv_untailKey`, over `walInvBody_untail`), `readAll_failSynced`; E10's code runs first, the exit
    lemma just before the unlock;
  - E6, E7: the lent tail kept (`ZeroToEnd`'s error arm's `walTailPE`, the fdatasync's `walTailP`),
    `walReadFailedF_lentIntro`.
  `walInv_readCommitReg` exports `CloseLeftOk X hj lay.segs gl` (from `DirKeysOk`, `SegsNamed`, `WalAbsD`).
- **`WAL.Close.specFailed`** (`WAL.Close.wp_proofFailed`, `WAL__CloseFailed.lean`): the pipeline's `Close`, then
  `w.sync()` by the tail's form, then (but on a lent tail's failed sync) `walInv_unpin` and the lock loop and the
  directory's `Close`, the token and the call permission's half back (the first arm, whatever an idle sync
  answers); a lent tail's failed sync returns `walCloseLeft dir` (the area's path, `walInv_dirPath`; the claim's
  half; the tail's lock, `fdLocksW_held`; the call permission's half).
- **New callee specs of `w.sync()`** (Spec files, one each): `WAL.sync.specIdleF` (proved,
  `WAL__syncIdleF.lean`: `specIdle` with an empty encoder, flushed over a writer accepting only `[]`,
  `encoder.flush.specPNE`), `WAL.sync.specLent` (proved, `WAL__syncLent.lean`: `Fdatasync.specWalPend`, then the
  tail unregistered by its key at the next step), **`WAL.sync.specLentE` (stated, not proved)**: the fdatasync
  of the tail `ZeroToEnd` left unknown (`walTailPE`), then the put-back; it needs the new invariant step
  `syncLayP` (W4c U5 log, fifth session, "E6"), then an `Fdatasync.specWalLentE`, then `walInvBody_untailL`
  (`p = false`).
- **Linked**: `wp_syncIdleF`, `wp_syncLent`, `wp_CloseFailed` (pending on `h_wal_WAL_syncLentE`) in the WAL
  `Link`; the tester's `Link` now uses `wp_CloseFailed` (its hypothesis `h_wal_WAL_CloseFailed` replaced by
  `h_wal_WAL_syncLentE`, 5 results). `durable`'s `Link` unchanged.

**Statement changes** (ledger 2026-11-15, "`WAL.Close.specFailed`'s proof"):
- `walCloseLeft dir` (roots existential; `Close.specFailed`'s post); `CloseLeftOk` without `dir`'s bound
  (moved to `wal.Repair.wp_afterCloseFailed`'s premise `dir.length < 2^59`); `CloseLeftOk` moved to `ReadDefs`.
- `walReadFailedF Mr w dir` (the ReadAll and Close.specFailed statements pass `Mr`).
- `fdLocksW` (a writable description is locked) in `walOpenedFile`, `walOpenedRc`, `walFileS`, `walLastOpen`,
  `walTailP`, `walTailPE`; `walTailP_po` one-directional (unused). `walTieFile`/`walFileAt` moved to `ReadDefs`.
- `walInvBody_readReg`/`walInv_readCommitReg` export `CloseLeftOk` last.

**Left**: `WAL.sync.specLentE` (the `syncLayP` step). No new axiom, no `sorry`, nothing trusted changed, no Go
changed, no Go bug found. `etc/tcb-collections/linuxfs.txt` not rerun (needs a full build of the roots).

**Decisions for the user**: none.
