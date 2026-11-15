# Unit `synclent`: `WAL.sync.specLentE` (branch `wal-c-synclent`, base `origin/wal-int`)

Plan: `notes/wal-units/closefailed.md` ("Left"), the W4c U5 log's fifth session ("E6", `syncLayP`).

## Session 1 (2026-11-15; base `origin/wal-int` at `dbd4495eb5`)

**The design.** The tail `ZeroToEnd` left (`walTailPE`: lent by the token of kind `false`, `TailMetaE`: the
length word at `wr = o0` zero, nothing known of the bytes past it; a resize window maybe open, no resize in
flight: the record's `none`) has F-Z or `TailPend` (`walLentRes_lookup`). Its fdatasync:

- with F-Z: `syncLay_any`'s layout (`WinZero` from `TailLast.winZero`/`WalAbsD.winZero`);
- with `TailPend` and no F-Z (a torn frame past `wr`): the new layout **`syncLayP`** (`syncLay` with `old` the
  synced values from `wr` on, `old`'s below, zero-padded): exact, every byte durable, `TailPend` again (the
  length word at `wr`, from the handle's bytes). No `WinZero` and no F-Z, so the token cannot turn into the key
  (`walLentRes_unpend` needs F-Z): it **stays lent**, and since `syncLayP`'s `old` has the synced tail's length
  (`LentOk` records `|old|`), the token's `k` is replaced (`walLentRes_relend`). `Close` then puts the tail back
  by the token (`walInvBody_untailL`, `p = false`), as planned.

**Proved** (no new axiom, no `sorry`, nothing trusted changed, no Go changed):

- `TailSyncLayP.lean` (pure): `syncLayP`, `walAbsD_syncP` (the static relation at the raised mark; `tailStop` by
  `decStep_zeroWord`), `tailPend_syncP`, `tailBound_syncP`, **`crashOk_syncP`** (the crash condition at the raised
  mark: `crashOkA_tailPend`'s proof, the old condition at the old mark with the tail imaged as of its last sync,
  then `crashTo_tailP` over `walAbsD_syncP` with the input mark `d.m`; no generalization of `crashTo_tailP`
  needed: its input `CrashTo {d' with m := d.m}` is the old one), `walsOk_syncP`, `dirKeysOk_syncP`,
  `syncLay_anyE` (either case, F-Z or `TailPend` out).
- `TailSyncPendE.lean`: `walLentRes_relend`, `walTailsRes_cutPE` (`walTailsRes_cutP`, the token kept),
  **`walInvBody_syncPE`** (the invariant step: `walInvBody_syncP` from the handle's zero length word in place of
  its zeros from `wr` on; success: the invariant at `walSyncS`, `walPast`, the token with some `k'`),
  `walInv_untailLent`.
- `FdatasyncLentE.lean`: `wp_tailFsyncPE`, `syscall.Fdatasync.wp_tailPE`, **`Fdatasync.wp_specWalLentE`**
  (new spec file `Spec/…/wal/FdatasyncLentE.lean`, `Fdatasync.specWalLentE`).
- `WAL__syncLentE.lean`: **`WAL.sync.wp_proofLentE`** (`WAL.sync.specLentE`, statement unchanged).

**Linked**: see "Build" below.

**Statement changes**: none (the client-facing specs unchanged; `WAL.sync.specLentE` as stated by `closefailed`).

**Decisions for the user**: none.
