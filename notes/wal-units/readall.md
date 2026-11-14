# WAL unit `readall`: the read and repair paths' `sorry`s

Branch `wal-c-readall` (from `wal-int` `8fdd224baa`), 2026-11-14.

## Finding: nothing left to prove; `notes/wal-fsext-w4c-plan.md` §5 is stale here

Every `sorry` this unit was given had already been discharged on `wal-int` before the branch was cut:

- `WAL.ReadAll.wp_proof`'s EOF stop (`S/WAL__ReadAll.lean`): proved (`ReadAllEnd`, `ReadAllExit`,
  `4e8e554732`, `5d2c9fb51b`); the `wal-fsext` collection dropped its `sorry` in `513d89f455`.
- `S/Repair.lean:411` (the `io.ErrUnexpectedEOF` arm reached at the frames' end): proved in `a41c93d9e8`.
- `S/RepairLoop.lean:65` (`errUeAns_end`): proved in `a9f1b980fc` (the decoder's `decUe`/`errIsTerm`).

`S/` = `LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/`. A token scan of `LinuxFs/{Proof,Spec}` finds
`sorry` in code only at `S/Create.lean:145,157,191` (`wal.Create.wp_proof`'s cleanup arms: another unit,
blocked by design, W4 log). `etc/tcb-collections/wal-fsext.txt`'s baseline agrees: its only `sorry` is
`wal.Create.wp_proof`.

The files the task said `git grep sorry` still finds mention it only in comments, none in code:

| File | Mention | Reached by `Link.lean`? |
| --- | --- | --- |
| `S/TailWriter.lean` | "no `sorry`" in the module comment | yes (`wal.tailWriter`, `wp_tailWrite`) |
| `S/WAL__cut.lean` | "**Proved** (no `sorry`)" | yes |
| `S/WAL__renameWAL.lean` | "No `sorry`" | yes |
| `S/InvOpenTest.lean` | "No `sorry`; nothing imports this module" | no: a test module (the W1 fifth session's `walInv`-inside-an-`os`-update test), imported by nothing; left in place (no `sorry`, so nothing to prove or delete) |
| `LinuxFs/Proof/os/File__TruncateAu.lean` | "no `sorry`" | yes (through `Repair`'s truncate) |
| `S/Create.lean` | real `sorry`s (above) | yes; not this unit |

## The §5 hypotheses in this area

All already closed on `wal-int`; nothing to merge:

- `wal.validSnapshotEntries{Absent,Pinned}`: proved (`S/validSnapshotEntries.lean`,
  `S/validSnapshotEntriesPinned.lean`) and linked without hypothesis (`Link.lean`'s
  `wp_validSnapshotEntriesAbsent`, `wp_validSnapshotEntriesPinned`).
- `fileutil.CheckDirPermission`: `origin/wal-leaf5-modeperm` is already an ancestor of `wal-int`; the proof
  (`LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/CheckDirPermission.lean`) is linked
  (`Link.lean`'s `wp_CheckDirPermission`).

So of §5's "the WAL's own" list only `WAL.renameWALUnlock.spec` (false as stated, ledger; `Create`'s unit)
remains as a hypothesis of the Link.

## Changes

Comments only (no statement, proof, axiom or hypothesis changed): the stale "`sorry`" remarks in the module
comments of `S/WAL__ReadAll.lean`, `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/OpenForRead.lean` and
`.../openAtIndex.lean` (both proofs exist with no `sorry`) now say proved.

## For the coordinator

- Update `notes/wal-fsext-w4c-plan.md` §5: the `sorry` line keeps only `wal.Create.wp_proof`; the WAL's own
  list keeps only `WAL.renameWALUnlock.spec`.
- No decision for the user, no new hypothesis, no Go bug.
