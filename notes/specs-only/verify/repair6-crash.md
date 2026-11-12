# Repair 6: the third crash-story pass (F2-crash N1-N3, s1, s3)

2026-11-09. Inputs:
- `verify/F2-crash.md` (N1-N3, second tier s1 and s3);
- the current design in `repair5-crash.md` and `repair4-raft-crash.md`;
- the Go: `.lake/src/server` (`storage/wal/wal.go`, `util.go`; `etcdserver/bootstrap.go`;
  `storage/backend.go`; `etcdserver/api/snap/db.go`); `client/pkg/v3/fileutil` from the module cache
  (`a4d2bb17`).

The criterion for every law: true of the Go and of OsFs, realizable, sound at `L' = L`, and
one-shot per file where it takes `crashRest`.

## N1: the install's rename crashes as one. Fixed.

**The finding.** A rename of `<sd>/<i>.snap.db` onto `<sd>/db` had two independent crash outcomes:
- the directory's `snapDbs_crash` could choose the source gone;
- 4a's `beFile_crash`/`beCrash` could choose a previous file.

Together they gave "old backend back, source gone". No disk reaches that state, and Go's restart
panics on it (`bootstrap.go:481-482`).

**The fix: one new record, and the directory's crash laws resolve the rename.**
- **New (snap, trusted): `Snap.snapRen sd r`**, exclusive and timeless, with
  `r : Option (Nat × GoString)`. It is the newest rename of a db file of `sd`, as its index and
  destination. Laws: `snapRen_timeless`, `snapRen_excl`.
  - It is client-owned beside `snapGone`, in the snapshot directory's invariant.
  - It is allocated at `none`, and every next generation gets it at `none`.
  - `dbFile_rename`'s update sets it to `some (i, dst)` at a rename. The `none` arm (no file)
    leaves it unchanged.
- **New transparent helpers.**
  - `renRevs r os`: the destination's revert list, `Backend.beRevs dst os`, or `emp` when no rename
    is recorded.
  - `renCrashed r F' os os'`: the rename's fate. Either it is **kept**, and the list becomes `[]`
    (`os' = []`), or it is **lost**, and the list is unchanged with the source back
    (`os' = os ∧ F' i ≠ none`). With no rename recorded, the list is untouched.
- **`snapDbs_crash` and `snapSaving_crash`** also take `snapRen sd r ∗ renRevs r os`. Their outputs:
  - `snapCrashed …` together with `renCrashed r F' os os'`;
  - at `L'`: `snapDbs`, `snapGone` and `snapRen … none`;
  - **`renRevs r os'` at the crashed generation.** The frame applies these laws after
    `beDetached_crash` and before 4a's `beFile_crash`/`beCrash`, which take that list. Their
    statements are unchanged.
  - The mask is now `|={⊤}=>`, because 4a's revert record is in `Backend.beFileN`.
- **`OpenSnapshotBackend.spec`'s update** threads `snapRen` in the same way.

**Why I resolve only the newest rename.**
- An older rename's destination was replaced by a later rename, so no restart depends on whether
  its source is back. Installs come in increasing index order, and the WAL's newest snapshot record
  is at or above the newest install's index.
- `snapGone` already says such a source may be back.
- The lost case states `F' i ≠ none`, not `F' i = some img`. A concurrent `SaveDBFrom` at the same
  index can put a new image there, and every image in `snapGone`, or saved, is certified for `i`.

**Why it is true.**
- A rename within one directory is one metadata operation, and ext4 and xfs commit it in one journal
  transaction. That is the physical premise, stated in the header. POSIX does not promise that
  `rename` is atomic across a crash.
- If the rename is kept, the destination cannot return to an earlier file, because the rename is
  that entry's newest change. Nothing else changes `db` after an install: `bolt.Open` creates it
  only when it is absent, and defrag keeps the image.
- If the rename is lost, its source is back.

**Why a stale record is harmless.** A record is stale once a `SaveDBFrom` has synced the directory.
- The rename is then durable, so the realization takes the kept case, which is true.
- After that sync the list holds only entries that cannot come back, such as a detached file closed
  after the sync.
- So no reset is needed at `SaveDBFrom`, and neither it nor rafthttp's `saveOk` changes.

**Realization.** The trusted meaning of `snapDbs`/`snapRen`, with 4a's revert record. Over OsFs, it
is the recorded `rename` gap, which now also needs a crash case that is atomic over both entries.

**Checked against the criterion.**
- *Satisfiable.* The kept case is always available, so the law cannot give `False`.
- *Sound at `L' = L`.* Each resource is consumed once and given back once. The update
  `beRevertL → beNoRevert` is a conversion, not a copy. A second application finds `r = none`.
- *One-shot per file.* No `crashRest` is involved.
- *Lost case.* `F' i ≠ none` is consistent with `snapCrashed`, because `dbFile_rename` records the
  removal in `H` (`goneAdd`) whenever it sets the record.

**`repair2-crash.md` decision 7's claim corrected.** The claim was that the model "may fail a
restart Go completes". In fact Go panics there. No Lean or snippet text repeated that sentence. The
one spec text that described the two laws as independent is `snap/Api.lean`'s "Crashes". It now has
a paragraph, "The install's rename crashes as one", which states the correction. The same
correction is in:
- `ApiBoot.lean`'s crossing paragraph and `disk_crash`'s Changes;
- `Durable.lean`'s "Unsynced renames" bullet;
- the Changes of `applySnapshot.lean` and `OpenSnapshotBackend.lean`;
- `bootstrap.lean`'s crash text and its allocation of `snapRen`.

The working copy's `open-questions.md` D23 still repeats the claim. I did not edit it (see the
requests).

**Files:**
- `SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Api.lean`
- `SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/OpenSnapshotBackend.lean`
- `SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/backend/Durable.lean` (text)
- `SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/ApiBoot.lean` (text)
- `SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrap.lean` (text)
- `SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__applySnapshot.lean` (text)
- `examples/specreq/etcdserverboot/boot.go` (`ReqCrashRecover`'s Specs line)

## N2: `wal.Create`'s window. Fixed.

**The Go.** `wal.Create` writes `wd.tmp`. `SaveSnapshot` fsyncs its file. Then `renameWAL` runs
(`wal.go:185`), and the parent is fsynced only afterwards (`:225`). A crash between the two may keep
the rename or lose it. When it is lost, `wd` is absent, or has no `.wal` files, which `wal.Exist`
reads as no WAL. The next `Create` removes the leftover `wd.tmp`.

**New (WAL, trusted).**
- **`Wal.walCreating wd md`**, exclusive and timeless: the window between the rename and the fsync.
- Laws:
  - `walCreating_timeless`;
  - `walCreating_excl`: with itself, with `walRecs` and with `walWriting`;
  - **`walCreating_crash`**: `walCreating wd md ∗ crashed ⊢ |==> walRecs@L' wd (Recs.init md) ∨ emp`,
    under `diskOk`.
- The law has no `crashInScope` premise, because `Recs.init md` meets `crashScopeOk`: no entries,
  and the zero record is at commit 0. Taking it would be an unneeded premise.
- The header has a new paragraph, "A crash inside `wal.Create`", that says why the law is true.

**The two texts now agree: the kind moves at the parent's fsync.**
- Before the rename there is no WAL.
- Between the rename and the fsync, `diskState(.boot/.join)` holds `walCreating`. The trusted
  `bootstrap` fires the disk's access at the rename and again at the fsync.
- After the fsync, the kind is `.member id` with `walRecs wd (Recs.init md)`.
- After a crash in that window, the kind is `k' = .member id` or `k = k'`. `disk_crash`'s post
  already admits both.
- Where the texts were:
  - `ApiBoot.lean`: the realization bullets for `.boot`/`.join`, and the "kind changes" sentence,
    which said the kind was unchanged before the fsync and admitted no WAL;
  - `bootstrap.lean`: the `wal.Create` item, which said the kind moved at the rename.
- `bootstrap.lean`'s WAL path now also covers a WAL at `Recs.init`: snapshot record 0, no entries,
  the backend at index 0, and `RestartNode` from an empty storage.
- `disk_crash`'s statement is unchanged. A Changes line is added.

**Not filed: F2's liveness observation.** A one-member cluster that crashes between `Create`'s
rename and its first `Save` restarts with an empty configuration and never campaigns. That is
liveness only. It is noted in `bootstrap.lean`'s text ("the configuration the backend holds"), not
filed, since the coordinator did not ask for it.

## N3: the `member/` directory. Recorded, specs not changed.

- **Verified in the module cache.** `fileutil.TouchDirAll` (`client/pkg/v3/fileutil/fileutil.go:49-68`)
  is `MkdirAll` plus `IsDirWriteable`, which writes and removes `.touch`. It does no fsync.
- **The server's directory fsyncs** are:
  - `wal.Create`'s fsync of `member/` (`wal.go:202,225`). It makes `member/wal` and `member/snap`
    durable inside `member/`, but it does not make `member/` durable in the data directory;
  - the WAL directory's, at a segment cut (`:879`);
  - `SaveDBFrom`'s (`snap/db.go:126-131`).
- **Filed** as `nonissues/etcd-member-dir-not-synced.md`, with `blocks-proof: yes` pending D7.
  - Its consequence under POSIX: a crash loses `member/`. A one-member `new` cluster then silently
    restarts empty. A member of a larger cluster fails with "member has already been bootstrapped"
    (`bootstrap.go:385`).
  - Its Notes add the same gap for the WAL's first segment: `wal/`'s entries are fsynced only at the
    first cut.
- **Corrected** `nonissues/bbolt-create-dir-not-synced.md`: `TouchDirAll` syncs nothing.
- **`open-questions.md` D7** has a new paragraph:
  - option (c) alone is insufficient: it would also need fsyncs of the data directory, of its
    parent, and of the WAL directory after `Create`;
  - option (a), stated for directory entries in general ("an entry on the path of a file is durable
    once that file is fsynced"), settles both cases.
- `etc/issues-status.py --index`, then `--check`: pass.

## Item 4: the Perennial entry and K6

- **`notes/perennial-changes.md`** has a new entry, "No WP step lemma refutes the generation's
  `crashed`" (s1). It sits after the crash-aware invariant entry, in the same format as its
  neighbours.
  - The gap: `notCrashed` is in the state interpretation (`Lifting.lean:752`), and
    `notCrashed_crashed` exists (`CrashToken.lean:50`), but no lemma hands it to a WP step.
  - Who needs it: the `token ∨ crashed` realizations, which are raft's starts and `NewServer`.
  - The proposed lemma: `wp_crashed_elim`, plus an atomic-step form.
- **`top.md` K6.** Only the "Pending the user" sentence was edited. It now also names:
  - `member/` under the same model, which only a premise over directory entries in general settles
    (D7);
  - raft's `raftState_crash`, which is not realizable until `readyBatch` exists (D6).

## Requests

### To the coordinator

- **`open-questions.md` D23** ("the model may fail a restart Go completes"): replace it with "**The
  rename's joint crash: fixed** (third crash pass, F2-crash N1, `repair6-crash.md`): the claim was
  false, since Go panics at `bootstrap.go:481-482` there. New `Snap.snapRen sd r`, the newest
  install's rename record, which `dbFile_rename`/`OpenSnapshotBackend` set. `snapDbs_crash` and
  `snapSaving_crash` take it with the destination's revert list, and give it back resolved: kept
  (`[]`) or lost (the source back), before 4a's laws." Also add New decision 1 below as a D entry.
- **K6.** Beyond the sentence I edited, the list of laws the frame applies could name
  `Wal.walCreating_crash` and the snapshotter laws' new role (applied before 4a's). The current text
  ("the snapshotter's laws and 4a's") is not wrong, so I left it.

## New decisions

1. **A trusted rename record, `Snap.snapRen`, and the joint fate of the install's rename** (N1).
   - It is new client-visible vocabulary in the snapshotter's trusted API.
   - The directory's crash laws now also take, and give back, 4a's revert list. A trusted law of
     the snapshotter thus updates 4a's ghost record at the crashed generation, as
     `beDetached_crash` does with its own.
   - Physical premise: a rename within one directory is atomic across a crash (ext4, xfs).
   - Alternative rejected: changing 4a's revert entries to carry their source. 4a cannot name the
     snapshotter's vocabulary, so the joint law would still have to live in snap. The list order
     also does not follow the order of the operations: two detached closes can arrive in either
     order.
   - Alternative rejected: one joint law per combination of forms. That would be four laws
     ({`snapDbs`, `snapSaving`} × {closed, open}), each duplicating 4a's outcome.
2. **`Wal.walCreating` and its crash law** (N2). This is new trusted WAL vocabulary. The kind now
   moves at `wal.Create`'s parent fsync, not at its rename.
3. **N3 widens D7** (above). The recommendation in `repair5-crash.md` (option (c)) does not suffice.
   Option (a), stated over directory entries in general, is the consistent choice.

## Build

- Changed modules (`wal/Api`, `snap/Api`, `OpenSnapshotBackend`, `Durable`): **OK (4 modules)**.
- Every `Spec` importer of every changed file (`etc/importers.py --leaves --git HEAD`, its `Spec`
  leaves, 485 modules): **OK (485 modules)**, `Build completed successfully (2952 jobs)`, no errors.
- Snippets: `go vet ./specreq/etcdserverboot/` is clean, and `gofmt -l specreq/` is empty.
