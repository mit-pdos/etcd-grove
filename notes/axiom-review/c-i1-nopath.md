# C-I1 without the path: `dbCrashKeep` restated for T10 (`Proof/go_etcd_io/etcd/server/v3/storage/backend/CrashInterim.lean`)

Review 2026-11-25, `axiom` skill, task T10 of #50 (branch `etcd-safe-t10` @ `3dea0aa4be`), before the restatement
goes to the owner. Earlier reviews of C-I1: [c-i1-bbolt-crash](c-i1-bbolt-crash.md) (six rounds).

## What is reviewed

The restatement proposed in `notes/etcd-dist-d6.md`, "T10 design" §1 (the C-I1 row of its table), with its use in
the draft `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/crash/BackendImage.lean` (`kbSync.law`'s
derived resync):

| law | at `3dea0aa4be` | restated |
|---|---|---|
| `dbCrashKeep` | `γ path i0 Dl Dn pd`, holds `bPath γ path` and `dbHalf γ Dn` | `γ i0 Dl Dn pd`, holds `dbHalf γ Dn` only |
| `dbCrashKeep_new` | consumes `dbOpts γ`, `boltIno γ i0`, `bPath γ path`, `dbHalf γ D`, a live writer at `wr D` | the same without `bPath` |
| `dbCrashKeep_close` | gives back `bPath γ path ∗ dbHalf γ Dn` and the writer | gives back `dbHalf γ Dn` and the writer |
| `_announce`, `_half`, `_clear`, `dbCrash` | | unchanged but for the dropped argument |
| resync (`kbSync.law`'s step) | | derived: `_clear; _close; _new`, holding the fresh writer at `Dn` (`t.tx = begin(true)` after a returned commit) |

The exact restated statements (to apply when the owner approves; nothing applied here):

```lean
opaque dbCrashKeep [hG : HeapGS hlc GF] (γ : DBNames) (i0 : Fs.Ino) (Dl Dn : Data)
    (pd : Option Data) : IProp GF := iprop(False)

axiom dbCrashKeep_new … (γ : DBNames) (i0 : Fs.Ino) (D : Data) (tx : Loc) :
    ⊢ dbOpts γ -∗ onFs iprop(bbolt.boltIno γ i0) -∗ dbHalf γ D -∗ txLive tx γ 1 (bbolt.TxView.wr D) ==∗
      dbCrashKeep γ i0 D D none ∗ txLive tx γ 1 (bbolt.TxView.wr D)

axiom dbCrashKeep_close … (γ : DBNames) (i0 : Fs.Ino) (Dl Dn S : Data) (G : GoString → Nat) (tx : Loc) :
    dbCrashKeep γ i0 Dl Dn none ∗ txLive tx γ 1 (wView Dn S G) ⊢
      dbHalf γ Dn ∗ txLive tx γ 1 (wView Dn S G)
```

and `path` dropped from `_announce`, `_half`, `_clear`, `dbCrash` (whose conclusion was already about the inode
`i0` alone, under `Named V'.now i0`).

## Verdict: **survives** (sound as restated), with docstring fixes

No panicking program and no false instance found. Dropping the name is a strengthening of `_new` (one premise
fewer) and a weakening of `_close` (less given back); the latter is trivially sound, and `_new`'s truth never
depended on the name: its argument (a live writer at fraction 1 excludes a commit in flight, the last commit of
this opening returned after both syncs under `FsNoErrAll`, `Open`'s own `fdatasync` at `db.go:326` covers an
earlier `NoSync` opening) is about the inode `boltIno γ i0`, which a rename does not change. `dbCrash` already
asked its caller for the name (`Named V'.now i0`) and concludes `fileHoldsM i0 D'` of the inode, so the record's
claim on a name was never part of what it asserts. The resync `_clear; _close; _new` is then a sequence of true
laws: holding the fresh writer at `Dn` after a returned commit, the file of `i0` is `Dn` on disk.

## Attacks tried

1. **Two records for one database (the role `bPath` played).** Reviews 1 and 4 cited `bPath` as what blocked a
   second record. Without it, a second record of `γ` needs a second `dbHalf γ D`: the only other half of
   `boltState γ 1` is `ownDB`'s (`InvBbolt.lean`, exposed to the backend's own proofs), so at most two records
   exist, each holding a half. Then every commit needs both halves (`Tx.Commit.spec`'s update takes
   `boltState γ 1`), so both records' `_half` are opened around the one commit point (nested `={E}=∗` steps: no
   other route to the halves), each requiring the new data be announced on it (`S = Dn ∨ pd = some S`), and both
   move to `(Dn, S, none)`: two accurate records. `dbCrash` consumes `i0` from the crash rest (`i0 ∉ Dx`), so only
   one of them is ever used. A half cannot be lent across threads (`_half` returns it in the same update).
   **Blocked** by the halves, not by the name.
2. **Two databases on one inode** (a record of `γ1` while `γ2` writes `i0`). A second `Open` of `i0` needs
   `fileHoldsM i0 _`, which holds `osMeta i0 (own 1)` and all of `i0`'s bytes (`FileImg.lean:162`), inside `γ1`'s
   `isBolt` while it is open; `DB.Close.spec` needs `boltState γ1 1`, so every record of `γ1` is closed first, and
   no record of `γ1` can be made after `Close` (`_new` needs `dbHalf γ1`, which `Close` consumed). In Go the
   second `Open` of an inode open elsewhere blocks on `flock` (a deadlock, not a panic). Renaming `db` away and
   opening the inode by its new name meets the same `fileHoldsM`. **Blocked.**
3. **`fileHoldsM` on the wrong inode** (a proof claiming the data for a file a rename replaced). `dbCrash` gives
   `fileHoldsM i0 D'` and takes `i0` out of the crash rest; to say what the *name* `db` holds, the caller joins it
   with a name claim whose entry is `i0` (`fileAtF`'s one `∃ i`, `bPath_join`'s `boltIno_agree`), which the file
   extension's crash facts give only when the durable tree names `i0` there. After the snapshot install's rename
   and its directory sync (`renamedDur`), no crash's durable tree names the old inode, so `Named V'.now iOld` is
   unprovable and the old record is unusable; it stays harmlessly in the old backend's commit invariant until
   `Close`. **Blocked** by `Named` and the inode-indexed conclusion.
4. **An unlinked, still-committing old file.** After `os.Rename(snap.db, db)` the old backend keeps committing to
   `iOld` (its timer, `CommitAndStop` in `oldbe.Close()`): its record follows, true of `iOld`'s bytes whether or
   not a name survives. Real ext4 makes the rename and `iOld`'s orphaning one journal handle (`ext4_rename`), so a
   recovered tree either names `iOld` as `db` (and `snap.db` names `iNew` again), or names `iNew` as `db` with
   `iOld` deleted by orphan cleanup; never `db` naming a half-deleted `iOld`. **Measured on C** (below).
5. **Crashes in the rename window before the directory sync.** The model leaves either entry (only `DirSync`
   commits a name; on Linux an `fsync` of either file can also commit the rename's journal transaction, which the
   model allows as one of its outcomes). The restated laws take no position on the name, so both outcomes are
   covered by `Named`. **Measured on C** (below).
6. **`_new` on a file renamed after its open** (record made on `iOld` after it lost `db`, from the resync). True:
   the resync's premise is a fresh writer at `Dn` of `γ`, and the disk of `boltIno γ` is `Dn` regardless of names.
7. **Inode reuse across the restatement.** Unchanged from review 4: the model's `nextIno` only grows within a
   generation and records are of one generation (`dbCrash` consumes them with `crashed`).

## Measured on configuration C (2026-11-25)

`c-i1-nopath/` (`main.go`, the Go module `renamewindow` with bbolt at the pin `ca88bb6a`, Go 1.27.3;
`rename-window.sh`, the method of `fs-config/trunc-size.sh`: `dmsetup suspend --nolockfs` at a random moment, the
image and the step log copied, each image recovered by a kernel mount and checked). Each run: `DIR/db` (bbolt)
opened and committing `n = 1, 2, …` with filler values (so the file grows: `DB.grow`'s truncate and sync); a synced
bbolt `DIR/snap.db` renamed onto `DIR/db` after 0-200 ms; the directory synced 200-1500 ms later. The check: before
`RENAMED` `db` is the old file, after `DIRSYNC` the new one, in between either, with `snap.db` present exactly
when `db` is the old file; the file `db` names holds the last returned commit, the one before it, or the
announced one (the restated `dbCrash`'s set). Run on fk-lean2 (Linux 7.0.0-1017-aws, `check.sh`: C).

| series | crashes | before the rename | in the window: `db` old / new | after the directory sync | BAD |
|---|---|---|---|---|---|
| 1: new file opened and committing right after the rename (not the fork's order), default `commit=5` | 40 | 4 | 1 / 23 | 12 | 0 |
| 1': the same, `commit=1` | 40 | 1 | 0 / 28 | 11 | 0 |
| 2: the fork's order (`RW_FORK=1`: rename, directory sync, then open), default `commit=5` | 60 | 7 | 1 / 46 | 6 | 0 |

Every recovered `db` held a value in the restated set (in practice the last returned commit or the announced
one, never the fallback: the synced commit is on disk). In the window the rename was usually already durable
(`db` the new file, the old inode deleted by orphan cleanup), although no directory sync had run: an
`fsync`/`fdatasync` of either file (the old file's commits, up to 287 of them after the rename; `DB.grow`'s
`fsync`) commits the running journal transaction, which holds the rename. Series 2, crash 52: the rename lost
after 5 commits of the old file returned past it: `db` the old inode at `n = 33` (last returned 33, announced
34), `snap.db` back: the case the old record covers. No recovered image named a half-deleted file or lost both
names. Outputs: `c-i1-nopath/results-2026-11-25.txt`.

## What the design should say (not soundness)

- The fork's `OpenSnapshotBackend` (e94f33b50, `server/storage/backend.go`) syncs the directory **before** it
  opens the new file (`syncDir` then `OpenBackend`). So in the install window only the old backend has a record;
  the new record (`_new` at its open) exists only once the rename is durable. The design's "the keep is a
  disjunction over two records" inside the window is one record and the received file still in `snapHeld`
  (`fileAt … Ds`): simpler than drafted, and it makes "if the rename did not survive, the file is back under its
  name holding `Ds`" true (nothing has committed to `iNew` yet).
- Docstrings to update with the restatement: `CrashInterim.lean`'s header (the record "holds the claim on the
  name (`bPath γ path`)", and "The name" bullet's "The record holds `bPath`, so a rename onto `path` closes it
  first"), `dbCrashKeep`'s ("whose file is at `path`"), `_close`'s ("the claim on the name and the half back …
  or to rename another file onto `path`"), and `memberDbNamed.law`'s in `dist/crash/MemberCrash.lean` ("The
  backend's record `dbCrashKeep` holds the claim on `db` (`bPath`), so no `nameCrash` can be kept beside it": with
  the restatement the name's crash promise can be kept beside the record, as the design intends).
- Not changed by this review and still open from review 3: `fileHoldsM`'s receipt of the in-flight txid.

## Not tried

A Lean counterexample (none was in reach: every attack above is blocked by a resource, not by an argument); a
power loss inside `oldbe.Close()`'s `CommitAndStop` (the same commit path as the measured timer commits); xfs or
other configurations (outside C).
