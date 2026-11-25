# C-I2 case 2: `bootstrapCrashContract.law`'s `.snap.db` recovery (`Proof/go_etcd_io/etcd/server/v3/etcdserver/CrashInterim.lean`)

Review 2026-11-25, `axiom` skill, task T10 of #50 (branch `etcd-safe-t10` @ `392980264e`), a fresh agent given the
law and the fork. Earlier reviews of C-I2 (its first case): [c-i2-bootstrap-crash](c-i2-bootstrap-crash.md).

## What is reviewed

The second conjunct of `bootstrapCrashContract` (`etcdserver/InvCrashImage.lean`), added by T10 (approved by
coordinator-E, #50 2026-11-25T15:22:46Z, item 2), quantified by `bootstrapCrashContract.law` over the deployment's
names (`γ.vs = ps`, ...; the A1 guard of the first review):

* **premises**: `uint.nat i < σ.b`, `uint.nat j = σ.b`, the old backend's stored consistent index
  `dget D meta consistent_index = encMeta i`, `walReadFacts σ`, `γ.cl.bootLen ≤ σ.commit`, the configuration facts of
  the first case, the image of the snapshot's data (`imageRestAt γk γ.boot j Ls Ds`, `imageStOk`, `mvccImage Ds …`),
  the files `srvFilesC cfg.DataDir' id σ D` (the WAL reading back as `σ`, `db` holding `D` or absent with `D = ∅`)
  and `backend.fileAt (snapDBPath (snapDirOf DataDir) j) Ds` (`<j>.snap.db` a bbolt file holding `Ds`);
* **post**: an error, or `bootOkR cfg γ id N dir σ j Ls Ds M b` (the restart at the snapshot's index, over `Ds`).

Go: the fork `upamanyus/etcd` `e94f33b50` (`goose-lean-fmt1c-crashfixes`, `etc/goose.py`'s project `etcd`), paths
below relative to its `server/`. (The law's file header still names `768ecf158`, the torn-`Save` fix alone; the pin
now carries it, `49bf5160f`, with the directory syncs `533e06e9c` and the unsaved-WAL backend removal.)

## Verdict: **sound** (survives)

No execution found in which `bootstrap` panics, gets stuck, or succeeds in a state other than `bootOkR … σ j Ls Ds`
while the premises hold. Every attack is blocked by a premise or by Go's own order; the kernel facts the case relies
on hold on configuration C (two measured, below). One docstring fix (not soundness), and two obligations that belong
to the caller (T10's `snapRowB2`), recorded below.

## Go's path in this case

`bootstrap` (`etcdserver/bootstrap.go:54`): `bootstrapSnapshot` (removes `tmp*`, `db.tmp*`, `*.snap` names only:
`<j>.snap.db` survives), `wal.Exist`, `wal.Unsaved`/`DiscardUnsaved` (a WAL with `bootLen ≤ σ.commit` has a state
record, so it is kept: first review), then `bootstrapBackend` (`:305`):

1. `beExist := Exist(db)`; `OpenBackend` on the old file (`D`; created empty if absent), `ci.SetBackend(old)`,
   `CreateMetaBucket`, `ci.ConsistentIndex()` (caches `i`).
2. `recoverSnapshot` (`:499`): `ValidSnapshotEntries` (snapshot records at or below the last state record's commit,
   `storage/wal/wal.go:921-980`), `newestSnapshotEntry` (highest index, last of equal ones, `:489`): this is `σ.b`
   (`walRead`'s filter `walKeep` and `walSaveSnap`'s max, `storage/WalHist.lean`, `WalRecsCore.lean:35`; `srvFiles`'
   docstring), so Go's snapshot index is `j`.
3. `RecoverSnapshotBackend` (`storage/backend.go:113`): reads `i` from the old backend (`0` if `!beExist`, and then
   `i = 0` by the premise's `encMeta i = none`); `j ≤ i` is false, so `oldbe.Close()` and `OpenSnapshotBackend`
   (`:65`): `DBFilePath(j)` (the name `%016x.snap.db`, `snapDBName`'s `hex16`), `os.Rename(<j>.snap.db, db)`,
   `syncDir(member/snap)`, `OpenBackend` (bbolt open of `Ds`).
4. `ci.SetBackend(new)` resets the cache; with `beExist`, `kvindex = ci.ConsistentIndex()` reads `Ds`'s index, `j`
   by `imageRestAt` (`encMeta j`, `j ≥ 1`), so the `kvindex < j` error is not taken; `schema.Validate` on `Ds`.
5. `bootstrapWALFromSnapshot` opens the WAL at `{j, term}` (a record of `σ`) and `ReadAll`s `σ`'s entries above `j`;
   `Finalize`, `buildConfStateFromV3store(Ds)`, `bootstrapRaftFromWAL`: as in the first case, at `(σ, j, Ds)`.

The `Logger.Panic`s on this path (`bootstrap.go:532`: `RecoverSnapshotBackend`'s error; `backend.New`'s failed
`bolt.Open`) need `<j>.snap.db` missing, a failed rename or directory sync, or an unopenable `Ds`: excluded by
`fileAt` (the name names a file holding a database), the two claims on `db` and `<j>.snap.db` in one directory, and
the file extension's `NoIoErr`/`FsNoErr` premises (the pin branch proved `syncDir` error-free,
`notes/STATUS.md` 2026-11-25).

## Attacks tried

1. **A crash between `SaveSnap` and the rename** (the window the case exists for). The raft loop's order
   (`etcdserver/raft.go:266-296`): `SaveSnap(j)`, `Save(hs, ents)`, `storage.Sync()`, then `notifyc` to the apply
   thread, whose `applySnapshot` renames. Before `Save`'s state record with `commit ≥ j` is durable, `j` is filtered
   out by both Go (`ValidSnapshotEntries`) and the model (`walKeep`), so `σ.b < j` and the image is the first case's
   (or this one at an older received snapshot). After it, `σ.b = j > i` (the old backend applied nothing above its
   index while the apply thread waited on `notifyc`), and `<j>.snap.db` is on disk: `SaveDBFrom` synced the file
   and then the directory before rafthttp handed the message to raft (`snap/db.go:39-87`). **Covered** by the
   premises; the file's presence is the caller's `snapRowB2` (`snapSaved γd j`, below).
2. **A crash after the rename, before the directory sync** (the runtime install, or `bootstrap`'s own step 3). One
   journal transaction renames: either `db` names the old inode and `<j>.snap.db` names `Ds` again (this case again,
   the same `D`: nothing commits to the old file after the apply thread stopped, its timer commits only flush applied
   entries at or below `i`), or `db` names `Ds`'s inode and `<j>.snap.db` is gone (the first case at `i = j = σ.b`:
   the fork opens the new backend only after the sync, so `Ds` is untouched). Measured on C by
   [c-i1-nopath](c-i1-nopath.md) (series 2, the fork's order: 60 power losses, the rename whole or lost, `snap.db`
   present exactly when `db` is the old file). **Covered**; a crash inside `bootstrap`'s own recovery lands in one
   of the two cases (the law itself is a crash-free triple: the crash condition of `bootstrap` is the caller's).
3. **A torn or partial `.snap.db`.** Excluded by the premise (`fileAt`: `fileHoldsM`, a whole database). Whether a
   crash can leave one under the name is the caller's claim; `SaveDBFrom` writes a `tmp*` file, `fsync`s it, then
   `link`s it under `<k>.snap.db` (`snap/db.go:42-87`), so the name exists only after the data is durable.
   **Measured on C** (`c-i2-snapdb/`, below): no recovered name ever held a torn or partial file; a torn
   temporary stays under `tmp*`, which `bootstrapSnapshot` removes.
4. **Several `.snap.db` files.** Go opens exactly `<j>.snap.db` (`DBFilePath(j)`); the others are untouched by
   `bootstrap` (`bootstrapSnapshot` removes names starting `tmp`/`db.tmp` and ending `.snap`, never `.snap.db`).
   A duplicate save of `j` (`SaveDBFrom`'s link refusing an existing name) keeps the first, whole file. **No effect.**
5. **A `.snap.db` older than the WAL's snapshot** (only `<k>.snap.db`, `k < j`, present). Go then panics
   (`DBFilePath` → `ErrNoDBSnapshot` → `Logger.Panic`, `bootstrap.go:532`), but the premise requires `<j>.snap.db`:
   **excluded**. Reachability is the caller's: `nonissues/etcd-purge-snapdb-unopened.md` (the purge removing an
   unopened received file, `blocks-proof: yes`) is exactly the image the law refuses to cover, so `snapRowB2`'s first
   disjunct (`c ≤ σ.b`, the file still in the directory's invariant) must carry the file out of the invariant as a
   `fileAt` (T10's obligation, below).
6. **Does `σ.b = j` identify the file Go opens?** Yes: Go's index is the newest snapshot record at or below the last
   state record's commit, over every WAL file (`validSnapshotEntries` reads from the first file); `walRead`'s is the
   same filter and `walSaveSnap`'s max (equal indexes: the last one, `newestSnapshotEntry`'s `>=`), `walReadFrom` the
   same after a purge; `srvFilesC`'s `walFilesC a id cid σ` ties the files to `σ`. The name is `hex16 (uint.nat j)`
   = Go's `%016x` of `j : w64`. Two snapshot records at `j` with different terms change the term, not the file.
7. **`db` absent** (`fileHoldsF`'s `D = ∅` case: `i = 0` by the meta premise). Go creates an empty `db`, compares
   `j` with `0`, renames `<j>.snap.db` onto `db`, skips the `kvindex` check (`!beExist`), and `Finalize`'s
   `databaseFileMissing` returns an error when `Ds` records a cluster version (the error disjunct), else succeeds at
   `(σ, j, Ds)`. **Covered.** (It also removes the renamed file: a Go finding, not a soundness one,
   `nonissues/etcd-missing-db-removes-recovered-snapshot.md`.)
8. **A stale consistent index written into `Ds`.** The cache holds `i` (step 1) while `OpenSnapshotBackend` opens
   `Ds` with the hooks; a commit of the new backend before `ci.SetBackend(new)` would store `i < j` in `Ds`
   (`OnPreCommitUnsafe` → `UnsafeSave`), and then `kvindex = i ≠ 0` is an error and the next start panics (the file
   was renamed away). Blocked by Go: `backend.New` sets the hooks after its constructor's empty commit
   (`storage/backend/backend.go:276-278`), and the run loop commits only with `safePending() != 0`; nothing writes to
   the new backend before `SetBackend`. `oldbe.Close()` stores `i` into the old file only (renamed over).
9. **The old backend's index read.** `ReadConsistentIndex(oldbe.ReadTx())` after `CreateMetaBucket` (uncommitted):
   the read transaction's missing-bucket path returns nothing (no panic), and the committed `D` has the key the
   premise names; an 8-byte value (`encMeta`). `maybeDefragBackend` is off (`bootCfgOk`, as in the first case).
10. **The post's other rows at `Ds`** (`v3ConfStateIs Ds cs` from the members bucket, `memStorRestarted σ cs`, the
    cluster's members from `restModel γ.boot Ls`): Go reads them from `Ds` exactly as the first case reads them
    from `D`; the premises on `Ls` (peer URLs as the bootstrap log's, `clusterVerLogOk Ls`) are the first case's.
    `j ≤ σ.commit ≤ σ.last` (`walReadFacts`, I1-I4) keeps raft's `RestartNode` from panicking, as there.

Not a soundness issue but worth a line: `bootstrapSnapshot` removes `tmp*`/`*.snap` names that no premise of the
law owns (they are in `snapDirOwn`, held by the snapshot directory's invariant with a free history `h`). Shared
with the first case and with the graceful contract; harmless while every law over those names leaves `h` free.

## The docstring fix (to apply with the law; text, not statement)

`bootstrapCrashContract.law`'s "Why it holds" argues only the first case ("`recoverSnapshot` with `beExist`, the
backend's index `i ≥ σ.b`, so no `.snap.db` is opened"). Add, after it:

> In the second case (`i < σ.b = j`), `recoverSnapshot` takes `j` (the newest valid snapshot record, `σ.b`),
> `RecoverSnapshotBackend` finds the old backend's index `i` (or `0` without `db`) below it and
> `OpenSnapshotBackend` renames the caller's `<j>.snap.db` onto `db`, syncs the directory and opens it; the
> `kvindex` check reads `Ds`'s index `j`; the rest is the first case's at `(σ, j, Ds)`. Review
> `notes/axiom-review/c-i2-snapdb.md` (2026-11-25): sound.

and update the file header's fork (`768ecf158` → the pin `e94f33b50`, which carries the fix).

## The caller's obligations (T10's `snapRowB2`, not this law)

* **The file out of the invariant.** In `snapRowB2`'s first disjunct (`c ≤ σ.b`) the file is inside the directory's
  invariant (`snapDirInvH`): the restart must take it out as `fileAt … Ds` before calling `bootstrap`, which needs
  the invariant's body to still hold `<σ.b>.snap.db` with its image after the crash, i.e. nothing removed it between
  `SaveDBFrom` and the install (`ReleaseSnapDBs` removes only below the released index; the purge of
  `nonissues/etcd-purge-snapdb-unopened.md` is the open hazard).
* **The image's index.** `imageRestAt … j Ls Ds` says `Ds`'s stored index is `j` exactly: the leader's
  `createMergedSnapshotMessage` must send a database whose consistent index is the message's index. If it could be
  above, Go would still succeed (`kvindex ≥ j`) but the premise could not be met.

## Measured on configuration C (2026-11-25)

`c-i2-snapdb/` (`main.go`, the Go module `snapdbcrash`, no dependencies, built with go1.27.1; `snapdb-crash.sh`, the
method of `c-i1-nopath/rename-window.sh`: `dmsetup suspend --nolockfs` at a random moment, image and step log copied,
each image recovered by a kernel mount, then checked). Each run loops `k = 1, 2, …`: `SaveDBFrom(k)` as the fork
writes it (a `tmp*` file of 64 KiB-6 MiB of PRNG bytes, `fsync`, `link` to `<k>.snap.db`, remove the temporary,
directory `fsync`), then the raft loop's `SaveSnap(k)` (an 8-byte record appended to a WAL file in another directory,
`fdatasync`), then `ReleaseSnapDBs` of `k - 2` (`os.Remove`, no directory sync). The check: every `<k>.snap.db`
present holds exactly `k`'s bytes, and every `k` whose directory sync returned or whose WAL record survived, and that
was not released, has its file. Run on fk-lean2 (Linux 7.0.0-1017-aws, `check.sh`: C).

| series | crashes | crash with a torn `tmp*` left | BAD |
|---|---|---|---|
| 1: default `commit=5` | 40 | 16 | 0 |
| 2: `commit=1` | 40 | 21 | 0 |

Every recovered `.snap.db` held its whole content; no file whose directory sync returned (or whose WAL record
survived) was missing; crashes mid-write left only a `tmp*` file (37 of 80), never a partial file under a
`.snap.db` name. Outputs: `c-i2-snapdb/results-2026-11-25.txt`.

## Not tried

A Lean counterexample (no Go execution to build one on); `bootstrap`'s crash condition (the law is a crash-free
triple); configurations outside C; a running cluster's `createMergedSnapshotMessage` index (caller's obligation).
