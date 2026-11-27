# C-I1: bbolt's file after a power loss (`Proof/go_etcd_io/etcd/server/v3/storage/backend/CrashInterim.lean`)

Review 2026-11-24, `axiom` skill, a fresh agent given the axioms and the Go code (bbolt fork `ca88bb6a`,
etcd's backend); every attack in the file extension's crash model (`MachineCrash`/`CrashFile`), no Go test
(each needs a power loss).

| axiom | first statement | after the fixes |
|---|---|---|
| `dbCrashKeep_new` | survives (repackages exclusive `bPath`, `dbHalf`; a live write transaction holds `rwlock`, both of `Commit`'s syncs done under `FsNoErrAll`) | survives; now takes `dbSyncs γ path` with the name committed |
| `dbCrashKeep_half` | **refuted**: the put-back wand could be held across two commits (`D0 → X → Y`, crash before `Y`'s second sync: disk `X`, record `(D0, Y)`) | restated: the half is lent to one mask-changing update (one commit point) |
| `dbCrashKeep_close` | survives | unchanged |
| `dbCrash` | **refuted twice**: (A) a name is not durable on a file's `fdatasync` in the model (only `DirSync` commits names): a rename onto `path` lost by the crash leaves the old file; (B) a crash inside `DB.grow`'s `Truncate` leaves any size in range, not whole pages (model only: ext4 sets `i_size` atomically); (C, suspect) per-byte torn meta pages whose FNV-64 validates | (A) `dbSyncs γ path` now includes the name's commit; (B, C) the crash premise `BoltCrashWhole` (opaque, a world premise like `W1`, pending the owner) is a hypothesis on `Q` |
| `dbSyncs` | harmless (no producer: the laws are vacuous) | producer pending: bbolt's persistent `NoSync`/`NoGrowSync` fields (`Inv/Bolt.lean:90`), not etcd's configuration alone; never defrag's temporary database (`NoSync = true`) |

Survived attacks: two records for one file (`bPath`'s whole name claim, `i ∉ Dx`); a commit error
(`FsNoErrAll`); `init`'s window (a record exists only after `Open`); freelist reuse (`ReleasePendingPages`
frees only below the oldest reader); a process crash then reuse (`Open`'s `fdatasync`).

Not checked: `fileRcpt`'s receipt across generations. Consumer gaps: a closed database (defrag's
`Close`/`Rename`), the snapshot install's rename window.

## Re-review (2026-11-24, a second fresh agent, the restated set)

- `dbCrash`: **false of the model** as restated: the new meta's bytes are crash candidates from its
  `pwrite`'s start (`OsFile.announce`), before `Tx.writeMeta` fires the update, so the disk can hold the
  new data `S` while the record says `(Dl, Dn)`. No panicking program found. **Fixed**: the record carries the
  announced commit `pd` (`dbCrashKeep_announce`, holding the write transaction at `wView Dn S G`, before
  `Commit`); `_half` lets the half change only to `Dn` or the announced `S`; `dbCrash` concludes
  `D' = Dl ∨ D' = Dn ∨ pd = some D'`.
- `dbSyncs`: **unsound once produced** (persistent, but renames can undo a durable name: close, rename away
  and back without a directory sync, re-create the record). **Fixed**: split into `dbOpts γ` (persistent, the
  options) and `dbNameDur path` (exclusive, consumed by `_new`, not given back by `_close`).
- `BoltCrashWhole`: **not acceptable as stated** (opaque; cannot be read over all files without forbidding
  the WAL's crashes). **Fixed in part**: it takes the inodes it covers (`dbCrash` asks it for the database's
  inode only); it stays opaque, with the shapes the review proposes in its docstring (sizes as of a sync or a
  completed `Truncate`; each meta as of one write; FNV-64 named as probabilistic): to be defined before a
  closed theorem takes it, for the owner's packet.
- `dbCrashKeep_new` survives (relies on `FsNoErrAll` through `onFs`: now said in its docstring);
  `_half`, `_close` survive.
- Not re-reviewed after these last fixes (budget): a third look is due with the owner packet.

## Third review (2026-11-25, a third fresh agent, the set with `announce`, `dbOpts`, `dbNameDur`)

No panicking program, no `False`. `_new`, `_announce`, `_half`, `_close` **survive** (`_new` true because of
`Open`'s `fdatasync`, fork `db.go:326`, now cited). `dbCrash` **suspect through `dbNameDur`**: a path-indexed
durable-name fact is not invalidated by a later remove/rename without a directory sync, so its first producer
would make `dbCrash` false (also with an inode index: move away, sync, move back). **Fixed**: `dbNameDur`
removed; the record names γ's inode `i0` (from `boltIno`), `dbCrash` concludes `fileHoldsM i0 D'` and asks
that the crashed durable tree still name `i0` (`Named V'.now i0`); the caller reads the name from the file
extension's own crash facts. `BoltCrashWhole`: acceptable only as an interim premise; its docstring now has
the weak forms the review asks (a validating meta equals one write on its checksummed bytes; sizes from a
sync or a `Truncate` completed or in flight); still to be defined, checked satisfiable and backed by a
configuration-C example before the owner packet. `dbOpts`: acceptable if produced from `isBolt`'s read-only
field facts. Open: `fileHoldsM`'s receipt of the in-flight txid (the record should carry it). These last fixes
are not re-reviewed.

## Fourth review (2026-11-25, a fourth fresh agent, the inode-based set at `f1c92c5af1`)

**No refutation**: no panicking program, no axiom false in a state a proof can use, no `False`. `_new`,
`_announce`/`_half`, `_close`, `dbCrash` survive (duplicate records blocked by `bPath`; inode reuse impossible,
`nextIno` grows; grow syncs before writing past the old size; the receipt survives: receipts are global and each
commit costs a counted step). One gap in how the laws are stated: a **stale announcement** (announce `S`, `Put`
more, commit `S'`, the commit landing through `_close`) leaves a window where the disk holds `S'` and the record
claims `{Dl, Dn, S}`. **Fixed** (not re-reviewed): `_close` now needs `pd = none`, and `dbCrashKeep_clear` drops an
announcement only with a fresh write transaction at `Dn`. `BoltCrashWhole`: **suspect as stated** (opaque; false
of Linux for files growing by appends, e.g. a received snapshot before its rename; a meta page split across two
`pwrite`s): its docstring now restricts it to an open database with no extending write since its last sync and
says the size part belongs in the file extension's `CrashFile`; to be written out for the packet. `dbOpts`:
acceptable shape; produce it in `Open`'s postcondition behind γ's ghost names.

## Fifth review (2026-11-25, a fifth fresh agent, the final set with `BoltCrashWhole` written out)

Given the axioms, `DbOpts.lean`, `storage.OpenBackend`'s new post, the file extension's change (`szCrash`) and
the Go code (bbolt pin `ca88bb6a`, etcd's backend), not the author's conclusions. **No refutation.**

- `dbCrashKeep_new`, `_announce`, `_half`, `_clear` (first review), `dbCrash`: **survive** (sizes: `DB.grow`'s
  page-aligned targets, writes never extend the file, `maxBytes` below `maxMapSize`; meta pages stamp-0 durable in
  `grow`'s window; the in-flight txid's receipt consistent with Perennial's global receipts).
- `dbCrashKeep_close` (`pd = none` only): **suspect** (not exploitable alone): a proof could close the record inside
  `Commit`'s atomic update, after the new meta's `pwrite` started, without ever announcing; the disk could then hold
  the commit while a record closed a moment before claimed `{Dl, Dn}`. Saved only because no law covers a closed
  database. **Fixed**: `_close` takes (and gives back) a fresh write transaction at `Dn`, as `_clear`, so no commit
  is in flight when the record closes.
- `BoltCrashWhole` (now a definition: a validating meta of a file of `I` with no size change since its last sync and
  nothing in flight past its end is the slot as of one change, on its 56 checksummed bytes) and
  `boltCrashWhole_exists`: **survive** (whole-page meta writes; a torn mix of an appended file zeroes the magic
  number; the residue is the FNV-64a collision it states).
- `dbOpts` and its producer (`OpenBackend`'s post under `UnsafeNoFsync = false`): **survive** (`backend.go:227-228`,
  bbolt `db.go:191-192`; defrag reopens with `b.bopts`; only its temporary database has `NoSync`).
- The file extension's change (an `ftruncate`'s crash size exact): **survives** (`ext4_setattr` in one handle;
  `i_disksize` moves through intermediate sizes only for writeback and `fallocate`; the range from `i_disksize` to
  `i_size` stays inside `szCrash`). The reviewer measured on C a loop mixing delayed-allocation appends, an in-place
  write and truncates up, down and to the same size, 40 power losses: every recovered size in the model's set
  (besides `notes/axiom-review/fs-config/trunc-size.sh`, 40 crashes of pure truncates, all targets).

**Re-review of the `_close` fix** (2026-11-25, a sixth fresh agent): **survives**. A live write transaction at fraction 1
cannot coexist with a commit in flight (`Tx.Commit.spec` consumes `boltTx … 1`, gives back only `txDone`; `Rollback`
likewise; a read transaction is `TxView.ro`; the next writer exists only after `close` releases `rwlock`, after the
meta's `fdatasync`, `tx.go:613/621`); the closed halves cannot re-create a record over data the disk lacks (`_new` needs a
fresh writer). It notes the old form was likely sound too (a closed record claims nothing), and that `wr Dn` would block
defrag's and `CommitAndStop`'s consumers (a pending batch committed by `unsafeCommit`); **applied its proposal**: `_close`
takes any live write transaction begun at `Dn` (`wView Dn S G`), by the same argument (`_clear` keeps `wr Dn`).
