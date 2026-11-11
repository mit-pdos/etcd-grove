# The Linux file extension, version 2 (one directory tree, inodes, per-byte crash candidates)

**Date:** 2026-11-05, revised through 2026-11-12. **Status:** implemented (`GooseLang/Ext/Fs/`,
branch `fs-bytes`). Supersedes the two-regime design of `notes/walfs-ext-plan.md` (N2) and the
v1 crash model of `notes/osfs-ext-plan.md` (D1).

**Reading guide.** The current model is the first section below, "Byte-level crash candidates",
together with `GooseLang/Ext/Fs/Impl.lean`'s header (authoritative). The later sections record the
decisions still in force (the directory tree, inodes, machine and process, overlapping metadata
calls, restarts, the environment), each marked where a later decision superseded part of it. The
superseded models (the per-sector state, steps and crash rule, the first audit's dispositions, the
sector program logic, the phases) are in `notes/fs-semantics-v2-history.md`.

**Examples (2026-11-09):** every decision of the semantics has a Go example saying why, with the
Lean names, the outcome it allows or excludes and the evidence (measured, documented, or assumed),
in `examples/osfs/semantics/` (indexed in its `doc.go`). A change to the semantics adds or updates
its example in the same commit (`CLAUDE.md`, "Layout").

## Byte-level crash candidates (2026-11-11, the user's decisions; supersedes V5)

**What changed.** A file is its page cache (`OsFile.cache`) and, per byte, a list of crash
candidates (`OsFile.cand : Nat → List (w8 × Nat)`): the value as of the last successful sync
(stamped 0), then each value a change since announced for it, stamped with the change's number
(`FsState.stamp`, numbered from 1). A change (`PWriteStart`, `FtruncateStart`, `FallocStart`,
`O_TRUNC`) announces all its data when it starts (`OsFile.announce` of its `OsChange`:
`OsChange.ofWrite`/`ofResize`); its finish lands a prefix of exactly those values (`OsFile.land`).
At most one change is in flight per file (round 7, below). A successful sync collapses each byte not under a
change in flight to its page-cache value (zero in a page past the size); a failed sync changes
nothing. **A crash leaves each byte any one of its candidates, independently** (`CrashFile`).
Removed: per-sector versions (`Sector`, `SecCand`, `Landed`, the dirty bit, `syncFailed`, lost
sectors), `NoTear.lean` and its premise, the "no mixed writeback" assumption, and device sector
atomicity (kept: a device write leaves each byte old or new, never garbage, SQLite's "linear" model).

**Why.** Measured on configuration C (`notes/axiom-review/fs-v2-r6/e2e/`): one aligned 4096-byte
`pwrite` reaches disk torn mid-sector in two ways. (A) Its source crosses a page that compaction is
migrating: the copy stops there, the prefix is committed, writeback takes it (49 torn images in 5
runs). (B) A page rewritten while its previous writeback is in flight: without stable pages the
device reads a mix (1.3-2.2 % of such writebacks, aligned buffers, no compaction). Every guarantee
that grouped bytes (V5's "a crash leaves each sector one whole version", NoTear's page cuts, no
mixed writeback) was false of C. The user: "The general semantics should avoid making sector-level
assumptions, and we could do the byte-level thing in general" (2026-11-11); per-byte version lists
over sector versions, with the stamps, so that the clients' premises can name "one state" of a
range without the semantics grouping bytes.

**The failed-sync simplification.** The dirty and lost bits existed only for a failed `fsync`
whose writeback failed (Linux marks its pages clean; a later sync does not redo them). Under the
environment's "no failed writeback" (F1) that never happens: a failed `fsync`'s writeback either
completed or left the pages dirty, so a later successful sync makes everything durable. The model
keeps the failure (an errno) and makes it change nothing.

**Client premises** (`Premises.lean`; a theorem states them on its executions, as crash filters of
`fsSemWithS`): `valAt l n` is a byte's value right after change `n` (its candidate of largest stamp
up to `n`); `SectorWhole covers`: each 512-byte sector below the crash size of a covered file comes
back as one state `valAt · m` of that sector. False of C in general (A, B); assumed only for etcd's
WAL, whose `isTornEntry` relies on it: a known limitation (`notes/STATUS.md`;
`nonissues/etcd-wal-torn-tail-mid-sector.md`). bbolt's P1 (a validating meta slot is one state of
its sector, `valAt · m`) is stated in bbolt's statement file the same way
(`Proof/github_com/mit_pdos/etcd_grove/examples/osfs/bboltfs/BootP1.lean`); it removes no crash of
minibolt's real runs (the final review, `notes/axiom-review/fs-final.md`, and `P1Sat.lean`).

**Open.** The stamps of a change are taken at its start with all its data; a short write's real
page-cache state (a prefix new, the rest old) is a byte-wise mix of two stamps, not one: a premise
of "one state" excludes it, which for `SectorWhole` is the assumption's intent (a sector torn by
a short write is a torn sector) and for P1 a slot torn that way must fail its checksum, as one torn
by A or B.

**Round 7 (2026-11-11, `notes/axiom-review/fs-v2-r7.md`; fork S2).** The page cache is a crash
candidate *by construction*: a change records what its start announced (`OsChange.lo`, `hi`, `val`,
`target`: `OsChange.ofWrite`, `ofResize`), and its finish lands a prefix of exactly those values
(`OsFile.land`) instead of recomputing them from the size at the finish. `Tests.lean` proves the
invariant (`CacheOk`: every file's page cache among its candidates, every change in flight's values
candidates of its file) at the start, after every step (`cacheOk_step`, each case of `IsFsStep`) and
after a crash. Two stuck restrictions replace the concurrency machinery (the user, 2026-11-11:
"make those assumptions instead of overcomplicating the semantics"): **at most one change in flight
per file** (every `…Start` and `open(O_TRUNC)` stuck while one is; it removes the disjoint-range
check, `Affects`, the resize's `[min, ∞)` range, the `O_TRUNC`-racing-a-write case and the
out-of-order finishes of `valAt`), and **no empty `pwrite`** (Go never issues one; it removes the
special cases of `written` and of an empty write past the end). Both only remove executions; every
client changes each file from one thread.

## Why

The extension as of `worktree-walfs-ext` has two ways to name a file: the original fixed table of
paths (`files : GMap GoString (Option OsFile)`, the "old regime") and the directory tree under fixed
roots, whose files live in the same table under NUL-byte keys. The split is not a Linux concept: it
exists because the original extension never modelled path resolution. Version 2 has one directory tree,
files keyed by internal inode numbers, the machine's state separated from the process's, and a
crash model at the granularity of 512-byte sectors, which is what etcd's WAL needs to restart.

## Decisions

- **V1, one directory tree.** Every path a program uses is resolved in the directory tree under the roots
  (directories fixed at boot); any other path is stuck. No `Regime` query, no second `Open`.
- **V2, inodes, internal.** Files are keyed by `Ino := Nat`, allocated fresh at create; no call
  takes or returns one. File identity is needed because Linux's fds, mappings and in-flight
  changes follow a file across `rename` and survive `unlink` (etcd: `wal.cut` renames the open
  tail, `PurgeFile` removes a locked segment), and because a crash can pair an older name with the
  current contents (create `a.tmp`, write, rename to `a`, write `Y`, crash before the rename
  commits: `a.tmp` may hold `Y`). A state keyed by path alone either misses that execution
  (unsound) or rebuilds identity elsewhere (fd paths rewritten on rename, orphans held by fds, the
  log replayed on file locations). An unlinked file stays in `files`; a crash drops every inode
  the surviving directory tree does not name. Nothing is dropped before a crash.
- **V3, machine and process.** `FsState` (names, files: the machine, what survives the process)
  and `ProcState` (fds, directory fds, in-flight changes, mappings, the metadata flag: the
  process). Both are the extension's per-node `LocalState` (Perennial's node is one machine running
  one Go program).
- **Naming.** The map from paths to what is there is the *directory tree* (POSIX: the file
  hierarchy; Linux implements it as directory entries, dentries), `Tree`; create, mkdir, remove and
  rename are *metadata operations*, `MetaOp`. "Namespace" is not used: Linux namespaces (mount,
  PID, ...) are a different thing.
- **V4, names: a base and a log.** `FsState` holds `treeDur`, the directory tree as of the last journal
  commit the model knows of, and `metaLog`, the metadata operations since, in order. The directory tree now
  is derived, `treeNow fs := replay fs.metaLog fs.treeDur` (no stored copy, so no invariant to keep).
  A metadata step checks its preconditions against `treeNow` and appends to `metaLog`; a commit of `k`
  operations folds `metaLog.take k` into `treeDur`; a crash keeps `replay (metaLog.take n) treeDur` for
  some `n` (ext4/xfs: metadata reaches the journal in order and the journal commits in order).
  *Superseded in part* (2026-11-06 and 2026-11-10, "Directories as inodes; overlapping metadata
  calls" below): a crash keeps a set of logged entries closed under `Follows` (not a prefix), and a
  directory `fsync` commits every logged entry (`OsState.commitAll`, not `dirCommitLen`).
  Names keep a base and a log, where file contents do not, because a crash keeps a prefix of one
  global order. A directory `fsync` commits through the last operation that changed its entries
  (`dirCommitLen`); a file `fsync` commits no name (as before; weaker than ext4).
- **V5, file contents by 512-byte sectors.** *Superseded 2026-11-11* by "Byte-level crash
  candidates" above (a crash leaving each sector one whole version is false on C). A file is a map from sector numbers to sectors. A
  sector holds every version it had since the last successful sync (the last one is the page
  cache's), and the kernel's dirty bit. A crash leaves one of the versions. There is no separate
  page cache (`cur`) or disk image (`durable`): the page cache is the last version of each sector,
  and what the disk may hold is the list. The dirty bit is needed only for failed fsyncs: Linux
  marks a failed sync's pages clean, so no later sync writes them, though the disk may hold any of
  their versions (D2's "lost" pages: not dirty, more than one version). Without failed fsyncs it
  would equal "more than one version". Naming: "sector" is the kernel's word for the fixed 512-byte
  unit (`sector_t`); "block" means the filesystem's block (4 KiB on ext4/xfs) or the device's
  logical block (4096 on 4Kn drives), so it is not used for this unit.
- **V6, process restart.** *Superseded 2026-11-06* by "Restarts are machine crashes" below (no
  process-restart crash; an environment assumption instead). Originally: staged after V1–V5. A crash outcome besides the machine
  crash: the process state is gone, the machine's is unchanged except that each in-flight change
  lands as some prefix. Today a process death is treated as a machine crash, which makes the files
  fully durable: unsound if the machine later loses power before writeback (a generation could rely
  on data that a later power loss removes). `notes/` records this as a finding.

## Directories as inodes; overlapping metadata calls (2026-11-06)

The three stuck cases of the first design ("After the soundness audit", `notes/fs-semantics-v2-history.md`) are lifted by one change (`Tree.lean`, `Impl.lean`):

- **Directories have inodes.** The tree is every directory by inode, with its entries (name ↦ file
  or directory); paths resolve by walking from a root (`OsState.lookup`). A rename moves an entry,
  and the directory's subtree with it. A directory fd holds the directory's inode, so a rename or
  rmdir with an fd open is no longer stuck (a removed directory reads as empty).
- **Operations are journaled by directory inode and name** (`MetaOp`), so replaying a subset of
  them gives a tree whatever the others did to the paths above.
- **Metadata calls overlap.** `MetaBegin` returns a token recording the log's length when the call
  began; the call's step takes it. A crash keeps a set of logged entries holding the committed ones
  and closed under `Follows`: an entry that took effect before another's call began, an earlier
  entry changing or locking a common directory, and an earlier rename across directories (the
  filesystem's rename lock) must be kept with it. Entries related by none of these change disjoint
  directories, so they commute, and replaying the set in log order gives what the journal's own
  order would. (Review round 1's finding 4: an observer can order two overlapping calls against the
  journal, so neither order can be assumed; this keeps both.)
- **A directory `fsync`** makes the directory's last logged change durable, with everything it
  follows (`Needed`); a failure guarantees nothing. The rebinding rule is gone: the directory is
  its inode, not its path. `wal.Create`'s `fsync` of a directory made in the same run now commits
  (`dirsync_new_dir`).
- Inodes are allocated from a counter (`FsState.nextIno`), for files and directories.
- After the second review (`notes/axiom-review/fs-v2-r2.md`): a path is resolved at the call's step,
  but Linux walks it component by component, so every call on a path begins with `CallBegin` and a
  directory's rename is stuck while another such call is in flight; `Follows` orders by the
  directories an operation locks (`MetaOp.locks`: not a directory a rename moves); a restart begins
  after the old process has left the kernel (assumed).
- *Superseded 2026-11-10* (review round 5, S1/S2, `notes/axiom-review/fs-v2-r5.md`): `Follows`
  keeps only its first clause (an entry that took effect before another's call began is kept with
  it); the lock and cross-rename clauses (`MetaOp.locks`, `crossRename`), which no proof used, are
  gone: Linux orders those pairs too, so dropping them only allows more crashes. A successful
  directory `fsync` commits every logged entry (`OsState.commitAll`: ext4 on C commits the whole
  journal for a file that is not regular, `ext4_force_commit`); `MetaOp.dirs`, `lastTouch`,
  `Needed` and `commitThrough` are gone. The journal order was measured on C (B1).

- `TreeWf` (2026-11-06, during the port) allows removed directories: unreachable, empty, named by
  no entry (an `rmdir`, or a rename onto an empty directory, leaves its inode in the tree so that an
  fd on it keeps working). It weakens a premise of `FsInit` only (the adequacy statement assumes
  less).

## Restarts are machine crashes (2026-11-06, the user's decision)

`ProcRestart` is gone: `OsCrash` is `MachineCrash`, under an environment assumption (`Impl.lean`'s
header, "Restarts"): the program restarts only after a machine restart, or after the old process has
exited and a `sync(2)` has made what it left durable (a supervisor runs `sync` before restarting it).
The state right after a process's restart is always a machine-crash outcome (every byte's page-cache
value is a candidate, and the whole log a closed set), but the next generation would then treat dirty
data as durable: without the `sync`, a later power loss could lose data that generation relied on
(e.g. it writes and syncs only another file pointing at it), an outcome the model excludes. With the
`sync` and no failed writeback, the disk is the page cache and the journal is committed, so the
restart is the machine crash that keeps everything. The per-sector lost tracking a restart needed
(`ee10d8f05f`) was reverted (`6040582275`).

## Environment assumptions (hypotheses of the adequacy statement)

**The target configuration C** (2026-11-09, the user's decision: one configuration, a reasonable
etcd deployment, every claim tested on it): Linux 7.0, x86-64, 4 KiB pages, no swap; one local
ext4 made by `mkfs.ext4` with its defaults (4 KiB blocks), mounted with ext4's default options
(`data=ordered`, `delalloc`, `dioread_nolock`, barriers); `RLIMIT_FSIZE` unlimited; Go 1.27.3.
`notes/axiom-review/fs-config/` (README, `check.sh`, `mkfs-mount.sh`, `crash.sh`). xfs,
`data=journal`, other block sizes and kernels are outside the claim until tested on their own.

On C, for the roots: regular files and directories only, no hard links, no other process changes
the trees, no read-only or error event; the device honours flushes, has no media errors. For
sectors:

- **Sector atomicity.** *Superseded 2026-11-11* ("Byte-level crash candidates" above): the device
  assumption is now only that a device write leaves each byte old or new, never garbage. Originally:
  a crash leaves each 512-byte sector of a write entirely old or entirely as sent. Sound for 512n and 4Kn devices alike (a 4 KB-atomic device's crash states
  are 512-byte-atomic ones); excludes devices whose write damages sectors it does not write (512e
  without power-loss protection).
- **No failed writeback** (new, F1): no writeback of a file in the roots' trees fails.
- **Durable at first start** (new, F2): when the program first starts, the roots' trees and their
  files are durable.
- **No mixed writeback.** *Superseded 2026-11-11* (refuted on C, mechanism B; the per-byte rule
  models the mix, and etcd's WAL's need is the client premise `SectorWhole`). Originally: the data a writeback sends never mixes a page's contents before
  and after a concurrent write into it. ext4 does not promise it: without stable
  pages (`BDI_CAP_STABLE_WRITES`), a write may change a page during its DMA. The alternative is to
  model the mix (a sector may also hold a byte-wise mix of two consecutive versions), which needs no
  assumption but under which etcd's WAL cannot be proved to restart (its `isTornEntry` needs an
  all-zero sector). Chosen: the assumption, stated as one (pending the user's confirmation).
