# Plan: the Linux file extension, version 2 (one directory tree, inodes, sectors)

**Date:** 2026-11-05. **Status:** design agreed with the user in outline (this note); not
implemented. Supersedes the two-regime design of `notes/walfs-ext-plan.md` (N2) and the per-byte
crash model of `notes/osfs-ext-plan.md` (D1) once it lands.

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
  Names keep a base and a log, where file contents do not, because a crash keeps a prefix of one
  global order. A directory `fsync` commits through the last operation that changed its entries
  (`dirCommitLen`); a file `fsync` commits no name (as before; weaker than ext4).
- **V5, file contents by 512-byte sectors.** A file is a map from sector numbers to sectors. A
  sector holds every version it had since the last successful sync (the last one is the page
  cache's), and the kernel's dirty bit. A crash leaves one of the versions. There is no separate
  page cache (`cur`) or disk image (`durable`): the page cache is the last version of each sector,
  and what the disk may hold is the list. The dirty bit is needed only for failed fsyncs: Linux
  marks a failed sync's pages clean, so no later sync writes them, though the disk may hold any of
  their versions (D2's "lost" pages: not dirty, more than one version). Without failed fsyncs it
  would equal "more than one version". Naming: "sector" is the kernel's word for the fixed 512-byte
  unit (`sector_t`); "block" means the filesystem's block (4 KiB on ext4/xfs) or the device's
  logical block (4096 on 4Kn drives), so it is not used for this unit.
- **V6, process restart** (staged after V1–V5; see "Phases"). A crash outcome besides the machine
  crash: the process state is gone, the machine's is unchanged except that each in-flight change
  lands as some prefix. Today a process death is treated as a machine crash, which makes the files
  fully durable: unsound if the machine later loses power before writeback (a generation could rely
  on data that a later power loss removes). `notes/` records this as a finding.

## The state

```lean
abbrev Ino := Nat

inductive OsNode | dir | file (i : Ino)
abbrev Tree := GMap GoString OsNode           -- canonical path ↦ what is there
inductive MetaOp                                 -- a metadata operation, as logged
  | create (p : GoString) (i : Ino) | mkdir (p : GoString)
  | remove (p : GoString) | rename (s t : GoString)

structure Sector where
  vers  : List (Vector w8 512)                 -- every version since the last successful sync,
                                               --   oldest first; the last is the page cache's
                                               --   (non-empty)
  dirty : Bool                                 -- the kernel's dirty bit: the next sync writes
                                               --   the last version

structure OsFile where
  secs   : Nat → Sector                        -- sector n covers bytes [512 n, 512 (n + 1));
                                               --   default ⟨[zeros], false⟩
  size   : Nat
  sizeLo sizeHi : Nat                          -- the sizes since the last successful sync

structure FsState where                        -- the machine
  roots : List GoString
  treeDur : Tree
  metaLog : List MetaOp
  files : GMap Ino OsFile

structure OsFd     where ino : Ino; readable writable : Bool
structure OsChange where ino : Ino; kind : OsChangeKind   -- write off data | truncate sz
structure OsMap    where ino : Ino; len : Nat
structure OsDirFd  where path : GoString; rd : OsDirRead   -- as now

structure ProcState where                      -- the process
  fds : GMap w64 OsFd
  dfds : GMap w64 OsDirFd
  inflight : GMap Nat OsChange
  maps : GMap Loc OsMap
  metaBusy : Bool                                -- a metadata call between MetaBegin and its step

structure OsState where
  fs : FsState
  proc : ProcState
```

The file's contents (what reads, `fstat` and mappings see) are derived: the last version of each
sector, concatenated, cut to `size`. A sector never written, or past every size the file had, has
the default: space a file grows into starts as zeros. Sectors past `size` keep their versions after
a shrink, so a crash that keeps an older, larger size finds the old contents there.

## The steps

Content steps find the file through `proc.fds !! fd` and then `fs.files !! ino`. Their effects on a
file, sector by sector:

| Step | Sector `n` | Size |
|---|---|---|
| `pread`, `fstat`, mapped loads | read the last version | — |
| `pwrite` (two steps, as now), `k` bytes landing; `ftruncate`, `fallocate` (grow) | each sector whose contents change: `vers ++ [new]`, `dirty := true` (a shrink's cut sectors get zeros past the new size as their new version) | the new size; the range widened to include it |
| `fsync` succeeds | `dirty` and not under an in-flight change: `⟨[last], false⟩`; otherwise unchanged (so a lost sector keeps its versions) | `sizeLo = sizeHi = size` |
| `fsync` fails | `dirty` and not under an in-flight change: `dirty := false`, `vers` unchanged (now lost) | unchanged |

A lost sector that is written again gets a new version and `dirty := true`, so the next successful
sync writes it and collapses its list, as rewriting a page dirties it again in Linux.

The metadata steps are those of `worktree-walfs-ext` (`open` with `O_CREAT`, `rename`, `unlink`,
`rmdir`, `mkdir`, readdir, directory `fsync` and `close`, `lstat`'s directory test, `fallocate`,
OFD locks), over `treeNow` and inodes; `open` with `O_CREAT` allocates an inode not in `files` and
logs `create p i`. The misuse, failure and race discipline of the existing extension (stuck on
misuse, any errno on environmental failure, two-step changes with holes for racing mapped loads)
is unchanged.

## Crash

**Machine crash** (`OsCrash`): `treeDur' = replay (metaLog.take n) treeDur` for some `n ≤ |metaLog|`,
`metaLog' = []`; `files'` holds exactly the inodes `treeDur'` names, each a crash image of its file;
the process state is empty. A crash image of a file:

- its size is in `[sizeLo, sizeHi]`, or between those and the target of an in-flight change;
- each sector is one of its `vers`, or, under an in-flight `pwrite`, the last version with any
  prefix of that write applied; it becomes `⟨[it], false⟩`;
- `sizeLo = sizeHi = size`.

**Process restart** (V6, staged): `fs'` is `fs` with each in-flight change landed as some prefix
(a `pwrite` of `k` bytes for some `k`, a truncate applied or not, with the sector updates of the
step); the process state is empty.

## Environment assumptions (hypotheses of the adequacy statement)

As now for the roots (one local ext4 or xfs filesystem, one journal; regular files and directories
only, no hard links, no other process changes the trees, no read-only or error event; ext4
`data=ordered` or `data=journal` without `fast_commit`; the device honours flushes, has no media
errors), without the old regime's clause. For sectors:

- **Sector atomicity** (stated today): a crash leaves each 512-byte sector of a write entirely old
  or entirely as sent. Sound for 512n and 4Kn devices alike (a 4 KB-atomic device's crash states
  are 512-byte-atomic ones); excludes devices whose write damages sectors it does not write (512e
  without power-loss protection).
- **No mixed writeback** (new): the data a writeback sends never mixes a page's contents before
  and after a concurrent write into it. Ordinary ext4 and xfs do not promise it: without stable
  pages (`BDI_CAP_STABLE_WRITES`), a write may change a page during its DMA. The alternative is to
  model the mix (a sector may also hold a byte-wise mix of two consecutive versions), which needs no
  assumption but under which etcd's WAL cannot be proved to restart (its `isTornEntry` needs an
  all-zero sector). Chosen: the assumption, stated as one (pending the user's confirmation).

## The program logic

The ghost state keeps per-byte resources (`osBytes` with a clean flag per byte). Their
interpretation relates them to the new state by: a byte the ghost state calls clean has the same
value in every version of its sector. The **bridge lemma**, every crash image of the sector model
is one of the per-byte model, carries the existing per-byte crash reasoning over unchanged (a byte
not written since the last successful sync agrees across every version of its sector; the
per-byte model is conservative after a failed sync, where the sector model knows more). A
sector-level resource is added when a proof needs the sector guarantee (etcd's WAL restart). The
directory tree's ghost state (the history, `osDir` its directory views) is keyed by inodes in place of
NUL keys.

## Phases

1. This note, reviewed by a fresh agent.
2. The trusted part: `Names.lean` (inode nodes), `Impl.lean` (the state, the steps, the crash),
   the `os`/`unix` trusted models (one `OpenFile` path; fds hold inodes), the crash interpretation,
   `Tests.lean`/`TestsNs.lean`; a fresh-agent review of the trusted diff.
3. The program logic: the ghost state by inode, the per-byte interpretation and the bridge lemma,
   the directory tree history over inodes, the old regime's specs removed.
4. The clients: bbolt, crashlog, the three walfs examples. bbolt's and crashlog's theorem
   statements change (their initial state: a directory tree in which the file's path names an inode);
   the statement diffs go to the user before they are committed.
5. Gates, notes, interfaces.
6. V6, process restart, with its proof repairs (every generation's boot precondition then admits
   files with dirty sectors) (pending the user's confirmation of the staging).
