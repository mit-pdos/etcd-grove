# Plan: the Linux file extension, version 2 (one namespace, inodes, sectors)

**Date:** 2026-11-05. **Status:** design agreed with the user in outline (this note); not
implemented. Supersedes the two-regime design of `notes/walfs-ext-plan.md` (N2) and the per-byte
crash model of `notes/osfs-ext-plan.md` (D1) once it lands.

## Why

The extension as of `worktree-walfs-ext` has two ways to name a file: the original fixed table of
paths (`files : GMap GoString (Option OsFile)`, the "old regime") and the namespace under fixed
roots, whose files live in the same table under NUL-byte keys. The split is not a Linux concept: it
exists because the original extension never modelled path resolution. Version 2 has one namespace,
files keyed by internal inode numbers, the machine's state separated from the process's, and a
crash model at the granularity of 512-byte sectors, which is what etcd's WAL needs to restart.

## Decisions

- **V1, one namespace.** Every path a program uses is resolved in the namespace under the roots
  (directories fixed at boot); any other path is stuck. No `Regime` query, no second `Open`.
- **V2, inodes, internal.** Files are keyed by `Ino := Nat`, allocated fresh at create; no call
  takes or returns one. File identity is needed because Linux's fds, mappings and in-flight
  changes follow a file across `rename` and survive `unlink` (etcd: `wal.cut` renames the open
  tail, `PurgeFile` removes a locked segment), and because a crash can pair an older name with the
  current contents (create `a.tmp`, write, rename to `a`, write `Y`, crash before the rename
  commits: `a.tmp` may hold `Y`). A state keyed by path alone either misses that execution
  (unsound) or rebuilds identity elsewhere (fd paths rewritten on rename, orphans held by fds, the
  log replayed on file locations). An unlinked file stays in `files`; a crash drops every inode
  the surviving namespace does not name. Nothing is dropped before a crash.
- **V3, machine and process.** `FsState` (names, files: the machine, what survives the process)
  and `ProcState` (fds, directory fds, in-flight changes, mappings, the metadata flag: the
  process). Both are the extension's per-node `LocalState` (Perennial's node is one machine running
  one Go program).
- **V4, names: a base and a log.** `FsState` holds `nsDur`, the namespace as of the last journal
  commit the model knows of, and `nsLog`, the metadata operations since, in order. The namespace now
  is derived, `nsNow fs := nsReplay fs.nsLog fs.nsDur` (no stored copy, so no invariant to keep).
  A metadata step checks its preconditions against `nsNow` and appends to `nsLog`; a commit of `k`
  operations folds `nsLog.take k` into `nsDur`; a crash keeps `nsReplay (nsLog.take n) nsDur` for
  some `n` (ext4/xfs: metadata reaches the journal in order and the journal commits in order).
  A directory `fsync` commits through the last operation that changed its entries
  (`dirCommitLen`); a file `fsync` commits no name (as before; weaker than ext4).
- **V5, file contents by 512-byte sectors.** Each sector is `clean` (the disk holds the current
  contents), `dirty old` (the disk holds one of the versions `old` it had since the last successful
  sync, or the current one), or `lost old` (the same, and a sync does not write it: a failed sync's
  pages, which Linux marks clean). This replaces `durable`/`dirty`/`lost` per byte: a byte not
  written since the last sync agrees across every candidate, so the per-byte model's crash images
  contain the sector model's (the bridge lemma below), and `durable` was redundant anyway (a clean
  byte's durable value is its current one).
- **V6, process restart** (staged after V1–V5; see "Phases"). A crash outcome besides the machine
  crash: the process state is gone, the machine's is unchanged except that each in-flight change
  lands as some prefix. Today a process death is treated as a machine crash, which makes the files
  fully durable: unsound if the machine later loses power before writeback (a generation could rely
  on data that a later power loss removes). `notes/` records this as a finding.

## The state

```lean
abbrev Ino := Nat

inductive OsNode | dir | file (i : Ino)
abbrev NsMap := GMap GoString OsNode           -- canonical path ↦ what is there
inductive NsOp                                 -- a metadata operation, as logged
  | create (p : GoString) (i : Ino) | mkdir (p : GoString)
  | remove (p : GoString) | rename (s t : GoString)

abbrev Sector := Vector w8 512
inductive SecSt
  | clean
  | dirty (old : List Sector)
  | lost (old : List Sector)

structure OsFile where
  cur : List w8                                -- the page cache; its length is the size
  sec : Nat → SecSt                            -- sector s covers [512 s, 512 (s + 1))
  sizeLo sizeHi : Nat                          -- the sizes since the last successful sync

structure FsState where                        -- the machine
  roots : List GoString
  nsDur : NsMap
  nsLog : List NsOp
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
  nsBusy : Bool                                -- a metadata call between NsBegin and its step

structure OsState where
  fs : FsState
  proc : ProcState
```

A sector's contents at a moment are the file's bytes `[512 s, 512 (s + 1))` then, zero-padded past
its size: space a file grows into starts as zeros.

## The steps

Content steps find the file through `proc.fds !! fd` and then `fs.files !! ino`. Their effects on a
file:

| Step | `cur` | `sec` | sizes |
|---|---|---|---|
| `pread`, `fstat`, mapped loads | read | — | — |
| `pwrite` (two steps, as now), `k` bytes landing | written | each sector touched: `clean` → `dirty [old]`, `dirty cs`/`lost cs` → `dirty (cs ++ [old])`, `old` its contents before | widened to the new size |
| `ftruncate`, `fallocate` (grow) | resized, zero-filled | each sector whose contents change, as above | widened |
| `fsync` succeeds | — | `dirty` not under an in-flight change → `clean`; `lost` unchanged | `sizeLo = sizeHi = size` |
| `fsync` fails | — | `dirty` not under an in-flight change → `lost` (same `old`) | unchanged |

The metadata steps are those of `worktree-walfs-ext` (`open` with `O_CREAT`, `rename`, `unlink`,
`rmdir`, `mkdir`, readdir, directory `fsync` and `close`, `lstat`'s directory test, `fallocate`,
OFD locks), over `nsNow` and inodes; `open` with `O_CREAT` allocates an inode not in `files` and
logs `create p i`. The misuse, failure and race discipline of the existing extension (stuck on
misuse, any errno on environmental failure, two-step changes with holes for racing mapped loads)
is unchanged.

## Crash

**Machine crash** (`OsCrash`): `nsDur' = nsReplay (nsLog.take n) nsDur` for some `n ≤ |nsLog|`,
`nsLog' = []`; `files'` holds exactly the inodes `nsDur'` names, each a crash image of its file,
all `clean`, `sizeLo = sizeHi` its size; the process state is empty. A crash image of a file:

- its size is in `[sizeLo, sizeHi]`, or between those and the target of an in-flight change;
- each sector below it is: the current contents if `clean`; otherwise one of `old`, the current
  contents, or, under an in-flight `pwrite`, the current contents with any prefix of that write
  applied; cut to the size.

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
interpretation relates them to the new state by: a byte the ghost state calls clean equals `cur`
in every candidate of its sector. The **bridge lemma**, every sector-model crash image is a per-byte
one, carries the existing per-byte crash reasoning over unchanged. A sector-level resource is added
when a proof needs the sector guarantee (etcd's WAL restart). The namespace's ghost state (the
history, `osDir` its directory views) is keyed by inodes in place of NUL keys.

## Phases

1. This note, reviewed by a fresh agent.
2. The trusted part: `Names.lean` (inode nodes), `Impl.lean` (the state, the steps, the crash),
   the `os`/`unix` trusted models (one `OpenFile` path; fds hold inodes), the crash interpretation,
   `Tests.lean`/`TestsNs.lean`; a fresh-agent review of the trusted diff.
3. The program logic: the ghost state by inode, the per-byte interpretation and the bridge lemma,
   the namespace history over inodes, the old regime's specs removed.
4. The clients: bbolt, crashlog, the three walfs examples. bbolt's and crashlog's theorem
   statements change (their initial state: a namespace in which the file's path names an inode);
   the statement diffs go to the user before they are committed.
5. Gates, notes, interfaces.
6. V6, process restart, with its proof repairs (every generation's boot precondition then admits
   files with dirty sectors) (pending the user's confirmation of the staging).
