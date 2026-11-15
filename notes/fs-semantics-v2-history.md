# The Linux file extension, version 2: superseded design sections

Moved from `notes/fs-semantics-v2.md` on 2026-11-12 (the final review's D3): the per-sector state,
steps and crash rule of version 2 as first designed, the first audit's dispositions, the sector
program logic and the phases. All superseded by that note's "Byte-level crash candidates" and by
`GooseLang/Ext/Fs/Impl.lean`; kept as the record of the decisions.

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

## After the soundness audit (`notes/axiom-review/fs-v2.md`, 2026-11-05)

Implemented in `GooseLang/Ext/Fs/{Paths,Tree,Impl}.lean` (with `Tests.lean`), standalone: the
clients still use `GooseLang/Ext/OsFs`. A fresh reviewer audited it (six findings, all in the data
path; the tree and the journal survived every attack). Dispositions:

- **F1, reads after a failed writeback** (Linux may drop data whose writeback failed, so reads return
  the disk's older contents): an environment assumption, *no failed writeback* (no I/O error, no
  delayed-allocation failure, for the roots' files). The failed `fsync` and lost sectors stay in the
  model (more behaviours). Neither etcd nor bbolt goes on using a file after a failed `Sync`.
- **F2, everything durable at the first start**: an environment assumption, *durable at first start*.
- **F3, stale bytes past EOF after a crash** (ext4): a model change. A crashed file keeps each
  sector's chosen version whole (`CrashFile`, `OsFile.ofDisk`), and an extension (`ftruncate` grow, a
  write's gap) shows what the sectors hold past the old size (`OsFile.resized`/`written` read
  `rawAt`), not zeros. In a run without a crash those bytes are zeros (every version is zero past the
  size it was made at), so nothing changes there; after a crash a proof must treat them as unknown.
  *Superseded 2026-11-08*: refuted by a crash test (ext4 zero-fills every extension,
  `notes/axiom-review/fs-v2.md`, F3); extensions read zeros again. The ordered-growth rule that
  followed (`Sector.fresh`) was refuted in turn (round 4, U1: ext4's default `dioread_nolock`
  commits an unwritten extent with its size) and replaced, 2026-11-09, by **durable zeros**: wherever
  a file's size is durable (sync, boot, crash) the pages wholly past it are zeros, and nothing orders
  sizes against data (`examples/osfs/semantics/data_durable_zeros.go`).
- **F4, short `pread` without an error**: a model change (success returns a non-empty prefix, or
  nothing at EOF).
- **F5, a restart during `fallocate`**: a model change (`Landed`: a resize lands at any size between
  the file's and its target).
- **F6, short `pwrite` with errno 0**: a model change (allowed).

**Stuck or less defined than Linux, which the clients hit** (sound; to decide before the WAL's proof):
`MetaBegin` forbids overlapping metadata calls, which etcd's WAL makes (the file pipeline creates the
next segment while `cut` renames, and purge runs beside both); a rename or rmdir with a directory fd
open on the tree is stuck, and etcd keeps one open on the WAL directory for its whole life; a
directory `fsync` commits nothing for a directory made or moved since the log's start
(`dirCommitLen`'s rebinding rule), which `wal.Create`'s `fsync` relies on.

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
