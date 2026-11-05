# Plan: the namespace of the Linux file extension (directories, rename, unlink) for the WAL

**Date:** 2026-11-05. **Branch:** `worktree-walfs-ext`. **Status:** carried out by an agent while the
user was away (the user's instruction: decide autonomously, report what to know before a merge).
Every decision below is **decided by the agent, pending the user** (`questions.md` lists them).
It extends `notes/osfs-ext-plan.md` (the extension as bbolt uses it); read that first.

## Why

etcd's WAL (`server/storage/wal`, `client/pkg/fileutil`) needs, beyond what minibolt uses:

| call (Go) | used by | the extension before |
|---|---|---|
| `os.Open(dir)`, `File.Readdirnames(-1)` (`fileutil.ReadDir`) | `Open`'s segment listing, purge | no directories |
| `File.Sync` of a directory (`fileutil.OpenDir`, `Fsync`) | `Create`, `cut` | no directories |
| `os.Rename` of a file and of a directory | `cut` (`N.tmp` to the segment name), `Create` (`dir.tmp` to `dir`) | a path is a file's identity |
| `os.Remove`, `os.RemoveAll` | `Create`, purge, `renameWAL` | no unlink |
| `os.Mkdir` (`fileutil.CreateDirAll`, `os.MkdirAll`) | `Create` | no directories |
| `os.OpenFile(O_CREATE)` of a new name in a directory | `filePipeline.alloc` | a fixed set of paths |
| `unix.Fallocate` (keep size, extend) | `Preallocate`, `ZeroToEnd` | no |
| `fcntl(F_OFD_SETLK[W])` | `LockFile`, `TryLockFile` | `Flock` only |
| `File.Seek`, `File.Write`, `File.Read` | the encoder, the decoder, `ZeroToEnd` | `pread`/`pwrite` only |

## The examples (`examples/osfs/walfs`)

- `segdir.go`, **`Boot`**: a segment committed by rename (`seg.tmp`: write, sync, rename to
  `seg`, sync the directory; the boot lists the directory, removes a leftover `seg.tmp`, checks
  `seg`). The WAL's `cut()`. **The program to prove crash-safe end to end.**
- `dirswap.go`, **`BootDir`/`Create`**: a directory made to appear atomically, as the WAL's
  `Create` (mkdir `wal.tmp`, create and sync `wal.tmp/seg`, rename `wal.tmp` to `wal`, sync the
  parent, never the temporary directory). Its panic fires under the POSIX crash model, not under
  the ordered-journal one (N1); `TestBootDirPOSIX` shows the image.
- `seglog.go`, **`Segment`/`ZeroToEnd`/`Reread`**: a segment's own calls (OFD lock, seek, write,
  fallocate in both modes, fdatasync, truncate). Pins down the calls; no property claimed.
- `walfs_test.go` runs the programs on the crash images; `linux_test.go` checks the Linux and Go
  facts the model rests on (an fd follows its file across rename and unlink; Go's `os.Rename`
  refuses an existing directory as the destination; a directory opens read-only only and its fd
  syncs; `Readdirnames` omits `.` and `..`; fallocate's modes; seek and write; OFD locks conflict
  within one process).

## Design

### The two regimes (N2)

The extension's existing state is kept, with its meaning: `files` maps keys to files, `fds`
name keys. Paths outside the **roots** are as before (*legacy*): a fixed set, each its file's
key, no rename (bbolt, crashlog). The roots are directories fixed at boot (the program's data
directories); every name in a root's tree is *managed*: resolved through the namespace.

- **Keys of managed files** contain a NUL byte (`IsInoKey`), so they are never a path Go can
  open (Go refuses a name with NUL, `EINVAL`), and never a legacy path (the environment
  assumptions already exclude NUL from paths). A file created in the namespace gets a fresh such
  key. An fd names the key, so it follows the file across a rename or an unlink, as on Linux.
- **The legacy regime is unchanged**: every existing step of `IsOsStep` is as it was, except
  that `Open` picks an fd that is no directory's fd either. `os.OpenFile`'s model asks the
  extension which regime a path is in (`Regime`, a query that is not a system call: is the path
  a key of `files`) and opens it with `Open` or `NsOpen`.
- *Alternatives rejected*: re-keying `files` by inode with names as a map in front of it (every
  spec and every bbolt proof keyed by path would be restated); one regime with legacy paths in
  the namespace (`Open`'s step and every proof over it would change).

### The namespace state

`ns` (name to node, `.file key` or `.dir`), `nsDur` (the names as of the durable prefix),
`nsLog` (the metadata operations since, in order), `roots`, `dfds` (directory fds: fd to the
directory's path, and whether `Readdirnames` has read it), `reads` (directory reads in flight).
The invariant `NsWf`: `ns` is `nsLog` replayed on `nsDur`; every name is a root or a valid name in
a directory of `ns`; every managed file's key is in `files`; no two names share a key (no hard
links); legacy keys lie outside the roots' trees; the fds of files and of directories are
disjoint.

### Crash semantics of names (N1)

**A crash keeps a prefix of the metadata operations since the last commit** (create, mkdir,
unlink, rmdir, rename, each atomic), and **an fsync of a directory `d` commits every operation up
to the last one that changed `d`'s entries** (its parent's entries for a rename of `d` itself
are its parent's). This is ext4's (`data=ordered`, the journal on, no `fast_commit`) and xfs's
behaviour: metadata goes through one journal committed in order, and `fsync(d)` forces it up to
`d`'s last change. It is stronger than POSIX, which says nothing of crashes, and weaker than the
journals in one way: an fsync of a *file* commits none of the names (on ext4 and xfs it commits
the journal up to the file's last change, which includes its creation). Recorded alternatives:
- *POSIX-only* (each directory's entries durable through its own fsync, independently): sound on
  any file system, and **etcd's `Create` is not crash-safe under it** (`dirswap.go`): it never
  syncs `dirpath.tmp` after creating the first segment in it.
- *Per-file fsync commits the journal* (ext4's actual behaviour): stronger; not needed by the WAL.
Environment assumption added: ext4 or xfs with the default journal (`notes/osfs-ext-plan.md`'s
list), `fast_commit` off.

A file's bytes keep their crash semantics (D1, D2): the namespace decides which keys survive and
under which names; each surviving key's bytes are a `CrashImage` as before.

### The operations (new cases of `IsOsStep`)

Every one may fail with any nonzero errno, with no effect or (for the namespace changes) with
its effect; misuse is stuck (D6). Paths must be *canonical* (no empty component, no `.` or `..`,
no NUL) and in a root's tree, or the step is stuck (path resolution is not modelled).

| op | effect |
|---|---|
| `Regime(p)` | `0` if `p` is a key of `files` (legacy), else `1`. No system call. |
| `NsOpen(p, fl)` | a file name: as `Open` on its key; a new name with `O_CREAT` in a directory of `ns`: a fresh key, a new empty file, a `create` logged; a directory with `O_RDONLY`: a directory fd. |
| `FdKind(fd)` | `0` for a file fd, `1` for a directory fd, stuck otherwise. No system call. |
| `DirSync(fd)` | commits the log through the last operation that changed the directory. |
| `DirClose(fd)` | frees the directory fd. |
| `DirRead(fd)`, `DirReadFinish(tok)` | two steps: the names the directory had throughout, and any of the names it had in between, each once (POSIX's `readdir` across concurrent changes). A second read of one fd is stuck. |
| `Rename(src, dst)` | Go's `os.Rename`: an existing directory as `dst` fails (Go's own check); a file onto a file replaces it (the old file stays readable through its fds); a directory moves its subtree. A directory or one in its tree with an open directory fd or a read in flight is stuck. |
| `Remove(p)` | Go's `os.Remove`: unlink a file (its fds keep it), or remove an empty directory. |
| `Mkdir(p)` | a new directory. |
| `FallocStart(fd, mode, off, len)` | mode 0: a truncate to `max size (off+len)` in flight (its finish is `FtruncateFinish`); `FALLOC_FL_KEEP_SIZE`: no change. |
| `OfdLock(fd, cmd)` | trivial, as `Flock` (D7): any errno. |

### Not in this round

`Seek`/`Write`/`Read` at the file offset (the plan: the offset in the trusted `os.file` model,
over `pread`/`pwrite`, as Go's `poll.FD` keeps no offset of its own; the kernel's `f_pos` lock
serializes a racing pair, which the model makes a data race on the offset field, stuck); lock
state; `RemoveAll` (Go code over `Remove`, `Open`, `Readdirnames`: translatable); hard links,
symlinks, permissions.
