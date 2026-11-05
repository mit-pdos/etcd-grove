# Plan: the namespace of the Linux file extension (directories, rename, unlink) for the WAL

**Date:** 2026-11-05. **Branch:** `worktree-walfs-ext`. **Status:** the semantics, its trusted Go
models, the examples, the sanity lemmas (`TestsNs.lean`) and the repair of every existing proof
are done; the namespace's program logic and the crash proof of `segdir.Boot` are designed, not
done ("The program logic of the namespace"). Carried out by an agent while the
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
| `NsBegin()` | the start of a call that changes the namespace (`open` with `O_CREAT` of a managed path, `rename`, `unlink`, `rmdir`, `mkdir`): stuck while another one is between its start and its step; the trusted models make it just before the call. Two such calls that overlap in time are a stuck run of the model (round 1, finding 4). |
| `DirSync(fd)` | commits the log through the last operation that changed the directory (`dirCommitLen`: nothing while the log holds an operation that made, removed or moved the directory's path or one above it, round 1, finding 1). |
| `DirClose(fd)` | frees the directory fd. |
| `DirReadNext(fd)` | one name at a time (the read's state is the fd's): the names the directory had throughout, each once, and any of the names it had in between, again if touched since returned (POSIX's `readdir` across concurrent changes; round 1, finding 5); then the end. A second read of one fd is stuck. |
| `NsLstatDir(p)` | `lstat`'s "is it a directory", which `os.Rename` asks of its destination: `(1, e)` for a directory, `e` a nonzero errno (the error `os.Rename` returns, `EEXIST` or the `lstat` of the source's); `(0, _)` for anything, a directory too (the `lstat` failed; round 1, finding 2). A query of the state, not a change. |
| `Rename(src, dst)` | `rename(2)`: a file onto nothing or a file (replaced; the old file stays readable through its fds); a directory onto nothing or an empty directory (replaced), not into its own tree. Stuck while a directory fd is open in `src`'s tree or on `dst`. Go's `os.Rename` (its trusted model) first refuses an existing directory as `dst` (`NsLstatDir`), as Go does: two system calls, so a directory made at `dst` between them is replaced, as on Linux. |
| `Unlink(p)`, `Rmdir(p)` | `unlink(2)` of a file (its fds keep it), `rmdir(2)` of an empty directory (stuck while a directory fd is open on it). Go's `os.Remove` (its trusted model) is Go's: `unlink`, then `rmdir` if that failed, the error chosen as Go chooses it. |
| `Mkdir(p)` | a new directory. |
| `FallocStart(fd, off, len)`, `FallocFinish(tok)` | mode 0: a truncate to `max size (off+len)` in flight; on failure the file may have any size between (ext4 grows it chunk by chunk; round 1, finding 3). Stuck on a negative offset or a length not above 0. |
| `FallocKeep(fd, off, len)` | `FALLOC_FL_KEEP_SIZE`: no visible change, any errno. |
| `OfdLock(fd, cmd)` | trivial, as `Flock` (D7): any errno. |

### The trusted Go models (`TrustedCode/os.lean`, `TrustedCode/golang_org/x/sys/unix.lean`)

- `os.OpenFile` asks `Regime` and calls `Open` or `NsOpen`; `os.Open` is translated (Go's
  `OpenFile(name, O_RDONLY, 0)`).
- `File.Sync` and `File.Close` ask `FdKind` and call `Fsync`/`Close` or `DirSync`/`DirClose`.
- `os.Rename` (Go's `rename`: `Lstat` of the destination, then `rename(2)`, `EINTR` retried),
  `os.Remove` (`unlink`, then `rmdir`), `os.Mkdir` (`mkdir(2)`), `File.Readdirnames(n)` for `n ≤ 0`
  (a loop of `DirReadNext`, never a nil slice; `n > 0` panics: not modelled).
- `unix.Fallocate` (mode 0: `FallocStart` and `FallocFinish`; `FALLOC_FL_KEEP_SIZE`:
  `FallocKeep`; other modes panic; stuck on a negative offset or a length not above 0; no `EINTR`
  retry, as x/sys/unix), `unix.FcntlFlock` (`OfdLock` for the lock-setting commands 6, 7, 37, 38;
  every other command panics).
- `NsBegin` before each call that changes the namespace (`OpenFile` with `O_CREAT` of a managed
  path, `rename(2)`, `unlink`, `rmdir`, `mkdir`), in every `EINTR` retry.

### Review round 1 (2026-11-05, a fresh reviewer, of the trusted files)

First tier, all repaired the same day:
1. `commitLen` matched directories by path text: after `/r/a` was moved away and another directory
   moved to `/r/a`, an fsync of `/r/a/b` committed a create made in the old `/r/a/b` (on xfs the
   fsync forces only the new directory's own changes). Now `dirCommitLen`: nothing is known
   committed while the log holds an operation that rebinds the path (made, removed or moved it or
   one above it). Sound (commits less); the WAL's `Create` and `cut` are unaffected.
2. `NsLstatDir` could not fail on a directory: Go then goes on to `rename(2)`, which may replace an
   empty directory. Now `(0, _)` is always possible.
3. A failed `fallocate` could leave only no change or the full size; ext4 grows the file chunk by
   chunk. Now `FallocFinish`, any size between on failure.
4. The log's order is not the journal's when calls in different directories overlap in time (the
   journal handle ends inside the inode operation, the dentry update after it, so an observer can
   order the model's steps against the journal). Now `NsBegin`: such calls never overlap in the
   model (an overlap is stuck). Consequence: the model cannot run two goroutines making metadata
   calls at once, and **the WAL does** (`filePipeline`'s goroutine creates the next `N.tmp` while
   `cut` renames the previous one; etcd's purge beside both): the WAL is not verifiable over this
   repair, `segdir.Boot` is. Lifting it, before the WAL: start/finish steps for the namespace's
   calls, each logged with the calls that had finished when it began, and a crash that keeps a set
   closed under "finished before the other began", calls on one directory serialized (as its lock
   serializes them).
5. `readdir` may return a name twice (xfs block directories, ext4 linear ones) when its entry moved
   meanwhile. Now a touched name may be returned again.
6. The environment assumptions did not say one filesystem (one journal), the mount options, no
   casefold, only regular files and directories. Now they do.

Second tier: `FcntlFlock` now models only the lock-setting commands (6, 7, 37, 38), panics on the
rest; `Fallocate` no longer answers `EINVAL` before the fd's checks (stuck on bad arguments,
misuse); the roots' form is canonical (`RootForm`), so textual nesting is nesting. Kept as is:
`Regime` answers `0` for a NUL key, so a legacy `Open` of a key may succeed where Go returns
`EINVAL` (an extra behaviour, sound; excluding it would put a premise on the existing `OpenFile`
spec). Noted for etcd (the reviewer's 11): `wal.Create` syncs `member/`, so a root must contain
`member/`, which then contains `member/snap/db`: bbolt's file would be in the namespace, not the
legacy regime, in a proof of etcd's server over this extension.

### Review round 2 (2026-11-05, a fresh reviewer, of round 1's repairs)

No first-tier finding: `dirCommitLen`, `NsBegin`/`nsBusy` (cleared on every branch, re-run on every
retry, reset by a crash), `FallocFinish`, `NsLstatDir` with `os.Rename`, `DirReadNext` were checked
sound. Repaired: roots are absolute (`RootForm`), and the environment says the legacy paths
resolve (not only textually) outside the roots' trees, no directory above a root moves, and the
filesystem is never read-only nor shut down (ext4's `errors=remount-ro`: an `fsync` may then return
0 without committing); `seglog.go`'s `ZeroToEnd` skips a 0-byte fallocate, as etcd's
`Preallocate` does. Recorded, not changed: `Rename`/`Unlink`/`Rmdir`/`Mkdir` of a root is stuck
(Linux fails; a program relying on that error cannot be verified); an `O_TRUNC` open racing an
in-flight `fallocate` gives an extra size (sound); `dirCommitLen` commits nothing for a directory
just made or moved, where ext4/xfs commit its creation (sound, weaker).

### What changed for the extension's existing clients

- `OsState` has the namespace's fields (with defaults); `Open` picks an fd that is no directory
  fd; `OsCrash` is `OsCrashFiles ∧ NsCrash` (`OsCrashFiles` is the old relation); `OsInit` is
  `OsInitFiles ∧ NsInit` (the old one and the namespace's boot condition); the state
  interpretation is `osCtxF ∗ nsCtx`, `nsCtx` the namespace's (for now `⌜NsWf st⌝`).
- `wp_os_step` takes `OldOp o` (the operation leaves the namespace alone, `nsFrame_old`): every
  existing spec passes `(by simp [OldOp])`.
- The `os` specs of `OpenFile`, `File.Sync` and `File.Close` take one more step (`wp_osRegime`,
  `wp_osFdKind`, and `wp_osRegime_cf`/`_cs` in the crash variants).
- No statement of bbolt's or crashlog's proofs changed; both build.

### The program logic of the namespace (next; not done)

The design for the specs of the namespace's operations and the crash proof of `segdir.Boot`:

- **Ghost state** (in `nsCtx`): a fractional map from each directory to `(dur, pend)`, its
  entries (last component to node) as of a point known durable and the changes since, in order
  (`LOp`: put, delete, rename within the directory); its entries now are `pend` replayed on `dur`.
  Coherence: every prefix of the log, replayed, gives the directory some prefix of `pend` replayed
  on `dur`. A commit by anyone keeps it (prefixes of the shorter log are prefixes of the longer);
  an operation in another directory keeps it (the entries do not change); the owner's operation
  appends to `pend`; the owner's `DirSync` makes `dur` the entries now and `pend` empty. A crash
  gives the next generation each directory's entries as some prefix of `pend` replayed on `dur`
  (the namespace's `CrashRel`). Directory fds: a ghost map mirroring `dfds`. Files of the
  namespace keep the existing per-key ghost state (`osMeta k`, `osBytes k`): only `NsOpen` of a
  new name allocates it, under the fresh key.
- **Specs**: `NsOpen` (an existing file, a new name, a directory), `DirReadNext` (with a fraction
  of the directory: its entries exactly), `DirSync`, `DirClose`, `Rename` of a file within a
  directory, `Unlink` of a file, `Rmdir` of a file (fails), `NsLstatDir`, `Regime` of a name (`1`),
  `FdKind` of a directory fd; directory renames, `Mkdir` and `Rmdir` of a directory later.
- **The crash proof of `Boot`** needs crash-aware specs (as `CrashOps.lean`'s for files) for the
  directory and for the segment's file under one invariant: the directory's crash outcomes and
  the file's crash state together (`seg` names a key only after that key's data was synced).

### Not in this round

`Seek`/`Write`/`Read` at the file offset (the plan: the offset in the trusted `os.file` model,
over `pread`/`pwrite`, as Go's `poll.FD` keeps no offset of its own; the kernel's `f_pos` lock
serializes a racing pair, which the model makes a data race on the offset field, stuck); lock
state; `RemoveAll` (Go code over `Remove`, `Open`, `Readdirnames`: translatable); hard links,
symlinks, permissions.

## Round 3: the program logic and `segdir.Boot`'s crash safety (2026-11-05)

Done, no `sorry`; `lake build` of `Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Results`
succeeds.

- **Extension level** (`GooseLang/Ext/OsFs/NsSpecs*.lean`, `CrashNs.lean`): the specs above, plus
  `NsOpenCreatExisting` (the retry of an `O_CREAT` open that created the file and failed),
  `UnlinkAbsent`/`RenameAbsent` (the retry after an `EINTR` that had the effect), and the crash
  interpretation `os_crash_interpN` with `osFs_crash_adequacyN` and `osNsCrash_take`.
- **`os` level** (`Proof/os/Ns.lean`): `OpenFile`/`Open` of a directory, `Readdirnames(-1)`
  (lends the read a fraction of the directory's entry, gives it back at the end; on an error the
  fraction stays with the fd and `Close` returns it), a directory fd's `Close` and `Sync`, and a
  read-only `OpenFile` of a file of the namespace (whose `OsMeta` must exist: `mo ≠ none`).
- **The program** (`Proof/.../examples/osfs/walfs/Boot.lean`): the crash invariant `bootInv` holds
  half of `dir`'s ghost entry, a ghost variable naming the key `seg` may name in a crash outcome
  (`SegOut`), and half of that key's `OsMeta` and bytes with every crash of them `DataGood`
  (`keyRes`); `NoDirs` says `seg`/`seg.tmp` are never directories in an outcome. The three calls
  that change the directory (`unlink`, `open(O_CREAT)`, `rename`) open it around their one step
  (`wp_unlinkTmp`, `wp_createTmp`, `wp_renameTmp`); their `os` wrappers retry on `EINTR` from either
  state (`*_any`). `commit` deposits the new file, written and `fdatasync`ed, under its key before
  the rename (`synced_good`: a crash leaves the data or no file, since it is not yet durably
  named). `check`, `readNames`, `syncDir`, `Boot`'s loop over the names.
- **The result** (`Results.lean`, `crash_safety`): `osFs_crash_adequacyN` with `bootPre`; after a
  crash, the new entry of `dir` is an outcome of the old (`osNsCrash_take`), and `seg`'s key's file
  is a crash of the invariant's half (`osCrashT_take_runs_keep`).

What the proof found about the semantics' specs: none wrong; `wp_osRenameAbsent` needed the target's
"not a directory" premise (an open directory fd may not be at the target).

Left: `dirswap` (directory `Mkdir`, `rmdir`, and directory `Rename`, whose ghost update moves the
subtree's entries), `seglog` (`Fallocate`, the OFD lock, `Seek`), and the concurrent-metadata repair
(`questions.md`, 10) before etcd's WAL.
