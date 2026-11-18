/-
The Linux file extension of GooseLang [Trusted definitions!]. The design is
`notes/fs-semantics-v2.md` ("Byte-level crash candidates"). Each decision below has a Go example
saying why, in `examples/osfs/semantics/` (indexed in its `doc.go`); a change here updates its
example.

A node's files and directories as Linux exposes them to one process: the directory tree under
fixed roots (`Tree.lean`); each file's page cache and, byte by byte, what its disk may hold after a
crash; and the process's fds, directory fds, system calls in flight and read-only shared mappings.
The machine's part (`FsState`) survives the process; the process's part (`ProcState`) does not.

**Configuration C** (the one target; `notes/axiom-review/fs-config/README.md`, whose `check.sh`
checks a machine against it and whose `mkfs-mount.sh` every experiment uses). Linux 7.0, x86-64,
4 KiB pages, no swap; one local ext4 filesystem made by `mkfs.ext4` with its defaults (4 KiB
blocks, extents, a journal; no `bigalloc`, `fast_commit`, `casefold` or `inline_data`), mounted
with ext4's default options (`data=ordered`, `delalloc`, `dioread_nolock`, barriers; any `commit=`
interval; not `journal_async_commit`, `nobarrier`, `data=journal`/`writeback`, `nodelalloc`,
`dioread_lock`, read-only); the process's `RLIMIT_FSIZE` unlimited; Go 1.27.3. Other
filesystems, options and kernels are outside the model until tested on their own.

**Environment** (hypotheses of the adequacy statement, not of this file). The roots (`FsState.roots`)
name distinct directories of the filesystem, none in another's tree; every entry in their trees is
a regular file or a directory (no symlink, mount point, device, FIFO or socket) and no file is a
hard link of another; no other process changes their trees or moves a directory above a root; **the
roots and their ancestors are existing directories throughout** (an ancestor may be a symlink to
one, a root is none: so a root's `lstat` answers as its `stat`, and `mkdir` of either fails with no
effect; `PathKind`; the program never removes, renames or replaces one either, as no step can); the
filesystem has no error or shutdown event (then an `fsync` may return 0 without committing); the
tree at boot is their trees' entries. The journal (jbd2) commits whole transactions, in order; a
metadata call joins a transaction no earlier than those of the calls that returned before it
began (measured, `notes/axiom-review/fs-v2-r5.md`, B1); an `fsync` of a directory commits the
whole journal (`ext4_force_commit` for a file that is not regular, `fs/ext4/fsync.c`).
**Restarts**: the program restarts only after a machine restart, or after the previous process
has exited (every thread of it returned from the kernel; by any means, a Go runtime fatal error
such as `netpollinit failed` at the first `os.OpenFile` included, which the model does not
describe otherwise) and a `sync(2)` has made everything it left durable (a supervisor runs `sync`
before restarting the program, e.g. systemd's `ExecStartPre=/bin/sync`): with no failed
writeback, the disk then holds the page cache and the journal is committed, so a process's
restart is the machine crash that keeps everything, and the model has machine crashes only. The
device honours cache flushes, has no media errors, and never returns garbage: a write it was
doing when the power went leaves each byte with its old or its new value (SQLite's "linear"
sector writes, `https://www.sqlite.org/atomiccommit.html`; nothing is assumed about which).
**No failed writeback**: no writeback of a file in the roots' trees fails (the device returns no
I/O error, and writeback never fails to allocate blocks, ext4's "Delayed block allocation
failed"; F1, `notes/axiom-review/fs-v2.md`): so a failed `fsync` lost nothing, and a later
successful one makes everything durable. **Durable at first start**: when the program first
starts, the roots' trees and every file in them are durable: nothing has changed them since their
last successful `sync`, `syncfs` or `fsync` (F2). Only paths in the roots' trees are given a
meaning: a step on any other path is stuck, but for the queries `PathKind` (at or above a root) and
`Open`'s outside case (a read-only `open` of a strict ancestor of a root, whose fd only `fsync`s,
with no claim on what that makes durable, and closes).

**Soundness discipline.** The model is never more defined than Linux:
* *Misuse is stuck*: a closed, forged or wrong-mode fd, an unsupported flag, `PROT_WRITE`, a
  nonzero `mmap` offset, a `munmap` of anything but a whole mapping, a negative offset, a path that
  is not canonical in a root's tree.
* *Environmental failure is a nondeterministic errno*: every step that makes a system call may fail
  with any nonzero errno (but `ENOENT` from `open` of a path that resolves, or from `getdents` of a
  directory still in the tree: `ENOENT`, 2026-11-14, pending review); on failure, the changes listed
  in each case may or may not have happened;
  a failed `pread` read a prefix; a failed `pwrite` wrote a prefix. **Page cuts**: whatever its
  errno, a `pwrite` (`PWriteFinish`) landed nothing, all of its data, or a prefix ending on a
  4096-byte page boundary of the file. On C, a write's loop (`generic_perform_write`) stops only
  before a folio (`write_begin` failing: `ENOSPC`, `EDQUOT`; the cut at `s_maxbytes`, page-aligned
  with 4 KiB blocks), and folios are page-aligned. The ways to cut inside a page are excluded by
  C and by the environment: a limited `RLIMIT_FSIZE` (C has it unlimited); a source page that
  cannot be faulted in (**every page of a `pwrite`'s source can be faulted in**, an environment
  assumption: a memory-cgroup OOM that fails a kernel-mode fault gives `EFAULT` after progress,
  mid-page; every client's source is a heap buffer, and a mapping's page needs a read that cannot
  fail); and an allocation failure in the write path after a short copy (**no allocation failure
  in the write path**, nor in a truncate's zeroing (below, "File bytes and crashes"), an
  environment assumption beside "no failed writeback": a short copy
  during a page migration followed by `ENOMEM` in the next `write_begin` stops mid-page with
  errno 0; from the kernel source, not measured). Measured on C
  (`notes/axiom-review/bbolt-port-plan-review/`): 20 of 20 `pwrite(2)` errno returns landed
  nothing; 19 of 19 short counts ended on a page boundary; at the Go level, 19 `(0, err)` results
  of `WriteAt` had a page-cut prefix landed (`ENOSPC` swept over free-block counts, `EFBIG` at
  `s_maxbytes`); both contrasts outside C (a limited `RLIMIT_FSIZE`, an unreadable source page)
  cut mid-page. It is a rule of the step's
  result only: a write in flight at a crash leaves, byte by byte, any candidates (the crash rule),
  as a process killed in mid-copy leaves a mid-page prefix in the page cache. **The largest file**
  (`maxBytes`, ext4's `s_maxbytes` on C, `2^44 - 4096`; **pending the user's review**, 2026-11-14):
  a `pwrite` lands nothing at or past it (`EFBIG` at it, a page-aligned cut when crossing it), an
  `ftruncate` or `fallocate` past it fails with no change (`EFBIG`), and no crash or first start has a
  larger file; so every file's sizes stay at most it (`OsWf.sizes`). Measured on C
  (`examples/osfs/semantics/data_maxbytes.go`).
* *Races*: a change to a file's bytes or size (`pwrite`, `ftruncate`, `fallocate`, and `O_TRUNC`
  in one step) is two steps (`…Start`/`…Finish`, the change in flight between them,
  `ProcState.inflight`). **At most one change is in flight on a file**: a change's first step is
  stuck while another is in flight on the same file (a restriction on programs, sound by
  construction: every client writes each file from one thread; Linux serializes a buffered write
  and a truncate on `i_rwsem` anyway); an `open` with `O_TRUNC` is such a first step. An empty
  `pwrite` is stuck too (Go's `WriteAt` never issues one; Go's `Write` does, and the `os` model's
  empty `Write` makes no extension step, as a zero-byte `write(2)` of an ext4 file changes nothing:
  `File.Write.impl`). A mapped load that could see a change in flight is stuck (a
  hole), and a racing `pread` or `fstat` returns any mix. Path calls
  (`CallBegin` … step) overlap, except that a rename of a directory is stuck while any other path
  call is in flight: Linux walks a path a component at a time, and the model resolves it at one
  instant, which agrees with Linux only when no directory is moved during the walk. This stuck
  case depends on other threads, so the model contains Linux's behaviours for the runs of programs
  proved not stuck (every WP is), which never have that overlap. A crash keeps a set of logged
  operations that respects the journal's order (`Tree.lean`, `Follows`).
* *Mappings*: a mapped cell is an ordinary byte cell; a store to it succeeds in the model, which on
  Linux is a fatal fault (`PROT_READ`), so the model's extra behaviours there are never Go's (Go's
  runtime makes the fault fatal unless `runtime/debug.SetPanicOnFault`, which Perennial does not
  model). A cell past EOF or under an in-flight change holds a hole (`osHole`), never a byte, so a
  Go load of it is stuck.

**Locks** (2026-11-15, the user's approval of lock state; **pending the user's review**,
`notes/wal-units/locks.md`). Whole-file OFD (`fcntl(F_OFD_SETLK[W])`) and `flock` locks, held per
open file description (`OsFd.ofd`, `OsFd.flk`), so two opens in one process conflict; the two kinds
are independent; a lock goes with its description at its `close` and at a crash. A request succeeds
only with no conflicting lock on another description (a blocking one waits for that), and may fail
with any errno and no change, `EAGAIN` from a non-blocking one only on a conflict (`LockStep`).
Classic per-process POSIX locks (`F_SETLK[W]`) are not modelled (the trusted models panic).

**Heap.** The steps never touch user memory except through `HeapRendered`: after every step, the
cells of every mapping show the file; a removed mapping's cells are gone; every other cell is
unchanged.

**File bytes and crashes.** A file is its page cache (`OsFile.cache`, what reads see) and, for
each byte, its *crash candidates* (`OsFile.cand`): the value it had at the last successful sync,
then the value each change since announced for it, stamped with the change's number. A change
announces its bytes when it starts, with all of its data, whatever it later lands (`…Start`,
`OsFile.announce`); its finish lands a prefix of exactly those announced values in the page cache
(`OsFile.land`), so the page-cache value of a byte is always one of its candidates. A file also
records the stamps of its resizes (`OsFile.rzs`), which no step reads: bookkeeping for a client
premise that must tell a resize's zeros from a write's (**pending the user's review**). A successful
sync (`OsFile.synced`) collapses every byte not under a change in flight to its page-cache value;
a failed one changes nothing (no failed writeback). **The crash rule** (`OsCrash`, a machine
crash; a restart of the process is one, by the environment's assumption on restarts): the durable
tree is kept with a set of the metadata operations since replayed (the committed ones, closed
under the journal's order, `Follows`); every file that tree names gets a size between the smallest
and the largest it had since its last successful sync (ext4's delayed allocation leaves on-disk
sizes the program never set in between), or towards the target of a change in flight, and **each
byte any one of its candidates, independently**, or zero at or past the smallest size since the
last sync (writeback's zeroing, below) (`CrashFile`); every other file, and the process's state,
is gone. Bytes are independent because
Linux's are: one `pwrite` of a page can reach disk torn mid-sector, a prefix of it new (its source
crossed a page that was migrated during the copy) or any mix of two writes (a page rewritten while
its previous writeback was reading it, on a device without stable pages); both measured on C
(`notes/axiom-review/fs-v2-r6/e2e/`). Nothing groups bytes into sectors. **Durable zeros**: at
every point where a file's size is durable (a successful sync, a boot, a crash), the bytes of each
page wholly past that size are zeros (at a sync, those not under the change in flight, which keep
their candidates): such a page has no block, or an unwritten one (`dioread_nolock`
and `FALLOC_FL_KEEP_SIZE` allocate unwritten extents), which reads as zeros (`diskByte`). The page
holding the end keeps whatever its bytes past the size hold, stale ones included; an extension
(truncate-up, a write past the end, `fallocate`) reads zeros past the old size. All measured on C
(`notes/axiom-review/fs-config/crash.sh`, `fs-v2-f3/f3.sh`). **An `ftruncate` zeroes the rest of
the page holding the old end**, to the same, a smaller or a larger size (`OsChange.ofResize`; ext4's
`ext4_block_truncate_page`, in the page cache and, ordered before the truncate's commit, on disk;
a growth's new last page past it is a hole; measured on C: `trunc-*`, `zerotoend`,
`pl-trunc-append` of `notes/axiom-review/eof-page.md`); a
`fallocate` zeroes only up to its target (`falloc-in`). It rests on **no allocation failure in the
write path** (above) widened to that zeroing: `__ext4_block_zero_page_range` gets the folio with
`FGP_CREAT` under `~__GFP_FS`, and `ext4_truncate` ignores its failure, so a memory-cgroup at its
limit could skip the zeroing of an uncached folio, leaving the stale tail on disk under a successful
`ftruncate`. **Pending the user's review** (P2 of `eof-page.md`, 2026-11-13). **Writeback zeroes the page holding
the end past the size** (`ext4_bio_write_folio`, "The folio straddles i_size. It must be zeroed out
on each and every writepage invocation", in the page cache and in the block it writes): a byte that
was past the size at some writeback since the last sync, so at or past the smallest size since then
(`sizeLo`), may come back zero whatever its candidates (`CrashFile`; a byte below `sizeLo` was
below the size throughout and is never zeroed so; after a sync `sizeLo` is the size, so the stale
candidate a sync keeps past the size is covered too). Measured on C
(`notes/axiom-review/eof-page.md`, `pl-wb-zero`: size 5020 reading `00` at bytes 5010..5019, whose
candidates were the stale `53` and the written `43`). **Pending the user's review** (P1 of
`eof-page.md`, 2026-11-13).

**Client premises** (`Premises.lean`, never part of these semantics): a theorem may assume of its
crashes more than this rule gives, as a stated premise on its executions. `SectorWhole` is one:
each 512-byte sector of the files it covers comes back as one state of that sector (`valAt` at one
stamp). It is false of Linux in general (the measurements above) and a known limitation, stated
only for etcd's WAL, whose recovery (`isTornEntry`) assumes it. The other, used by a proved
theorem, is minibolt's P1 (`Proof/github_com/mit_pdos/etcd_grove/examples/osfs/bboltfs/BootP1.lean`):
a meta slot of a crash image that validates is the slot as of one change (a torn meta does not
collide on its checksum); it removes no crash of minibolt's real runs (`notes/axiom-review/fs-final.md`).
Both are listed in `notes/STATUS.md`, "Known limitations".
-/
module

public import GooseLang.Ext.Fs.Tree

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

/-! ## State -/

/-- The crash candidates of one byte: the values the disk may hold there after a crash, oldest
first, each stamped with the number of the change that announced it; the first is the value as of
the file's last successful sync (or boot, or crash), stamped 0. -/
abbrev Cands := List (w8 × Nat)

/-- A regular file: its page cache (`cache b` is byte `b` as reads see it below the size; past the
size, what its page holds there), each byte's crash candidates, its size, the smallest and
largest sizes since its last successful sync, and the stamps of its resizes. -/
structure OsFile where
  cache : Nat → w8
  cand : Nat → Cands
  size : Nat
  sizeLo : Nat
  sizeHi : Nat
  /-- **Bookkeeping only** (2026-11-14, `notes/wal-fsext-plan.md` §2.5; pending the user's review):
  the stamps of the resizes (`ftruncate`, `fallocate`'s growth, `open`'s `O_TRUNC`) announced on
  the file since it was last read from disk (`ofDisk`: a boot or a crash; a new file starts with
  none), appended at the announcement (`OsFile.announce`). No step reads it: no behaviour or
  outcome depends on it. It lets a client premise on crashes tell a candidate a resize announced
  (zeros) from one a `pwrite` announced (W1, `LinuxFs/.../wal/W1.lean`). A sync keeps it: a resize
  in flight keeps its candidates across a sync, and stamps are never reused, so an old stamp in the
  list says nothing wrong. `examples/osfs/semantics/model_resize_stamps.go`. -/
  rzs : List Nat := []

/-- An open file description: its file, access mode, and the whole-file locks it holds. (The file
offset of `Seek`/`Write`/`Read` is the Go model's, `TrustedCode/os.lean`: every step here is
positional.) No step duplicates an fd (no `dup`, `fork` or fd passing), so each fd is its own
description, and the description's locks live in it: its `close` releases them (`Close` removes the
entry) and a crash does (the process's state is gone). **Locks** (2026-11-15, the user's approval of
lock state, I5; the semantics **pending the user's review**, `notes/wal-units/locks.md`): `ofd`, its
OFD lock (`fcntl(F_OFD_SETLK[W])`), and `flk`, its `flock` lock, each `none`, `some false` (shared)
or `some true` (exclusive); the two kinds are independent (Linux keeps them on separate lists:
`examples/osfs/semantics/locks_flock_vs_ofd.go`). Every `open` gives a description with none. -/
structure OsFd where
  ino : Ino
  readable : Bool
  writable : Bool
  ofd : Option Bool := none
  flk : Option Bool := none

/-- What an in-flight change does: a `pwrite` of `data` at `off`, a resize to `sz` by `ftruncate`
(`truncate`), or one by `fallocate`'s growth (`falloc`). -/
inductive OsChangeKind where
  | write (off : Nat) (data : List w8)
  | truncate (sz : Nat)
  | falloc (sz : Nat)

/-- A change between its two steps, of the file `ino`: what it does, and what its first step
announced (`OsFile.announce`): the bytes `[lo, hi)` it may change, the value `val b` each gets, and
the size it leaves the file (`target`). Its second step lands a prefix of the announced bytes with
exactly the announced values (`OsFile.land`), so the page cache only ever takes a value that is a
crash candidate. -/
structure OsChange where
  ino : Ino
  kind : OsChangeKind
  lo : Nat
  hi : Nat
  val : Nat → w8
  target : Nat

/-- A read-only shared mapping: its file and its length in bytes. -/
structure OsMap where
  ino : Ino
  len : Nat

/-- Where a directory fd's `Readdirnames` is: not begun; begun, with the names that were there when
it began and that no operation has touched since (`untouched`), the names there at some point since
it began (`seen`), and those it has returned (`returned`); or done (a second read is stuck). -/
inductive OsDirRead where
  | idle
  | reading (untouched seen returned : GoString → Bool)
  | done

/-- An open directory: its inode (it follows the directory across renames, and outlives its
removal: a removed directory reads as empty), and its read. -/
structure OsDirFd where
  ino : Ino
  rd : OsDirRead

/-- The machine's state: the roots (each a path and its directory's inode); the tree as of the boot
(or the last crash) and the metadata operations since, in the order they took effect (the tree now
is derived: `OsState.tree`); the entries of the log a directory `fsync` made durable (`committed`);
the files; the next inode number to allocate (every inode in use is below it); and the number of
the last change announced (`OsFile.announce`; changes are numbered from 1). A file stays in `files`
after its last name goes (its fds may still use it), until a crash. -/
structure FsState where
  roots : List (GoString × Ino)
  treeDur : Tree
  metaLog : List LogEntry
  committed : Nat → Prop
  files : GMap Ino OsFile
  nextIno : Nat
  stamp : Nat

/-- The process's state: its fds (of files, of directories of the roots' trees, and of directories
outside them, at or above a root's parent, `ofds`; all with distinct numbers), its changes in flight
(by the token their first step returned, `osTokV`), its mappings (by base address), and its calls on
paths in flight (by the token `CallBegin` returned: the length of the log when the call began). The
two kinds of token are distinct. -/
structure ProcState where
  fds : GMap w64 OsFd
  dfds : GMap w64 OsDirFd
  inflight : GMap Nat OsChange
  maps : GMap Loc OsMap
  calls : GMap Nat Nat
  /-- The fds of directories outside the roots' trees (a strict ancestor of a root, `Open`'s
  outside case, 2026-11-13): the model knows nothing of them but that they are open. -/
  ofds : GMap w64 Unit := ∅

/-- A process with nothing open or in flight. -/
def ProcState.empty : ProcState :=
  { fds := ∅, dfds := ∅, inflight := ∅, maps := ∅, calls := ∅, ofds := ∅ }

/-- A node's state: the machine's and the process's. -/
structure OsState where
  fs : FsState
  proc : ProcState

instance : Inhabited OsState :=
  ⟨{ fs := { roots := [], treeDur := ∅, metaLog := [], committed := fun _ => False,
                files := ∅, nextIno := 0, stamp := 0 }
     proc := ProcState.empty }⟩

/-- The Linux file extension. Its values are the tokens of in-flight changes; it has no global
state. -/
@[reducible] def fsExt : GooseExt where
  name := "os"
  Val := Nat
  LocalState := OsState
  GlobalState := Unit

/-! ## Constants (linux/amd64) -/

/-! ## Bytes -/

/-! ## File effects -/

section effects

end effects

/-! ## Derived facts about a state -/

section derived
variable (st : OsState)

end derived

/-! ## State effects -/

section effects2

end effects2

/-! ## The step relation -/

section step
variable [GooseExts] [GoGlobalContext]

/-! ### Locks (`notes/wal-units/locks.md`; pending the user's review) -/

end step

/-! ## Crash -/

end Fs
end Perennial

end
