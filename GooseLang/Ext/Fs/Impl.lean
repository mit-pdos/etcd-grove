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
theorem, is minibolt's P1 (`LinuxFs/Proof/github_com/mit_pdos/etcd_grove/examples/osfs/bboltfs/BootP1.lean`):
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

/-- The page of byte `b` holds a byte below the size `sz` (4096-byte pages, which are the blocks
of the configuration: the header). -/
def pageIn (sz b : Nat) : Bool := decide (4096 * (b / 4096) < sz)

/-- The end of the page holding byte `x - 1`: `x` rounded up to a 4096-byte page. -/
def pageEnd (x : Nat) : Nat := 4096 * ((x + 4095) / 4096)

/-- What the disk holds at byte `b` of a file of durable size `sz` whose bytes are `img`: `img b`
in a page that holds a byte below `sz`; zero past it, a page with no block or an unwritten one
(**durable zeros**, the header). -/
def diskByte (img : Nat → w8) (sz b : Nat) : w8 := if pageIn sz b then img b else 0

/-- A file of size `sz` whose bytes are `img`, all of it on disk (a boot and a crash find files
so): the bytes past the size in its last page are whatever `img` holds there (stale ones included),
the pages past it zeros (`diskByte`); each byte's one candidate is what it holds. -/
def OsFile.ofDisk (img : Nat → w8) (sz : Nat) : OsFile :=
  { cache := diskByte img sz, cand := fun b => [(diskByte img sz b, 0)],
    size := sz, sizeLo := sz, sizeHi := sz }

/-- A file holding `c`, all of it on disk, zero past its end. -/
def OsFile.ofBytes (c : List w8) : OsFile := OsFile.ofDisk (fun b => c.getD b 0) c.length

/-- What reads, `fstat` and mappings see: the page cache, cut to the size. -/
def OsFile.contents (f : OsFile) : List w8 := (List.range f.size).map f.cache

/-- Byte `b`'s value as of change `n`: its candidate of the largest stamp up to `n`. It is the page
cache's value right after change `n` landed when every change on the byte since the last sync
landed all it announced (changes on a file never overlap in time: at most one is in flight). A
short landing's state (a prefix of the change new, the rest as before) is no stamp's. -/
def valAt (l : Cands) (n : Nat) : w8 := ((l.filter (·.2 ≤ n)).getLast?.map (·.1)).getD 0

/-- An open file description: its file and access mode. (The file offset of `Seek`/`Write`/`Read`
is the Go model's, `LinuxFs/TrustedCode/os.lean`: every step here is positional.) -/
structure OsFd where
  ino : Ino
  readable : Bool
  writable : Bool

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

def O_RDONLY : Nat := 0x0
def O_WRONLY : Nat := 0x1
def O_RDWR : Nat := 0x2
def O_CREAT : Nat := 0x40
def O_TRUNC : Nat := 0x200
def O_CLOEXEC : Nat := 0x80000

def EINTR : w64 := 4
/-- `ENOENT`: what a failing `open(2)` returns only for a path that does not resolve, and a failing
`getdents64` only for a removed directory (`IsFsStep`'s `"Open"` and `"DirReadNext"`). -/
def ENOENT : w64 := 2
def PROT_READ : Nat := 0x1
def MAP_SHARED : Nat := 0x1
def MAP_POPULATE : Nat := 0x8000
def osPageSize : Nat := 4096
/-- **Configuration C's largest file size**, ext4's `s_maxbytes` with 4 KiB blocks and extent-mapped
files: `(2^32 - 1) << 12 = 2^44 - 4096` (`ext4_max_size`, `fs/ext4/super.c`). No step lands a byte at
or past it, no resize reaches past it and no crash leaves a file larger (`PWriteFinish`,
`FtruncateFinish`, `FallocFinish`, `CrashFile`; at the first start, `FsInit`), so every file's sizes
stay at most it (`OsWf.sizes`). Measured on C: `examples/osfs/semantics/data_maxbytes.go`
(**pending the user's review**, 2026-11-14). It is page-aligned, so a write cut there is a page cut. -/
def maxBytes : Nat := 0xffffffff000

/-! ## Bytes -/

/-- `i` is in `[lo, hi)`. -/
def inRange (lo hi i : Nat) : Bool := lo ≤ i && i < hi

/-! ## File effects -/

section effects

/-- The contents of `f` resized to `sz`: cut, or extended with zeros (whatever the page holds past
the size: Linux zeroes it on an extension, F3). -/
def OsFile.resized (f : OsFile) (sz : Nat) : List w8 :=
  (List.range sz).map (fun b => if b < f.size then f.cache b else 0)

/-- The contents of `f` with `d` written at `off`, any gap past the end zero (as `resized`). -/
def OsFile.written (f : OsFile) (off : Nat) (d : List w8) : List w8 :=
  let c := f.resized (max f.size (off + d.length))
  c.take off ++ d ++ c.drop (off + d.length)

/-- A `pwrite` of `data` at `off` to the file `f` of inode `i`, as its first step announces it:
the bytes from where it starts or the end, whichever is first (the zero gap before the data
included), to the end of the data, with the values `written` gives them. -/
def OsChange.ofWrite (i : Ino) (f : OsFile) (off : Nat) (data : List w8) : OsChange :=
  { ino := i, kind := .write off data, lo := min off f.size, hi := off + data.length,
    val := fun b => (f.written off data).getD b 0, target := max f.size (off + data.length) }

/-- A resize of the file `f` of inode `i` to `sz`, by `ftruncate` (`trunc`) or by `fallocate`'s
growth, as its first step announces it: zeros from where the old and new sizes part (an extension
reads zeros; a cut zeroes the page cache past the new end); `ftruncate` also zeroes the rest of the
page holding the old end (ext4 zeroes the block holding EOF to its end: `ext4_block_truncate_page`
from `ext4_truncate`, shrinking or at the same size, and from `ext4_setattr`'s growth; the pages
past it are freed or holes), and so to the end of the page holding the larger of the two ends (a
growth's new last page, when past the old end's, is a hole: zeros), `fallocate` only up to its
target (`ext4_zero_partial_blocks`). Measured on C (`notes/axiom-review/eof-page.md`: `trunc-*`,
`trunc-up-past` reading zeros past its new end, `zerotoend`, `pl-trunc-append`; `falloc-in` keeps
the stale tail past its target). **Pending the user's review** (P2 of `eof-page.md`,
2026-11-13). -/
def OsChange.ofResize (i : Ino) (f : OsFile) (sz : Nat) (trunc : Bool) : OsChange :=
  { ino := i, kind := if trunc then .truncate sz else .falloc sz, lo := min f.size sz,
    hi := if trunc then pageEnd (max f.size sz) else max f.size sz, val := fun _ => 0,
    target := sz }

/-- The change is a resize (`ftruncate` or `fallocate`'s growth), not a `pwrite`. -/
def OsChangeKind.isResize : OsChangeKind → Bool
  | .write _ _ => false
  | .truncate _ => true
  | .falloc _ => true

/-- `f` with the change `c` announced as change number `n`: each byte of `[c.lo, c.hi)` gets the
candidate `c.val b`, stamped `n`; a resize's stamp is recorded (`OsFile.rzs`, bookkeeping only). -/
def OsFile.announce (f : OsFile) (c : OsChange) (n : Nat) : OsFile :=
  { f with cand := fun b => if inRange c.lo c.hi b then f.cand b ++ [(c.val b, n)] else f.cand b,
           rzs := if c.kind.isResize then n :: f.rzs else f.rzs }

/-- `f` with the change `c` landed up to `e` (`c.lo ≤ e ≤ c.hi`): the bytes `[c.lo, e)` take their
announced values in the page cache, and the size becomes `sz`; the size range widens to it. -/
def OsFile.land (f : OsFile) (c : OsChange) (e sz : Nat) : OsFile :=
  { f with cache := fun b => if inRange c.lo e b then c.val b else f.cache b,
           size := sz, sizeLo := min f.sizeLo sz, sizeHi := max f.sizeHi sz }

/-- `f` after a successful sync: the size is durable; each byte not under an in-flight change
(`busy`) is durable: its page-cache value in a page that holds a byte below the size, zero in a
page past it (the sync committed the freeing of the blocks a shrink cut off; durable zeros, the
header), its one candidate that value. -/
def OsFile.synced (f : OsFile) (busy : Nat → Prop) [DecidablePred busy] : OsFile :=
  { f with
    cache := fun b => if busy b then f.cache b else diskByte f.cache f.size b,
    cand := fun b => if busy b then f.cand b else [(diskByte f.cache f.size b, 0)],
    sizeLo := f.size, sizeHi := f.size }

end effects

/-! ## Derived facts about a state -/

section derived
variable (st : OsState)

/-- The tree now: the durable tree with the operations since replayed. -/
def OsState.tree : Tree := replay (st.fs.metaLog.map (·.op)) st.fs.treeDur

/-- The file of inode `i`. -/
def OsState.file (i : Ino) : Option OsFile := st.fs.files !! i

/-- The size of the file of `i` (0 if there is none). -/
def OsState.size (i : Ino) : Nat := ((st.file i).map (·.size)).getD 0

/-- The in-flight change on the file of `i` may change its byte `b`: `b` is one it announced. -/
def InflightAt (i : Ino) (b : Nat) : Prop :=
  ∃ t c, st.proc.inflight !! t = some c ∧ c.ino = i ∧ inRange c.lo c.hi b

/-- A change is in flight on the file of `i`. A change's first step requires that none is: at most
one change is in flight on a file (a stuck restriction, the header). -/
def BusyAt (i : Ino) : Prop := ∃ t c, st.proc.inflight !! t = some c ∧ c.ino = i

/-- What `fstat` may give as the size of the file of `i`: its size, or, while a change resizes it,
a size between its size and the change's target. -/
def StatSees (i : Ino) (sz : Nat) : Prop :=
  sz = st.size i ∨ ∃ t c, st.proc.inflight !! t = some c ∧ c.ino = i ∧
    min (st.size i) c.target ≤ sz ∧ sz ≤ max (st.size i) c.target

/-- What a `pread` of `n` bytes at `off` of the file of `i` may return: the bytes up to EOF, for a
size `fstat` could see; each byte the file's, unless an in-flight change may change it, when it is
arbitrary (Linux returns some mix). -/
def ReadSees (i : Ino) (off n : Nat) (r : List w8) : Prop :=
  (∃ sz, StatSees st i sz ∧ r.length = min n (sz - off)) ∧
  ∀ j (h : j < r.length), ¬ InflightAt st i (off + j) →
    ((st.file i).map (·.contents)).bind (·[off + j]?) = some r[j]

/-- `l` is byte `b` of a mapping of the file of `i`. Mappings are disjoint: each lies in cells that
were free when it was made. -/
def MapsTo (l : Loc) (i : Ino) (b : Nat) : Prop :=
  ∃ base m, st.proc.maps !! base = some m ∧ m.ino = i ∧ b < m.len ∧ l = base +ₗ (b : Int)

/-- `l` is a cell of some mapping. -/
def Mapped (l : Loc) : Prop := ∃ i b, MapsTo st l i b

/-- A hole: what a mapped cell holds where a load must be stuck. A literal, not `#()`, so that it
is never a byte whatever the Go context's `intoVal`. -/
def osHole [GooseExts] : val := LitV LitPoison

open Classical in
/-- What byte `b` of a mapping of the file of `i` holds: the file's byte, or a hole past EOF or
where an in-flight change may be changing it. -/
noncomputable def cellVal [GooseExts] [GoGlobalContext] (i : Ino) (b : Nat) : val :=
  match st.file i with
  | some f => if h : b < f.contents.length then
      (if InflightAt st i b then osHole else LitV (LitByte f.contents[b])) else osHole
  | none => osHole

end derived

/-- The heap after a step from `st` to `st'`: every mapping of `st'` shows its file (a cell that was
already mapped keeps its mode; a new one is an ordinary byte cell, `Free`); a cell mapped in `st`
only is gone; every other cell is unchanged. -/
def HeapRendered [GooseExts] [GoGlobalContext] (st st' : OsState)
    (h h' : GMap Loc (NonAtomic val)) : Prop :=
  (∀ l i b, MapsTo st' l i b → Mapped st l →
    ∃ m v0, h !! l = some (m, v0) ∧ h' !! l = some (m, cellVal st' i b)) ∧
  (∀ l i b, MapsTo st' l i b → ¬ Mapped st l → h' !! l = some (Free (cellVal st' i b))) ∧
  (∀ l, ¬ Mapped st' l → Mapped st l → h' !! l = none) ∧
  (∀ l, ¬ Mapped st' l → ¬ Mapped st l → h' !! l = h !! l)

/-! ## State effects -/

section effects2

/-- The file of `i` replaced by `f`. -/
def OsState.setFile (st : OsState) (i : Ino) (f : OsFile) : OsState :=
  { st with fs := { st.fs with files := <[i := f]> st.fs.files } }

/-- The file of `i` replaced by `g n` for the next change number `n`, which is taken: a change
announced. -/
def OsState.stampFile (st : OsState) (i : Ino) (g : Nat → OsFile) : OsState :=
  { st with fs := { st.fs with files := <[i := g (st.fs.stamp + 1)]> st.fs.files,
                               stamp := st.fs.stamp + 1 } }

/-- The process's state replaced. -/
def OsState.setProc (st : OsState) (p : ProcState) : OsState := { st with proc := p }

/-- The node the components `cs` lead to from `n` in `m`. -/
def walk (m : Tree) : Node → List GoString → Option Node
  | n, [] => some n
  | .dir j, c :: cs => match m.entry j c with
    | some n => walk m n cs
    | none => none
  | .file _, _ :: _ => none

open Classical in
/-- What the path `p` names now: a root followed by valid components, walked from the root's
directory (the roots' forms make the split unique: `RootsOk`); nothing for any other path. -/
def OsState.lookup (st : OsState) (p : GoString) : Option Node :=
  if h : ∃ (rj : GoString × Ino) (cs : List GoString), rj ∈ st.fs.roots ∧ (∀ c ∈ cs, NameOk c) ∧
      p = joinPath rj.1 cs then
    walk st.tree (.dir h.choose.2) h.choose_spec.choose
  else none

/-- `p` is a path that may be created, renamed or removed: canonical, strictly in a root's tree. -/
def OsState.TreeName (st : OsState) (p : GoString) : Prop := ∃ rj ∈ st.fs.roots, CanonBelow rj.1 p

/-- `p` is a path of the roots' trees: a root, or a `TreeName`. -/
def OsState.TreePath (st : OsState) (p : GoString) : Prop :=
  (∃ rj ∈ st.fs.roots, rj.1 = p) ∨ st.TreeName p

/-- `p` is a root or an ancestor of one: not empty, and a root is `p` or below it, textually
(`IsUnder`; the roots being canonical and absolute, `RootForm`, such a `p` is `/c₁/…/cₖ`, a prefix of
a root's components). The environment (the header) keeps each an existing directory. -/
def OsState.AtOrAboveRoot (st : OsState) (p : GoString) : Prop :=
  p ≠ [] ∧ ∃ rj ∈ st.fs.roots, IsUnder p rj.1

/-- `p` is a strict ancestor of a root: `/`, or `/c₁/…/cₖ` with `/c₁/…/cₖ/` a prefix of a root
(the roots being canonical and absolute, `RootForm`, these are the ancestors' canonical paths). The
environment (the header) keeps each an existing directory, which no step of the program changes. -/
def OsState.AboveRoot (st : OsState) (p : GoString) : Prop :=
  p = [slashB] ∨ (p ≠ [] ∧ ∃ rj ∈ st.fs.roots, (p ++ [slashB]).IsPrefix rj.1)

/-- The directory `p` is in (its inode) and `p`'s last component, if that directory exists. -/
def OsState.parent (st : OsState) (p : GoString) : Option (Ino × GoString) :=
  match parentOf p with
  | some d => match st.lookup d with
    | some (.dir j) => some (j, baseOf p)
    | _ => none
  | none => none

/-- The directory `p` is in exists. -/
def OsState.ParentDir (st : OsState) (p : GoString) : Prop := ∃ jb, st.parent p = some jb

/-- A read of the directory `df.ino` told of the operation `o`: the names it touches there are no
longer untouched and may be returned again, and those it adds have been seen. -/
def OsDirFd.note (o : MetaOp) (df : OsDirFd) : OsDirFd :=
  match df.rd with
  | .reading u s r =>
    let u' : GoString → Bool := fun b => u b && decide (b ∉ o.touched df.ino)
    let s' : GoString → Bool := fun b => s b || decide (b ∈ o.adds df.ino)
    let r' : GoString → Bool := fun b => r b && decide (b ∉ o.touched df.ino)
    { df with rd := OsDirRead.reading u' s' r' }
  | _ => df

/-- `st` with the metadata call `t` done (after its step). -/
def OsState.metaEnd (st : OsState) (t : Nat) : OsState :=
  { st with proc := { st.proc with calls := GMap.delete t st.proc.calls } }

/-- `st` after the metadata operation `o` of a call that began when the log had `start` entries:
`o` logged (the tree now changes with it), the directory reads told. -/
def OsState.metaDo (st : OsState) (o : MetaOp) (start : Nat) : OsState :=
  { fs := { st.fs with metaLog := st.fs.metaLog ++ [⟨o, start⟩] },
    proc := { st.proc with dfds := GMap.fmap (·.note o) st.proc.dfds } }

/-- `st` with the next inode number taken. -/
def OsState.takeIno (st : OsState) : OsState :=
  { st with fs := { st.fs with nextIno := st.fs.nextIno + 1 } }

/-- `st` with every entry of its log durable. -/
def OsState.commitAll (st : OsState) : OsState :=
  { st with fs := { st.fs with committed := fun y => st.fs.committed y ∨ y < st.fs.metaLog.length } }

/-- A new file: empty. Whether its name survives a crash is the tree's question. -/
def newFile : OsFile := OsFile.ofBytes []

/-- What `open(p)` does before its fd (`st1`), and what the fd will be on (`tgt`): an existing file
(truncated with `trunc`: a resize to 0 announced and landed at once; the `Open` step is stuck
then while a change is in flight on the file, as every change's first step); a new file of a fresh inode, with its `create`
logged (`O_CREAT`, in an existing directory; `start` the call's start); or a directory, opened
read-only without `O_CREAT` or `O_TRUNC` (Linux refuses the rest, `EISDIR`). -/
def OpenEffect (st : OsState) (p : GoString) (acc : Nat) (creat trunc : Bool) (start : Nat)
    (st1 : OsState) (tgt : Node) : Prop :=
  match st.lookup p with
  | some (.dir j) => acc = O_RDONLY ∧ creat = false ∧ trunc = false ∧ st1 = st ∧ tgt = .dir j
  | some (.file i) => (∃ f, st.file i = some f ∧
      st1 = (if trunc then
        st.stampFile i (fun n => let c := OsChange.ofResize i f 0 true; (f.announce c n).land c c.hi 0)
        else st)) ∧
      tgt = .file i
  | none => creat = true ∧ ∃ j b, st.parent p = some (j, b) ∧
      st1 = ((st.setFile st.fs.nextIno newFile).takeIno).metaDo (.create j b st.fs.nextIno) start ∧
      tgt = .file st.fs.nextIno

/-- The path `p` is an empty directory, of inode `j`. -/
def EmptyDir (st : OsState) (p : GoString) (j : Ino) : Prop :=
  st.lookup p = some (.dir j) ∧ ∀ b, st.tree.entry j b = none

/-- A `rename(2)` that Linux performs (all else fails): of an existing entry to another name in an
existing directory; a file onto nothing or onto a file (replaced: an fd of the replaced file keeps
it); a directory onto nothing or onto an empty directory (replaced), not into its own tree. -/
def RenameOk (st : OsState) (s t : GoString) : Prop :=
  s ≠ t ∧ st.ParentDir s ∧ st.ParentDir t ∧
  match st.lookup s with
  | some (.file _) => ∀ j, st.lookup t ≠ some (.dir j)
  | some (.dir _) => ¬ IsUnder s t ∧ (st.lookup t = none ∨ ∃ j, EmptyDir st t j)
  | none => False

/-- The rename of `s` to `t`, as logged. -/
def RenameOp (st : OsState) (s t : GoString) (o : MetaOp) : Prop :=
  ∃ js bs jt bt n, st.parent s = some (js, bs) ∧ st.parent t = some (jt, bt) ∧
    st.lookup s = some n ∧ o = .rename js bs jt bt n (st.lookup t)

/-- Whether `b` is now a name in the directory `j`. -/
def present (st : OsState) (j : Ino) (b : GoString) : Bool :=
  decide (NameOk b) && (st.tree.entry j b).isSome

/-- A directory fd's read, as its next step finds it: begun now if it was not. -/
def OsDirRead.cur (st : OsState) (j : Ino) :
    OsDirRead → Option ((GoString → Bool) × (GoString → Bool) × (GoString → Bool))
  | .idle => some (present st j, present st j, fun _ => false)
  | .reading u s r => some (u, s, r)
  | .done => none

end effects2

/-! ## The step relation -/

section step
variable [GooseExts] [GoGlobalContext]

/-- The token of an in-flight change, an opaque value of the extension: a program cannot forge one,
and there are always fresh ones. -/
abbrev osTokV (t : Nat) : val := ExtV (extVal fsExt t)

/-- A result and an errno, as the Go wrapper's models take them apart. -/
abbrev osRes (v : val) (e : w64) : Expr := Val (PairV v (#e))

/-- An open fd of a file and its description. -/
def FdOpen (st : OsState) (fd : w64) (d : OsFd) : Prop := st.proc.fds !! fd = some d

/-- `fd` is free: no fd of a file or of a directory has it. -/
def FdFree (st : OsState) (fd : w64) : Prop :=
  0 ≤ fd.toInt ∧ st.proc.fds !! fd = none ∧ st.proc.dfds !! fd = none ∧ st.proc.ofds !! fd = none

/-- `st` with the fd `fd` of a directory outside the roots' trees open. -/
def OsState.addOfd (st : OsState) (fd : w64) : OsState :=
  { st with proc := { st.proc with ofds := <[fd := ()]> st.proc.ofds } }

/-- `st` with the fd `fd` of a directory outside the roots' trees closed. -/
def OsState.delOfd (st : OsState) (fd : w64) : OsState :=
  { st with proc := { st.proc with ofds := GMap.delete fd st.proc.ofds } }

/-- The flags `Open` supports: an access mode and `O_CREAT`, `O_TRUNC`, `O_CLOEXEC`. -/
def OpenFlagsOk (fl : Nat) : Prop :=
  fl % 4 ≠ 3 ∧ fl - fl % 4 ∈ [0, O_CREAT, O_TRUNC, O_CREAT + O_TRUNC, O_CLOEXEC,
    O_CREAT + O_CLOEXEC, O_TRUNC + O_CLOEXEC, O_CREAT + O_TRUNC + O_CLOEXEC]

/-- `st` with the in-flight change `t` done. -/
def OsState.doneInflight (st : OsState) (t : Nat) : OsState :=
  { st with proc := { st.proc with inflight := GMap.delete t st.proc.inflight } }

/-- `st` with `c` in flight under the token `t`. -/
def OsState.addInflight (st : OsState) (t : Nat) (c : OsChange) : OsState :=
  { st with proc := { st.proc with inflight := <[t := c]> st.proc.inflight } }

/-- `Open`'s outside case (`IsFsStep`, `"Open"`): `(tok, #p, #flags) ↦ (#fd, #errno)` for a strict
ancestor `p` of a root, read-only (`O_RDONLY`, with or without `O_CLOEXEC`), a call begun by
`CallBegin`: the call ends, and a fresh fd of a directory outside the trees is open (`addOfd`), or
any nonzero errno. -/
abbrev OpenOutside (v : val) (st : OsState) (e' : Expr) (st' : OsState) : Prop :=
  ∃ (p : GoString) (fl : w64) (t start : Nat),
    v = PairV (osTokV t) (PairV (#p) (#fl)) ∧ ¬ st.TreePath p ∧ st.AboveRoot p ∧
    (fl.toNat = O_RDONLY ∨ fl.toNat = O_CLOEXEC) ∧ st.proc.calls !! t = some start ∧
    ((∃ fd : w64, FdFree st fd ∧ st' = (st.metaEnd t).addOfd fd ∧ e' = osRes (#fd) 0) ∨
     (∃ e : w64, e ≠ 0 ∧ st' = st.metaEnd t ∧ e' = osRes (#(-1 : w64)) e))

open Classical in
/-- The steps of the operations; the heap is `HeapRendered` (`FsStep`). Each case is a disjunction:
the success branch and its premises, then the failure branch (any nonzero errno). -/
def IsFsStep (op : String) (v : val) (st : OsState) (e' : Expr) (st' : OsState) : Prop :=
  match op with
  /- `open(p, flags)` of a path of the roots' trees, a call begun by `CallBegin` (`tok`):
  `(tok, #p, #flags) ↦ (#fd, #errno)`, as `OpenEffect` says, with a fresh fd (of a file, on its
  inode, or of a directory, on its inode). On failure, the effect may or may not have happened,
  without the fd.
  **Outside case** (the second disjunct; 2026-11-13, **pending the user's review**,
  `notes/wal-fsext-models-review.md`, "Above-root Stat/Open"): `open(p, O_RDONLY)` of a strict
  ancestor of a root (`AboveRoot`: `/`, or a directory above a root; the environment keeps each an
  existing directory that no step changes, so the walk to it meets no moved directory): the call
  ends, and a fresh fd of a directory outside the trees (`ofds`) is open, of which the model knows
  nothing else (`OutSync`, `OutClose`; every other step on it is stuck), or any errno, nothing else
  changing. Any other flags there are stuck. Go example:
  `examples/osfs/semantics/model_os_open_above.go`.
  **`ENOENT`** (2026-11-14, decided provisionally, **pending the user's review**; plan
  `notes/wal-fsext-plan.md` §10): a failure of the first disjunct returns `ENOENT` only when `p` does not
  resolve at the step (`st0.lookup p = none`): Linux's `ENOENT` is a component's lookup finding no
  entry, or a dead directory, and with no directory renamed during the call the path did not resolve at
  that instant, where the step may be placed. Go example: `examples/osfs/semantics/meta_enoent.go`. -/
  | "Open" => (∃ (p : GoString) (fl : w64) (t start : Nat),
      v = PairV (osTokV t) (PairV (#p) (#fl)) ∧ st.TreePath p ∧ OpenFlagsOk fl.toNat ∧
      st.proc.calls !! t = some start ∧
      let acc := fl.toNat % 4
      let creat := decide (fl.toNat / O_CREAT % 2 = 1)
      let trunc := decide (fl.toNat / O_TRUNC % 2 = 1)
      let st0 := st.metaEnd t
      (trunc = true → ∀ i, st0.lookup p = some (.file i) → ¬ BusyAt st0 i) ∧
      ((∃ (st1 : OsState) (tgt : Node) (fd : w64),
          OpenEffect st0 p acc creat trunc start st1 tgt ∧ FdFree st fd ∧
          st' = (match tgt with
            | .file i => st1.setProc { st1.proc with
                fds := <[fd := ⟨i, acc ≠ O_WRONLY, acc ≠ O_RDONLY⟩]> st1.proc.fds }
            | .dir j => st1.setProc { st1.proc with
                dfds := <[fd := ⟨j, .idle⟩]> st1.proc.dfds }) ∧
          e' = osRes (#fd) 0) ∨
       (∃ e : w64, e ≠ 0 ∧ (e = ENOENT → st0.lookup p = none) ∧ e' = osRes (#(-1 : w64)) e ∧
          (st' = st0 ∨ ∃ tgt, OpenEffect st0 p acc creat trunc start st' tgt)))) ∨
    OpenOutside v st e' st'
  /- `pread(fd, n, off)`: `(#fd, #off, #n) ↦ (#data, #errno)`, as `ReadSees` allows. On success,
  a non-empty prefix (Linux returns a short count when page allocation fails part way, F4), or
  nothing at EOF; on failure, any prefix. -/
  | "PRead" => ∃ (fd off n : w64) (d : OsFd) (r : List w8), v = PairV (#fd) (PairV (#off) (#n)) ∧
      FdOpen st fd d ∧ d.readable ∧ 0 ≤ off.toInt ∧ ReadSees st d.ino off.toNat n.toNat r ∧
      st' = st ∧
      ((∃ k, k ≤ r.length ∧ (0 < k ∨ r = []) ∧ e' = osRes (#(r.take k)) 0) ∨
       ∃ (k : Nat) (e : w64), k ≤ r.length ∧ e ≠ 0 ∧ e' = osRes (#(r.take k)) e)
  /- The first step of `pwrite(fd, data, off)`: `(#fd, #off, #data) ↦ token`. It makes no system
  call and cannot fail; it announces the write (all of its data, as the next change). Stuck while
  another change is in flight on the file, and on empty data (Go's `WriteAt` and `Write` never
  issue an empty `pwrite`). -/
  | "PWriteStart" => ∃ (fd off : w64) (data : List w8) (d : OsFd) (f : OsFile) (t : Nat),
      v = PairV (#fd) (PairV (#off) (#data)) ∧ FdOpen st fd d ∧ d.writable ∧ 0 ≤ off.toInt ∧
      data ≠ [] ∧ st.file d.ino = some f ∧ ¬ BusyAt st d.ino ∧
      st.proc.inflight !! t = none ∧ st.proc.calls !! t = none ∧
      (let c := OsChange.ofWrite d.ino f off.toNat data
       st' = (st.stampFile d.ino (f.announce c)).addInflight t c) ∧
      e' = Val (osTokV t)
  /- The second step: `token ↦ (#written, #errno)`. A prefix of `k` bytes of the data is
  written: with errno 0, all of it or a non-empty part (a short write, F6); with a nonzero errno,
  any prefix. Whatever the errno, the prefix is empty, the whole write, or ends on a 4096-byte
  page boundary of the file (**page cuts**, the header). It lands the announced bytes up to the
  end of what was written (the zero gap included), none if nothing was; the size grows to that
  end. **Nothing lands at or past `maxBytes`** (`k = 0 ∨ off + k ≤ maxBytes`): a write starting
  there fails with nothing landed (`EFBIG`), one crossing it is cut there (a short count, page-aligned;
  `data_maxbytes.go`, pending the user's review). -/
  | "PWriteFinish" => ∃ (t : Nat) (c : OsChange) (off : Nat) (data : List w8) (f : OsFile)
      (k : Nat) (e : w64), v = osTokV t ∧ st.proc.inflight !! t = some c ∧
      c.kind = .write off data ∧ st.file c.ino = some f ∧ k ≤ data.length ∧
      ((k = data.length ∨ 0 < k) ∧ e = 0 ∨ e ≠ 0) ∧
      (k = 0 ∨ k = data.length ∨ (off + k) % osPageSize = 0) ∧ (k = 0 ∨ off + k ≤ maxBytes) ∧
      (let w := if k = 0 then c.lo else off + k
       st' = (st.doneInflight t).setFile c.ino (f.land c w (max f.size w))) ∧
      e' = osRes (#(W64 k)) e
  /- `fstat(fd)`'s size: `#fd ↦ (#size, #errno)`, as `StatSees` allows. -/
  | "Fstat" => ∃ (fd : w64) (d : OsFd) (sz : Nat), v = #fd ∧ FdOpen st fd d ∧
      StatSees st d.ino sz ∧ st' = st ∧
      (e' = osRes (#(W64 sz)) 0 ∨ ∃ e : w64, e ≠ 0 ∧ e' = osRes (#(0 : w64)) e)
  /- The first step of `ftruncate(fd, sz)`: `(#fd, #sz) ↦ token`. It makes no system call and
  cannot fail; it announces the resize. Stuck while another change is in flight on the file. -/
  | "FtruncateStart" => ∃ (fd sz : w64) (t : Nat) (d : OsFd) (f : OsFile), v = PairV (#fd) (#sz) ∧
      FdOpen st fd d ∧ d.writable ∧ 0 ≤ sz.toInt ∧ ¬ BusyAt st d.ino ∧ st.file d.ino = some f ∧
      st.proc.inflight !! t = none ∧ st.proc.calls !! t = none ∧
      (let c := OsChange.ofResize d.ino f sz.toNat true
       st' = (st.stampFile d.ino (f.announce c)).addInflight t c) ∧
      e' = Val (osTokV t)
  /- The second step: `token ↦ #errno`. It lands all of the announced bytes and the new size; on
  failure the file may or may not be resized. A size past `maxBytes` fails with no change (`EFBIG`,
  `data_maxbytes.go`, pending the user's review); the bytes the first step announced stay among the
  candidates, as on any failure. -/
  | "FtruncateFinish" => ∃ (t : Nat) (c : OsChange) (sz : Nat) (f : OsFile), v = osTokV t ∧
      st.proc.inflight !! t = some c ∧ c.kind = .truncate sz ∧ st.file c.ino = some f ∧
      (let st0 := st.doneInflight t
       let st1 := st0.setFile c.ino (f.land c c.hi c.target)
       c.target ≤ maxBytes ∧ st' = st1 ∧ e' = Val (#(0 : w64)) ∨
       ∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧ (st' = st0 ∨ c.target ≤ maxBytes ∧ st' = st1))
  /- `fsync(fd)` and `fdatasync(fd)` of a file alike: `#fd ↦ #errno`. Success makes every byte
  not under an in-flight change durable (`OsFile.synced`); a failure changes nothing (no failed
  writeback, the header: whatever it wrote, a crash may keep anyway). A failure is never `EINTR`:
  `fsync(2)` on a local ext4 file does not return it, and Go's `File.Sync` retries `EINTR`, so a
  hidden failed attempt behind a successful `Sync` would be a run Linux does not have. It commits
  no name. -/
  | "Fsync" => ∃ (fd : w64) (d : OsFd) (f : OsFile), v = #fd ∧ FdOpen st fd d ∧
      st.file d.ino = some f ∧
      (st' = st.setFile d.ino (f.synced (InflightAt st d.ino ·)) ∧ e' = Val (#(0 : w64)) ∨
       ∃ e : w64, e ≠ 0 ∧ e ≠ EINTR ∧ e' = Val (#e) ∧ st' = st)
  /- `flock(fd, how)`: `(#fd, #how) ↦ #errno`. Trivial: the lock state is not modelled, so the
  errno is anything; only the fd must be open. -/
  | "Flock" => ∃ (fd how e : w64) (d : OsFd), v = PairV (#fd) (#how) ∧ FdOpen st fd d ∧
      st' = st ∧ e' = Val (#e)
  /- `close(fd)` of a file: `#fd ↦ #errno`. The fd is freed whatever the errno. -/
  | "Close" => ∃ (fd e : w64) (d : OsFd), v = #fd ∧ FdOpen st fd d ∧
      st' = st.setProc { st.proc with fds := GMap.delete fd st.proc.fds } ∧ e' = Val (#e)
  /- `mmap(nil, len, prot, flags, fd, off)`: `(#fd, #off, #len, #prot, #flags) ↦ (#base, #errno)`.
  The cells are fresh and page-aligned; `HeapRendered` creates them. -/
  | "Mmap" => ∃ (fd off len prot fl : w64) (d : OsFd),
      v = PairV (#fd) (PairV (#off) (PairV (#len) (PairV (#prot) (#fl)))) ∧
      FdOpen st fd d ∧ d.readable ∧ off = 0 ∧ 0 < len.toInt ∧ prot.toNat = PROT_READ ∧
      (fl.toNat = MAP_SHARED ∨ fl.toNat = MAP_SHARED + MAP_POPULATE) ∧
      ((∃ base : Loc, 0 < base.addr ∧ (osPageSize : Int) ∣ base.addr ∧
          st.proc.maps !! base = none ∧
          st' = st.setProc { st.proc with maps := <[base := ⟨d.ino, len.toNat⟩]> st.proc.maps } ∧
          e' = osRes (#base) 0) ∨
       (∃ e : w64, e ≠ 0 ∧ st' = st ∧ e' = osRes (#null) e))
  /- `munmap` of a whole mapping, as Go's `unix.Munmap(b)` takes it: `(#ptr, #len, #cap) ↦ #errno`. -/
  | "Munmap" => ∃ (base : Loc) (len cap : w64) (m : OsMap),
      v = PairV (#base) (PairV (#len) (#cap)) ∧
      st.proc.maps !! base = some m ∧ len.toNat = m.len ∧ cap.toNat = m.len ∧
      let st1 := st.setProc { st.proc with maps := GMap.delete base st.proc.maps }
      (st' = st1 ∧ e' = Val (#(0 : w64)) ∨
       ∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧ (st' = st ∨ st' = st1))
  /- What `fd` is: `#fd ↦ #0` for a file's fd, `#1` for a directory's, `#2` for a directory's
  outside the roots' trees (2026-11-13); stuck on any other. A query of the model, not a system
  call (`File.Sync`'s and `File.Close`'s models ask it). -/
  | "FdKind" => ∃ fd : w64, v = #fd ∧ st' = st ∧
      ((∃ d, st.proc.fds !! fd = some d) ∧ e' = Val (#(0 : w64)) ∨
       st.proc.fds !! fd = none ∧ (∃ df, st.proc.dfds !! fd = some df) ∧ e' = Val (#(1 : w64)) ∨
       st.proc.fds !! fd = none ∧ st.proc.dfds !! fd = none ∧ st.proc.ofds !! fd = some () ∧
         e' = Val (#(2 : w64)))
  /- `fsync(fd)` of a directory outside the roots' trees (`ofds`, `Open`'s outside case):
  `#fd ↦ #errno`, any errno (`0` included), nothing changing: the model makes no claim about what
  it makes durable (on C it commits the journal of the directory's filesystem, which is no less
  than nothing). **Pending the user's review** (2026-11-13). Go example:
  `examples/osfs/semantics/model_os_open_above.go`. -/
  | "OutSync" => ∃ (fd e : w64), v = #fd ∧ st.proc.ofds !! fd = some () ∧ st' = st ∧
      e' = Val (#e)
  /- `close(fd)` of a directory outside the roots' trees: `#fd ↦ #errno`; the fd is freed whatever
  the errno. **Pending the user's review** (2026-11-13). -/
  | "OutClose" => ∃ (fd e : w64), v = #fd ∧ st.proc.ofds !! fd = some () ∧ st' = st.delOfd fd ∧
      e' = Val (#e)
  /- The start of a system call on a path (`open`, `rename`, `unlink`, `rmdir`, `mkdir`, `lstat`):
  `#() ↦ tok`, a token recording the length of the log now (the operations that have taken effect
  before the call began: the journal has them before it, and the call's walk of its path sees them).
  The call's step ends it. Not a system call; calls overlap freely, but a directory's rename waits
  for every other one (see `Rename`). A trusted model makes one `CallBegin` per system-call attempt
  (inside Go's `EINTR` retry loop), before the attempt enters the kernel, and passes its token to
  that attempt's step only. A model that returns without the step leaves the call in flight for
  good, which makes every later directory rename stuck. -/
  /- Where the path `p` is: `#p ↦ #1` for a `TreeName` (strictly below a root), `#0` for a root,
  `#2` for a strict ancestor of a root (`AboveRoot`: `/` included); stuck on any other path. A query
  of the model, not a system call (no state changes): `os.MkdirAll`'s model asks it, so that at a
  root or above it runs Go's body with no step on the paths the extension gives no meaning (the
  roots and their ancestors are existing directories, the environment: Go's `stat` there succeeds,
  its `mkdir` fails, neither changes anything); `os.Stat`'s and `os.Lstat`'s ask it, and answer at a
  strict ancestor with no step. **Pending the user's review** (2026-11-13,
  `notes/wal-fsext-models-review.md`, finding 1 and "Above-root Stat/Open"). Go examples:
  `examples/osfs/semantics/model_os_mkdirall_above.go`, `model_os_stat_above.go`. -/
  | "PathKind" => ∃ p : GoString, v = #p ∧ st' = st ∧
      (st.TreeName p ∧ e' = Val (#(1 : w64)) ∨
       ¬ st.TreeName p ∧ (∃ rj ∈ st.fs.roots, rj.1 = p) ∧ e' = Val (#(0 : w64)) ∨
       ¬ st.TreePath p ∧ st.AboveRoot p ∧ e' = Val (#(2 : w64)))
  | "CallBegin" => ∃ t : Nat, v = #() ∧ st.proc.calls !! t = none ∧
      st.proc.inflight !! t = none ∧
      st' = st.setProc { st.proc with calls := <[t := st.fs.metaLog.length]> st.proc.calls } ∧
      e' = Val (osTokV t)
  /- `fsync(fd)` of a directory: `#fd ↦ #errno`. Success makes every logged operation durable
  (ext4 commits the whole journal for a file that is not regular); a failure guarantees nothing
  more (whatever it committed, a crash may keep anyway). -/
  | "DirSync" => ∃ (fd : w64) (df : OsDirFd), v = #fd ∧ st.proc.dfds !! fd = some df ∧
      ((st' = st.commitAll ∧ e' = Val (#(0 : w64))) ∨
       ∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧ st' = st)
  /- `close(fd)` of a directory: `#fd ↦ #errno`; the fd is freed whatever the errno. -/
  | "DirClose" => ∃ (fd e : w64) (df : OsDirFd), v = #fd ∧ st.proc.dfds !! fd = some df ∧
      st' = st.setProc { st.proc with dfds := GMap.delete fd st.proc.dfds } ∧ e' = Val (#e)
  /- One step of `Readdirnames(-1)` on a directory fd: `#fd ↦ (#name, #done, #errno)`. A name that
  the directory had at some point since the read began, not returned since it was last touched; or
  the end, once it has returned every name the directory had when the read began, still has, and
  that no operation touched since (POSIX's `readdir`: an entry added or removed meanwhile may or may
  not be returned); or an errno, the read unchanged, `ENOENT` only for a removed directory (not
  reachable from a root: Linux's `iterate_dir` answers `ENOENT` for a dead directory, and only then;
  2026-11-14, decided provisionally, **pending the user's review**, Go example
  `examples/osfs/semantics/meta_enoent.go`). After the end, a second read is stuck. A removed
  directory has no names. -/
  | "DirReadNext" => ∃ (fd : w64) (df : OsDirFd) (u s r : GoString → Bool), v = #fd ∧
      st.proc.dfds !! fd = some df ∧ df.rd.cur st df.ino = some (u, s, r) ∧
      ((∃ b, s b = true ∧ r b = false ∧
          st' = st.setProc { st.proc with dfds := <[fd := { df with
            rd := .reading u s (fun x => r x || decide (x = b)) }]> st.proc.dfds } ∧
          e' = Val (PairV (#b) (PairV (#(0 : w64)) (#(0 : w64))))) ∨
       ((∀ b, u b = true → present st df.ino b = true → r b = true) ∧
          st' = st.setProc { st.proc with dfds := <[fd := { df with rd := .done }]> st.proc.dfds } ∧
          e' = Val (PairV (#([] : GoString)) (PairV (#(1 : w64)) (#(0 : w64))))) ∨
       (∃ e : w64, e ≠ 0 ∧ (e = ENOENT → ¬ Reach st.fs.roots st.tree df.ino) ∧
          st' = st.setProc { st.proc with dfds := <[fd := { df with
            rd := .reading u s r }]> st.proc.dfds } ∧
          e' = Val (PairV (#([] : GoString)) (PairV (#(0 : w64)) (#e)))))
  /- `lstat(p)`'s "is it a directory", as `os.Rename` asks it of its destination:
  `#p ↦ (#isDir, #errno)`. `#1` only for a directory, with a nonzero errno, the one `os.Rename`
  returns then; `#0` otherwise, and for a directory too (the `lstat` failed: `Rename`'s model then
  goes on to `rename(2)`, as Go does). -/
  | "LstatDir" => ∃ (p : GoString) (isDir e : w64) (t start : Nat),
      v = PairV (osTokV t) (#p) ∧ st.TreePath p ∧ st.proc.calls !! t = some start ∧
      st' = st.metaEnd t ∧
      ((∃ j, st.lookup p = some (.dir j)) ∧ isDir = 1 ∧ e ≠ 0 ∨ isDir = 0) ∧
      e' = Val (PairV (#isDir) (#e))
  /- `rename(2)` of a call (`tok`, from `CallBegin`): `(tok, #s, #t) ↦ #errno`. As `RenameOk` says,
  or a no-op on an entry renamed to itself; any case may fail, a failure with or without the effect.
  Open fds of a moved file or directory keep it (they hold its inode). A rename of a directory is
  stuck while any other call on a path is in flight: Linux walks a path a component at a time,
  without locking the directories it has passed, so a call walking through a directory being moved
  may find a path that no single tree of the log has; the model resolves a path at its step, so it
  excludes that overlap. -/
  | "Rename" => ∃ (s t : GoString) (k start : Nat), v = PairV (osTokV k) (PairV (#s) (#t)) ∧
      st.TreeName s ∧ st.TreeName t ∧ st.proc.calls !! k = some start ∧
      ((∃ j, st.lookup s = some (.dir j)) → ∀ k' start', st.proc.calls !! k' = some start' → k' = k) ∧
      let st0 := st.metaEnd k
      ((RenameOk st s t ∧ ∃ o, RenameOp st s t o ∧
          (st' = st0.metaDo o start ∧ e' = Val (#(0 : w64)) ∨
           ∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧ (st' = st0 ∨ st' = st0.metaDo o start))) ∨
       (s = t ∧ st.lookup s ≠ none ∧ st' = st0 ∧ e' = Val (#(0 : w64))) ∨
       (∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧ st' = st0))
  /- `unlink(2)` of a metadata call: `(tok, #p) ↦ #errno`. A file's name is removed (its fds keep
  the file, which stays in `files`); any case may fail, a failure with or without the effect. -/
  | "Unlink" => ∃ (p : GoString) (k start : Nat), v = PairV (osTokV k) (#p) ∧ st.TreeName p ∧
      st.proc.calls !! k = some start ∧
      let st0 := st.metaEnd k
      ((∃ i j b, st.lookup p = some (.file i) ∧ st.parent p = some (j, b) ∧
          (st' = st0.metaDo (.remove j b (.file i)) start ∧ e' = Val (#(0 : w64)) ∨
           ∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧
            (st' = st0 ∨ st' = st0.metaDo (.remove j b (.file i)) start))) ∨
       (∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧ st' = st0))
  /- `rmdir(2)` of a metadata call: `(tok, #p) ↦ #errno`. An empty directory is removed (an fd on it
  keeps it, empty); any case may fail, a failure with or without the effect. -/
  | "Rmdir" => ∃ (p : GoString) (k start : Nat), v = PairV (osTokV k) (#p) ∧ st.TreeName p ∧
      st.proc.calls !! k = some start ∧
      let st0 := st.metaEnd k
      ((∃ j' j b, EmptyDir st p j' ∧ st.parent p = some (j, b) ∧
          (st' = st0.metaDo (.remove j b (.dir j')) start ∧ e' = Val (#(0 : w64)) ∨
           ∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧
            (st' = st0 ∨ st' = st0.metaDo (.remove j b (.dir j')) start))) ∨
       (∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧ st' = st0))
  /- `mkdir(2)` of a metadata call: `(tok, #p) ↦ #errno`. A new directory of a fresh inode where
  nothing is, in an existing directory; any case may fail, a failure with or without the effect. -/
  | "Mkdir" => ∃ (p : GoString) (k start : Nat), v = PairV (osTokV k) (#p) ∧ st.TreeName p ∧
      st.proc.calls !! k = some start ∧
      let st0 := st.metaEnd k
      let o (j : Ino) (b : GoString) := MetaOp.mkdir j b st.fs.nextIno
      ((∃ j b, st.lookup p = none ∧ st.parent p = some (j, b) ∧
          (st' = st0.takeIno.metaDo (o j b) start ∧ e' = Val (#(0 : w64)) ∨
           ∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧
            (st' = st0 ∨ st' = st0.takeIno.metaDo (o j b) start))) ∨
       (∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧ st' = st0))
  /- The first step of `fallocate(fd, 0, off, len)`: `(#fd, #off, #len) ↦ token`, a resize to
  `max size (off + len)` in flight (its visible effect is `ftruncate`'s to that size, zeros past the
  end announced, but only up to its target, `OsChange.ofResize`; the blocks it allocates are not
  modelled). Stuck while another change is in
  flight on the file, on a negative offset, or on a length not above 0. -/
  | "FallocStart" => ∃ (fd off len : w64) (t : Nat) (d : OsFd) (f : OsFile),
      v = PairV (#fd) (PairV (#off) (#len)) ∧ FdOpen st fd d ∧ d.writable ∧ 0 ≤ off.toInt ∧
      0 < len.toInt ∧ ¬ BusyAt st d.ino ∧ st.file d.ino = some f ∧ st.proc.inflight !! t = none ∧
      st.proc.calls !! t = none ∧
      (let c := OsChange.ofResize d.ino f (max f.size (off.toNat + len.toNat)) false
       st' = (st.stampFile d.ino (f.announce c)).addInflight t c) ∧
      e' = Val (osTokV t)
  /- The second step: `token ↦ #errno`. It lands all of the announced bytes (zeros from the old
  end) and the new size; on failure, a prefix of them, the size grown to the prefix's end (ext4
  grows the file as each chunk is allocated). A target past `maxBytes` fails with no change
  (`EFBIG`, `data_maxbytes.go`, pending the user's review). -/
  | "FallocFinish" => ∃ (t : Nat) (c : OsChange) (sz : Nat) (f : OsFile), v = osTokV t ∧
      st.proc.inflight !! t = some c ∧ c.kind = .falloc sz ∧ st.file c.ino = some f ∧
      (let st0 := st.doneInflight t
       c.target ≤ maxBytes ∧ st' = st0.setFile c.ino (f.land c c.hi c.target) ∧ e' = Val (#(0 : w64)) ∨
       ∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧
         (st' = st0 ∨ c.target ≤ maxBytes ∧ ∃ w, c.lo ≤ w ∧ w ≤ c.hi ∧
           st' = st0.setFile c.ino (f.land c w w)))
  /- `fallocate(fd, FALLOC_FL_KEEP_SIZE, off, len)`: `(#fd, #off, #len) ↦ #errno`. No change: the
  blocks it allocates past the end are unwritten extents, which read as zeros until written, as a
  page with no block does (durable zeros, the header); any errno. Stuck on a negative offset or a
  length not above 0. -/
  | "FallocKeep" => ∃ (fd off len e : w64) (d : OsFd),
      v = PairV (#fd) (PairV (#off) (#len)) ∧
      FdOpen st fd d ∧ d.writable ∧ 0 ≤ off.toInt ∧ 0 < len.toInt ∧ st' = st ∧ e' = Val (#e)
  /- `fcntl(fd, F_OFD_SETLK[W], ...)`: `(#fd, #cmd) ↦ #errno`. Trivial, as `Flock`: the lock state
  is not modelled, so the errno is anything. -/
  | "OfdLock" => ∃ (fd cmd e : w64) (d : OsFd), v = PairV (#fd) (#cmd) ∧ FdOpen st fd d ∧
      st' = st ∧ e' = Val (#e)
  | _ => False

/-- The cells a new mapping takes are free, in `(0, maxAddr]`. -/
def MapsFresh (st st' : OsState) (h : GMap Loc (NonAtomic val)) : Prop :=
  ∀ base m, st'.proc.maps !! base = some m → st.proc.maps !! base = none →
    base.addr + m.len ≤ maxAddr ∧ ∀ k < m.len, h !! (base +ₗ (k : Int)) = none

/-- The step relation: an operation's step, the heap rendered from the new state. -/
def FsStep (op : String) (v : val) (h : GMap Loc (NonAtomic val)) (st : OsState) (_g : Unit)
    (e' : Expr) (h' : GMap Loc (NonAtomic val)) (st' : OsState) (_g' : Unit) : Prop :=
  IsFsStep op v st e' st' ∧ MapsFresh st st' h ∧ HeapRendered st st' h h'

end step

/-! ## Crash -/

/-- `f'` is what a machine crash may leave of the file `f` of inode `i`: a size between the
smallest and the largest it had since its last successful sync, or between such a size and the
target of the change in flight, and never past `maxBytes` (a size the file had: no step makes one
larger, `data_maxbytes.go`, pending the user's review); each byte
any one of its crash candidates, each independently (its bytes past the size included), or zero
at or past the smallest size since the last sync (writeback zeroes the page holding the end past
the size of the moment, the header; **pending the user's review**); all of it on disk (`ofDisk`:
the pages past the size durable zeros). -/
def CrashFile (st : OsState) (i : Ino) (f f' : OsFile) : Prop :=
  ∃ (sz : Nat) (img : Nat → w8),
    ((f.sizeLo ≤ sz ∨ ∃ t c, st.proc.inflight !! t = some c ∧ c.ino = i ∧ c.target ≤ sz) ∧
     (sz ≤ f.sizeHi ∨ ∃ t c, st.proc.inflight !! t = some c ∧ c.ino = i ∧ sz ≤ c.target)) ∧
    sz ≤ maxBytes ∧
    (∀ b, (∃ s, (img b, s) ∈ f.cand b) ∨ (f.sizeLo ≤ b ∧ img b = 0)) ∧ f' = OsFile.ofDisk img sz

/-- The file `i` is named in the tree `m`. -/
def Named (m : Tree) (i : Ino) : Prop := ∃ j b, m.entry j b = some (.file i)

/-- A machine crash: the roots stay; the tree is the durable one with a set of the logged operations
replayed in log order, a set that holds the committed ones and is closed under `Follows` (what the
journal may have on disk), all of it durable; every file it names is what a crash may leave of its
file (`CrashFile`); every other file is gone; the process has nothing open or in flight. -/
def MachineCrash (st st' : OsState) : Prop :=
  st'.proc = ProcState.empty ∧ st'.fs.roots = st.fs.roots ∧ st'.fs.metaLog = [] ∧
  (∀ y, ¬ st'.fs.committed y) ∧ st'.fs.nextIno = st.fs.nextIno ∧ st'.fs.stamp = st.fs.stamp ∧
  (∃ S : Nat → Prop, (∀ x, S x → x < st.fs.metaLog.length) ∧ (∀ y, st.fs.committed y → S y) ∧
    Closed st.fs.metaLog S ∧ st'.fs.treeDur = replay (keptOps st.fs.metaLog S) st.fs.treeDur) ∧
  ∀ i, (Named st'.fs.treeDur i →
      ∃ f f', st.fs.files !! i = some f ∧ CrashFile st i f f' ∧ st'.fs.files !! i = some f') ∧
    (¬ Named st'.fs.treeDur i → st'.fs.files !! i = none)

/-- A crash: of the machine (a process's restart is one, by the environment's assumption). -/
def OsCrash (st st' : OsState) : Prop := MachineCrash st st'

/-- A state a program may start in: the process has nothing open; nothing logged or committed; the
roots and the tree well formed; every inode the tree names is a file, every file named (no orphan
at boot) and all of it on disk (the environment's "durable at first start"), none larger than
`maxBytes` (no file of C is, `data_maxbytes.go`); every inode in use below `nextIno`. -/
def FsInit (st : OsState) : Prop :=
  st.proc = ProcState.empty ∧ st.fs.metaLog = [] ∧ (∀ y, ¬ st.fs.committed y) ∧
  RootsOk st.fs.roots ∧ TreeWf st.fs.roots st.fs.treeDur ∧
  (∀ i, Named st.fs.treeDur i → st.fs.files !! i ≠ none) ∧
  (∀ i f, st.fs.files !! i = some f → Named st.fs.treeDur i ∧
    ∃ img sz, sz ≤ maxBytes ∧ f = OsFile.ofDisk img sz) ∧
  (∀ i, i ∈ st.fs.files → i < st.fs.nextIno) ∧ (∀ j, j ∈ st.fs.treeDur → j < st.fs.nextIno)

instance fs_semantics : ExtSemantics fsExt where
  step := FsStep
  crash := OsCrash

end Fs
end Perennial

end
