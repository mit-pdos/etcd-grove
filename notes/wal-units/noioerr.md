# Unit `noioerr`: no I/O errors on chosen files (`NoIoErr`)

Branch `wal-c-noioerr` (base `origin/wal-int`). The user's decision (2026-11-15): etcd's server calls
`lg.Panic` when certain WAL operations fail (`Create`; the apply thread's `SaveSnap` and `Release`;
`applySnapshot`'s `Release`; `onStop`'s `Close`; `Reopen`), and `fsExt` lets every system call fail, so an
environment assumption "no I/O errors on these files" is approved, made at the trace level in adequacy
and usable inside Iris. Approved to add a trusted premise; `Impl.lean` unchanged.

## Session 1 (2026-11-15)

### The premise (trusted: `GooseLang/Ext/Fs/Premises.lean`)

- `IoSet` = `{ ino : OsState → Ino → Prop, path : GoString → Prop }`: files by inode at the step's state
  (the calls on an fd or a change token), paths by the call's own argument (the calls on a path).
- `IoCovers S o v st`: the step is `Fsync`/`Close`/`Fstat`/`PRead` on an fd whose inode `S.ino` covers,
  `PWriteFinish`/`FtruncateFinish`/`FallocFinish` on a token whose change's inode is covered,
  `DirSync`/`DirClose` on a directory fd whose inode is covered, `Open`/`Mkdir`/`Unlink`/`Rmdir` of a covered
  path, `Rename` with either path covered. Nothing else: not the lock calls (`Flock`, `OfdLock`: kept
  independent of `wal-c-locks`), not `mmap`/`munmap`, `FallocKeep`, `LstatDir`, the directory reads, the
  outside-the-roots calls, the first steps of changes (no system call).
- `ErrnoZero o e'`: the outcome's errno is 0.
- **`NoIoErr S : StepPrem`** := `IoCovers S o v st → (∃ e'' st'', IsFsStep o v st e'' st'' ∧ ErrnoZero o
  e'') → ErrnoZero o e'`: a covered call succeeds **whenever the semantics has a success for it from that
  state**. So it excludes exactly the errors where a success exists: a failing fsync/fdatasync (EIO,
  ENOSPC, EDQUOT), a pwrite ending with an errno where a byte can land (offset below `maxBytes`), a failing
  ftruncate/fallocate up to `maxBytes`, failing fstat/pread/close, a covered directory's fsync/close, and a
  failing open/rename/mkdir/unlink/rmdir that could succeed. It keeps EFBIG at `maxBytes`, EMFILE with no
  free fd, the path errors of a call that cannot succeed (ENOENT, EEXIST, ...), short writes/reads with
  errno 0, and everything on calls it does not name.
- Documented: `examples/osfs/semantics/premise_no_io_err.go` (indexed in `doc.go`; evidence: assumed),
  `notes/decisions.md` ("fsExt: no I/O errors on chosen files").

### `StepKeeps` (proved, no `sorry`: `GooseLang/Ext/Fs/NoIoErr.lean`)

`noIoErr_keeps (S) : StepKeeps (NoIoErr S)`. Because the premise asks for a success only when one exists,
the kept step is that success when there is one, else the given step; no per-call success construction.
What is left is the heap: `isFsStep_maps` (every covered operation leaves the mappings, by cases) and
`heapRendered_restamp` (a heap rendered for one outcome re-renders for another with the same mappings).
So `fsSemWithS (NoIoErr S) Q` is a valid semantics for `fsSQ_crash_adequacy` (which already takes any
`SQ` with `StepKeeps`); `fsSemWithS_sat` gives `FsStepSat (NoIoErr S)`.

### Using it in Iris (untrusted)

- `GooseLang/Ext/Fs/WpPost.lean` (generic in the extension): **`wp_ext_post`**: if every step of `o` on
  `v` (in the program's semantics) ends in `Val r` with `Ψ r`, then `WP … {{ r, ⌜Ψ r⌝ -∗ Φ r }} ⊢ WP …
  {{ Φ }}`; **`wp_ext_postS`**: the same with a fact `R` of the step's state read off a resource `P` the
  caller holds (`P ∗ localCtx σ ⊢ ⌜R σ⌝`; `P` is then handed to the spec). An existing spec with error arms
  thus gives an error-free one without re-proving it.
- `GooseLang/Ext/Fs/NoIoErrSpecs.lean`: `noIoErr_step`, `fsync_noErr`, `dirClose_noErr`, `pwFinish_noErr`
  (pure: the step's errno is 0), `wp_osFsyncNE`, `wp_osDirCloseSNE`, `pwTok_inflight`,
  `wp_osPWriteFinishKNE` (offset below `maxBytes`).
- WAL: `TailFdatasyncNE.lean`: `wp_tailFsyncNE`, `syscall.Fdatasync.wp_tailNE`,
  `fileutil.Fdatasync.wp_tailNE`/`wp_tailWNE` (the tail's fdatasync returns `errnoErr 0`, the history
  synced); `TailWriterWNE.lean`: `wp_tailPWriteFinishWNE`; `LinuxFs/Proof/os/CloseNE.lean`:
  `os.File.Close.wp_dirSNE` (a shared directory fd's `Close` returns `nil`).
- All built with `lake build` (2026-11-15), no `sorry`, no axiom.

### Statement choices and their limits

- **The inode set is effectively "every inode" for now.** The fd/token specs take `hS : ∀ st i, S.ino st i`:
  `wp_ext_post` sees the step but not which inode the program's fd is on, and for a set given by the WAL's
  paths (`dir`, `dir.tmp` and their entries) the data step would also need the tree at the step (the WAL's
  name claims with the tree's authority), which `wp_os_stepX` frames away. `wp_ext_postS` with `P` = the
  fd (`osFd`, splittable) handles a fixed inode set; a path-derived set needs a data-step lifting that also
  opens the tree context, then the WAL invariant at the step. **Decision for the user/coordinator**:
  (a) instantiate `NoIoErr` with every inode (`ino := fun _ _ => True`) for the server's theorem: "no I/O
  error on any file of the roots' trees" (the roots being etcd's data directory), broader than "the WAL's
  files"; or (b) keep "the WAL's files" (`ino` from the tree) and build the tree-aware lifting first.
  Recommendation: (a) now (the roots already bound the scope to the data directory; the premise is stated
  generally, so (b) can replace it later without touching the semantics).
- The path-based part is usable as is (a path call's argument is visible to `wp_ext_post`).

### What is left (none of the WAL-level `.specNoErr` variants is stated yet)

1. **The tail's writer with no error** (`wal.tailWriterWNE`, for `sync`, `SaveSnapshot`'s `encode`,
   `Close`'s flush): the `WriteAt` loop (`wp_tailWriteAtW`, 270 lines) and `wp_tailWriteW`/`wal.tailWriterW`
   again over `wp_tailPWriteFinishWNE` (needs the offset below `maxBytes` at each attempt: from the loop's
   `off + |data| ≤ max m.size maxBytes`, to be strengthened to `< maxBytes` at the start), the EINTR and
   error exits refuted. Two obstacles found:
   - **An empty `Write` has an arbitrary errno and no `fsExt` step** (`os.File.Write.wp_empty`: the
     `TrustedCode` model draws the errno from `ArbitraryInt`). `NoIoErr` cannot exclude it, so the writer's
     broken predicate can only be `B := fun _ xs => ⌜xs = []⌝`. A trusted-model question (an `fsExt` step
     for a zero-byte `write(2)`, or Go's behaviour modelled otherwise): **for the user**.
   - **`encoder.flush.specP` allows an error with nothing pending** (its error arm is `B out pend` whatever
     `pend`), so with that `B` the sync's flush error is not refutable when `pend = []`. Go's `PageWriter`
     does not write with nothing buffered; a stronger flush spec (`pend = [] → err = nil`) is provable
     (ledger entry). `encode.specG`'s error arm likewise (`B (out ++ a) b` with `b` possibly `[]`).
2. `sync.wp_coreNE` (copy of `wp_core` over the above and `fileutil.Fdatasync.wp_tailWNE`), then
   `sync.specNoErr`/`specCNoErr`, `SaveSnapshot.specNoErr`, `Close.specNoErr` (with `wp_dirSNE`).
3. `ReleaseLockTo.specNoErr`: its only error is `parseWALName` rejecting a lock's name (close errors are
   ignored), not an I/O error; the handle (`walLockNamed`) does not record that the locks' names are WAL
   names, so `NoIoErr` does not help. Needs a handle invariant (each lock's name `walName seq idx`).
4. `Create.specNoErr`: its errors include `Exist` (not I/O; the server calls `Create` only when the WAL
   does not exist: a premise) and every step of the creation; after items 1-2, the path calls are covered
   by `S.path` (`dir`, `dir.tmp`, their entries), the data calls by the inode set.

Next step: item 1 with `B := ⌜xs = []⌝`, after the flush/encode specs gain their "nothing written, no
error" clause.
