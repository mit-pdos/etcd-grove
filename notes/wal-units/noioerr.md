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

## Session 2 (2026-11-15, branch `wal-c-noioerr2`, base `origin/wal-int`)

The user's decisions of 2026-11-15: **coverage (a)** for now (the premise covers every file under the
roots, etcd's data directory: the specs take `∀ st i, Sio.ino st i`; recorded in `notes/decisions.md`, the
noioerr entry, and in each spec's docstring); fork changes only for demonstrated bugs (etcd's Go unchanged).

### Item 1: zero-byte writes are never reached (obstacle 1 moot)

The WAL never hands its `*os.File` an empty slice on the paths the server panics on: every write to the tail
goes through the encoder's `ioutil.PageWriter` (`encode` -> `write` -> `PageWriter.Write`; `flush` ->
`PageWriter.Flush`), and the page writer calls its writer only in two places, both non-empty:
`flush` writes `buf[:bufferedBytes]` only when `bufferedBytes != 0` (pagewriter.go:107-111), and `Write`
writes `p[:pages*pageBytes]` only when `len(p) > pageBytes` (`pages >= 1`, pagewriter.go:86-88); its
recursive `pw.Write(p)` of the rest is buffered (the rest fits below the watermark). So `encoder.flush` with
nothing pending makes no `Write` and returns `nil`, and the trusted empty-`Write` branch (arbitrary errno, no
`fsExt` step, `os.File.Write.wp_empty`) is never reached. No trusted-model change is needed.

Made checkable without changing any existing statement:

- `io.writerStreamPNE wi ok W B` (`Proof/io/WriterStream.lean`): `io.writerStreamP` for the calls with a
  non-empty `xs` only; `io.writerStreamP_NE`: every guarded stream is one.
- The page writer and the encoder over it (obstacle 2, the ledger's proposal (1), done this way): new specs
  `PageWriter.flush.specNE`, `Flush.specNE`, `Write.specNE`, `encoder.flush.specPNE`, `wal.write.specNE`,
  `encoder.encode.specGNE`, `WAL.saveCrc.specNE`, identical to the existing ones but over
  `io.writerStreamPNE`. Their proofs are the old ones with the non-emptiness discharged at the two writer
  calls (`flush`: the buffer's length is `bb ≠ 0`; `Write`: `P = len/pB * pB ≥ pB > 0`); the old specs are
  now their instances (`wp_proof` from `wp_proofNE` by `io.writerStreamP_NE`), taking the NE callee specs.
  A writer whose every non-empty `Write` succeeds (`B` false) thus makes `flush` and `encode` succeed, and
  "nothing pending, no error" needs no separate clause.

### The error-free tail writer, `sync`, `Close`, `SaveSnapshot`

- `TailWriterWNE.lean` (lemmas): `wp_tailWriteAtWNE` (the `WriteAt` loop over `wp_tailPWriteFinishWNE`,
  every errno 0: no `EINTR`, no error exit; premise: the write's end at most `maxBytes`, so every attempt
  starts below it), `wp_tailWriteWNE`, the guard `tailOkWNE` (`tailOkW` and the stream's end at most
  `maxBytes`) and **`wal.tailWriterWNE`**: `io.writerStreamPNE (wal.fileWi f) (tailOkWNE …) (walTailWS …)
  (fun _ _ => False)`.
- `WAL.sync.specNoErr`, `sync.specCNoErr` (`Spec/…/WAL__syncNoErr.lean`; proof `WAL__syncNoErr.lean`,
  `wp_coreNE`: `wp_core` over `wal.tailWriterWNE`, `flush.specPNE` and `fileutil.Fdatasync.wp_tailWNE`):
  `sync.spec`/`specC`'s success arm, always, when `o0 + |out| + |pend| ≤ maxBytes`.
- `encoder.encode.specTailNoErr` (`encoder__encodeTailNoErr.lean`): `specTail`'s success arm, when the
  encoder's bytes and the frame end at most at `maxBytes`.
- **`WAL.Close.specNoErr`** (`WAL__CloseNoErr.lean`): `Close.spec`'s success arm with `err = nil`, from
  `walOpenWFR P Mr w dir 0`; the lock files' close errors are ignored by the code, the directory's `Close`
  is `os.File.Close.wp_dirSNE`.
- **`WAL.SaveSnapshot.specNoErr`** (`WAL__SaveSnapshotNoErr.lean`): `SaveSnapshot.spec`'s success arm, from
  `walOpenWFR P Mr w dir (|encSnap md| + 64)` (the frame is at most the data plus 64,
  `frame_walRecEnc_tight`).
- All linked (`etc/gen-link.py --walfs`; `etc/link_walfs.py` now also emits the implicit section variables
  an instance names, `{Sio : IoSet}` of `[FsStepSat (NoIoErr Sio)]`). The old specs of the page writer and
  `write` are no longer linked results (nothing reaches them: their callers' proofs take the NE specs); they
  are still proved (`wp_proof`).

### A premise that is not an I/O error: `EFBIG` at `maxBytes` (decision left for the user)

`fsExt` bounds every file at ext4's `s_maxbytes` (`maxBytes = 0xffffffff000`, `wal-maxb14`): a write that
reaches it fails with `EFBIG`, and `NoIoErr` keeps that error (no success exists there). So an error-free
flush needs the tail's stream (written and pending) to end at most at `maxBytes`, which the handle does not
record (`walOpenWF` keeps `o0 + |out| ≤ sz ≤ maxBytes` only; the stream-end fact was withdrawn because
`SaveSnapshot` never cuts, ledger 2026-11-14). The specs above take it as **a sealed handle with room**,
`walOpenWFR P Mr w dir k` (`HandleRoom.lean`: `walOpenWF` with `o0 + |out| + |pend| + k ≤ maxBytes`;
`walOpenWFR_wf`: it is a `walOpenWF`). How a client comes by it is the user's decision; options:

1. **Room laws on the existing specs' posts** (recommended): `Create`'s post gives `walOpenWFR … K` for a
   large `K` (the fresh tail is the header records, below `2^42`); `Save`'s post after a cut likewise; a
   law `walOpenWF ⊢ walOpenWFR … 0`-style is false in general, so a long run of `SaveSnapshot`s without a
   `Save` must carry the room itself (each `SaveSnapshot.specNoErr` consumes `|frame|` of it; its post
   would return `walOpenWFR … (k - |frame|)`). The server alternates `Save` and the apply thread's
   `SaveSnap`, so the room comes back at each cut; this needs a statement of the server's `Save` rhythm.
2. **A public measure of the tail** (`walOpenWFn … n`, `n` the stream's end, `walOpenWF ⊣⊢ ∃ n, …`), each
   spec's post saying how `n` moves; the premise `n + k ≤ maxBytes` on the no-error specs.
3. **A premise on the whole history's encoded size** in the update's precondition (needs a peek law,
   `d.H = h.H`, and a pure bound of the tail's stream by the history's bytes); undischargeable for a long run
   (the model's history grows without bound).

No change to the trusted semantics is involved (EFBIG is the configuration's limit, measured).

### `ReleaseLockTo` (item 2): not done; the plan

`ReleaseLockTo` makes no I/O call that can fail into its result (S/wal.go:1013-1053: the locks' `Close`
errors are ignored), so `ReleaseLockTo.specNoErr` needs no `NoIoErr` at all, only that every lock's file name
is a WAL file name (`parseWALName(filepath.Base(l.Name()))` succeeds). Lemmas exist
(`baseModel_child_walFileName`, `scanWalName_walFileName`, `CutName.lean`). The handle does not record it:
the tail's name does (`walDirH`: `name = child pd nm0`, `nm0 = walFileName sq ix`), the non-tail locks'
(`walLockH`) do not. The change: `walLockH` records `∃ pd sq ix, nm = child pd (walFileName sq ix)`;
its producers are `readAll_splitLeft` (`ReadAllLocks.lean`, from the segments' names, `WalAbsD`'s) and
`cut` (`WAL__cut.lean:889`, the old tail demoted, from `walDirH`'s fact); its consumers' `icases` patterns
(`WAL__Close`, `WAL__CloseU`, `WAL__CloseOpening`, `WAL__ReleaseLockTo`, `ReleaseLocks`) gain one
component. **Not done this session** because `wal-c-locks` rewrites exactly `walLockH` (a new conjunct),
`ReadAllLocks.lean` and `WAL__cut.lean`: doing it after that branch lands avoids a three-way conflict. Then
`walLockNamed` carries the fact and the error arm of the name loop is refuted.

### `Create` (item 3): not done

`Create.specNoErr` needs no-error variants of every call of its 1322-line proof (the `RemoveAll`s,
`CreateDirAll`, `OpenFile`, `Preallocate`, `WriteAt` of the metadata, `Fdatasync`, `syncDir`, `OpenDir`, the
directory `Fsync`, `renameWAL`, `cleanupWAL`), each over `wp_ext_post` (the path calls through `Sio.path`,
covered by (a)), then the proof copied with the error arms refuted. Its encodes can use `encode.specGNE`/
`saveCrc.specNE` over a no-error writer on the fresh segment (the tail's `tailWriterWNE` or the length-bounded
`os.File.writerStream`, whose empty-write case `writerStreamPNE` now avoids). The fresh tail is far below
`maxBytes`, so `Create` needs no room premise (and its post can give `walOpenWFR … K`, option 1 above).
Not started: `wal-c-locks` also edits `Create.lean`, `CreateHandle.lean`, `CreateSeg.lean`.

### Build

`lake build` of the WAL's `Link` and the tester's `Link` (2026-11-15; every module touched is below them),
no error, no `sorry`, no axiom. Also `WAL.Sync.specNoErr` (`WAL__SyncNoErr.lean`: the room `k` kept) and
`SaveSnapshot.specNoErr` returning `walOpenWFR … k` from `walOpenWFR … (k + |encSnap md| + 64)` (option 1's
shape). `etc/gen-link.py --wal-tester`/`--durable` outputs unchanged.

### Next steps

1. The user's decision on the room (above); then `Create`'s post (and `Save`'s) giving `walOpenWFR`.
2. After `wal-c-locks` lands: `walLockH`'s name fact and `ReleaseLockTo.specNoErr`; re-run this session's
   copies (`wp_coreNE`, `wp_tailWriteAtWNE`, `Close.wp_proofNoErr`) over its changed `osFd`/`walTailW`.
3. `Create.specNoErr` (the os-level no-error variants first), `Save.specNoErr` (with room for its batch).
