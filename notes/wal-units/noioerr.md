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

## Session 3 (2026-11-15, branch `wal-c-noioerr3`, base `origin/wal-int` 7fe119fb19, merged 9d6a18783e)

### Item 1: `walLockH` records each lock's segment name; `ReleaseLockTo.specNoErr` (proved)

- `Handle.lean`: **`walSegName nm`** := `∃ pd sq ix, nm = child pd (walFileName sq ix)`; `walLockH lf (np :=
  walSegName)` gains the conjunct `⌜np nm⌝` (additive: an optional parameter, the handle's uses unchanged).
  Producers: `readAll_splitLeft` (new premise `∀ g ∈ gs, ∃ sq ix, g.name = walFileName sq ix`, discharged in
  `WAL__ReadAll.lean` from `WalAbsD.nameBound`), `cut` (the demoted tail, from its `walDirH`'s name facts).
  `walOpening`'s closing loop (`walTie_locks`, `WAL__CloseOpening`) uses `walLockH lf (fun _ => True)`: its
  files' names are not tracked, and only `Close` reads them. Consumers' `icases` patterns gained a `-`.
  **Pushed early (commit 21a3d42167) for the purge work.**
- `ReleaseLocks.lean`: `walLockNamed` carries `⌜walSegName nm⌝`; `walDirH_segName` (the tail's name);
  `walLocks_named` takes the tail's fact.
- **`WAL.ReleaseLockTo.specNoErr`** (in `Spec/.../WAL__ReleaseLockTo.lean`): `spec` with `⌜err = nil⌝`; no
  I/O premise. `wp_proofNoErr` is the old proof with the `parseWALName` error arm refuted
  (`baseModel_child_walFileName`, `scanWalName_walFileName`); `wp_proof` is its weakening (no copy).

### Item 2: the room's provenance

- `HandleRoom.lean`: **`walFreshRoom := maxBytes - 2 ^ 43`** (about 8 TB); `cutHdrs_room`,
  `createStream_room` (a fresh tail's headers end below `2 ^ 43`, over `frame_walRecEnc_tight`);
  `walOpenWFR_fresh` (a quiescent handle whose stream ends below `2 ^ 43` has room `walFreshRoom`),
  `walOpenWFR_mono`.
- **`cut.spec`'s success post strengthened** (internal spec, its one consumer `Save`): `h'.o0 + |h'.out| +
  |h'.pend| ≤ 2 ^ 43`. `cut`'s proof gives it from `cutHdrs_room`.
- `Save`: the room comes back after every `Save` that writes (`Save.specNoErr` below): either the tail stays
  below `SegmentSizeBytes` (64 MB, plus at most the page writer's `2 ^ 18` pending bytes) or the call cut.
- `Create`: `createStream_room` is ready, but the room belongs to `Create.specNoErr` (blocked, below): the
  success arm of `Create.spec` includes the reopened WAL of `renameWALUnlock` (arm 2, after an `EPERM`
  rename), whose handle's stream `Create`'s proof does not see; under `NoIoErr` that arm is excluded.

### Item 4: `Save.specNoErr` (proved over `cut.specNoErr`, which is stated, not proved)

- `saveEntry.specNoErr`, `saveState.specNoErr` (new spec/proof files `WAL__saveEntryNoErr`,
  `WAL__saveStateNoErr`): the success arms, over `encode.specTailNoErr`, given room for the record's frame
  (data + 64); posts bound the stream's growth by the same.
- `cut.specNoErr` (`WAL__cutNoErr.lean`, **spec only**): `cut.spec`'s success arm given `o0 + |out| + |pend| ≤
  maxBytes`. Not provable with the current premise: see "Blocked" below.
- **`Save.specNoErr`** (`WAL__SaveNoErr.lean`): from `walOpenWFR k` with `saveRoom Mr hs es ≤ k`
  (`saveRoom` = Σ (|encEntry e| + 64) + |encState hs| + 64), `nil` returned, the handle back with room `k` if
  nothing was written (`hsEmptyP hs ∧ es = []`, the shortcut), else with `walFreshRoom`. The proof is
  `WAL__Save.lean`'s (copied, 300 lines of body) with the loop invariant carrying the room left for the
  remaining frames (`save_drop_sum`) and `save_postR`.
- Linked (`etc/gen-link.py --walfs`): `wp_ReleaseLockToNoErr` (no hypothesis), `wp_saveEntryNoErr`,
  `wp_saveStateNoErr` (the `P` laws), `wp_SaveNoErr` (the `P` laws and `h_wal_WAL_cutNoErr`, pending).

### Blocked: `Create.specNoErr`, `cut.specNoErr` (a decision for the user)

`NoIoErr`'s `IoCovers` does not name every call these make, and on what it names it forces errno 0 only
when a success exists:

1. **The lock calls** (`Flock`, `OfdLock`): `cut` locks its new segment (`fileutil.LockFile`), `Create`'s
   `createNewWALFile` locks the first segment. The lock semantics (`wal-c-locks`) lets any request fail with
   any errno at any time. A blocking lock request with no conflict always has a success, so an extension in
   `NoIoErr`'s style ("a covered lock request succeeds whenever it can") would make both error-free.
2. **The directory reads** (`DirReadNext`, `LstatDir`, `PathKind`, `FdKind`): `Create`'s
   `fileutil.CreateDirAll` reads the new directory (`ReadDir`, to check it is empty) and `os.MkdirAll`
   stats the path; `os.RemoveAll` of an existing `dir.tmp` (a crash's leftover) reads it.
3. **Failing path calls fail with any errno**: an `Unlink`/`Rmdir`/`Open` that cannot succeed may return any
   nonzero errno (`Impl.lean`), and `NoIoErr` keeps all of them (no success exists). Where Go tests for
   `ENOENT`/`EEXIST` (`RemoveAll` of an absent name returns `nil` only on `ENOENT`, `MkdirAll` on `EEXIST`),
   another errno is an error. `Create`'s calls on `dir.tmp` reach this only if it exists or vanishes
   (the area's exclusivity), so it may be avoidable with a premise; to be checked call by call.

Options: (a) extend `IoCovers` with the lock requests and the directory reads on covered inodes/paths (the
same "succeeds whenever it can" form; trusted, `Premises.lean` and its Go example), and add "a covered path
call that cannot succeed fails with the errno Linux gives" if item 3 is reached; (b) leave `Create`/`cut`
with errors and have the server's theorem take their success as a premise. **Recommendation: (a)** for the
lock calls (the WAL's locks are on its own files, which no other process locks: the premise is the same
kind of environment assumption) and the directory reads; item 3 only if a call needs it.

After the decision, `Create.specNoErr` still needs no-error variants of its ~25 callees and a pass over its
1322-line proof. To avoid a copy, the plan: parametrize the proof by a flag `E : Prop` ("errors possible"),
the callee hypotheses at `specE E` (error arms guarded by `⌜E⌝`, `specE True` ⇔ `spec`, `specE False` =
`specNoErr`), so `Create.spec` and `Create.specNoErr` (with `walOpenWFR … walFreshRoom` from
`createStream_room`) are the two instances.

### Build

`lake build` of the WAL's `Link` and the tester's `Link` after the merge of `origin/wal-int` 9d6a18783e: success; no new axiom,
no `sorry`. `etc/gen-link.py --wal-tester --check` and `--durable --check` unchanged.

### Next steps

1. The user's decision on the premise's coverage (above).
2. `cut.wp_proofNoErr` over the extended premise (no-error `Truncate`, `sync.specCut`, the pipeline's
   `Open` (its goroutine's `OpenFile`/`Preallocate`), the encodes on `N.tmp`, `Rename`, the directory
   `Fsync`, `Close`, `LockFile`, `Seek`).
3. `Create.specNoErr` by the flag parametrization.

## Session 4 (2026-11-19, branch `wal-link`): option (a) implemented; item 3 is needed by `Create`

The user approved option (a) (via etcd-grove-03, `questions.md`). Done in 3778c95957 (trusted, `Premises.lean`):
`IoCovers` gains `Flock`, `OfdLock` (an fd of a covered inode) and `DirReadNext` (a directory fd of a covered
inode); `ErrnoZero "DirReadNext"` is errno 0 **or `ENOENT`** (the semantics gives `ENOENT` only for a removed
directory, as Linux, `meta_enoent.go`; excluding it there would make the premise false of Linux; the
shared-mode specs already exclude it for a directory reachable through a claim,
`wp_osDirReadNextChildS`). `noIoErr_keeps` extended (`lockStep_maps`; the reads change only `dfds`). Go
example `premise_no_io_err.go` (excluded/allowed lists, the further assumptions: memory for lock records,
no other process locking, no fatal signal), measurement `premise_no_io_err_test.go` (support only; for
the user's run on C with `run-models-on-c.sh`).

**Not covered, though named in the approval:** `LstatDir` (its outcome `isDir = 0` is both a
non-directory and a failed `lstat` of a directory: no success to name; the WAL's `os.Rename`s target
absent names, where `isDir = 0` is the only outcome), `PathKind` and `FdKind` (model queries with one
answer per state: "covering" them in `NoIoErr`'s form is vacuous).

**Item 3 is reached by `Create`** (so `Create.specNoErr` is blocked on it; `cut` is not):
`renameWAL` starts with `os.RemoveAll(w.dir)`, and `w.dir` is absent at a first start (`wal.Exist` is
false: no WAL directory, or an empty one; etcd's bootstrap does not make `member/wal` first). The
`RemoveAll` model (`TrustedCode/os.lean`) on an absent path: `unlink` fails (no success exists, any
errno), `rmdir` fails (any errno `e1`); `nil` only if `e1 = ENOENT` (or `e1 = ENOTDIR` and the unlink's
errno is `ENOENT`), else it opens the parent and `removeAllFrom`'s `unlink` again needs `0`/`ENOENT`
(or `EISDIR`/`EPERM`/`EACCES`, then the open needs `ENOENT`...). So with any other errno `RemoveAll`
returns an error and `Create` fails, which `NoIoErr` does not exclude. What `Create` needs: "an
`Unlink`/`Rmdir` of a covered path that has no entry, in an existing directory, fails with `ENOENT`"
(Linux: `ENOENT` for a missing last component). With `w.dir` present and empty, `rmdir` succeeds (no
item 3). `Exist(tmpdir)` (a `Stat`) and `MkdirAll`'s `Stat` of the absent `dir.tmp` take any errno as
"absent", and the deferred `RemoveAll(dir.tmp)`'s result is ignored: neither needs item 3. A
leftover `dir.tmp` (a crash's, if `Create.spec`'s area allows one) needs item 3 too: `RemoveAll` of a
non-empty directory first `unlink`s it (no success: Linux `EISDIR`, the model any errno) and `rmdir`s it
(no success: Linux `ENOTEMPTY`, the model any errno); an `ENOENT` there makes `RemoveAll` return `nil`
with the tree still present (then `CreateDirAll`'s emptiness check fails), and `removeAllFrom` recurses
only on `EISDIR`/`EPERM`/`EACCES` (any other errno is an error). So item 3's statement, for `Create`:
a covered path's `Unlink`/`Rmdir` that cannot succeed fails with Linux's errno: `ENOENT` for an absent
entry (its parent a directory), `EISDIR` for `unlink` of a directory, `ENOTEMPTY` for `rmdir` of a
non-empty directory (Linux may also give `EEXIST` there; Go treats both alike), `ENOTDIR` for `rmdir` of
a file. **Stopped for the decision** (the coordinator's instruction).

### The independent attack on (a) (2026-11-19, read-only subagent with the axiom skill): STOPPED

- **F1, refutation (pre-existing in `Impl.lean`, made stronger by (a)):** a lock outlives its fd's `close`
  while a mapping of the file is live (the mapping holds the `struct file`; OFD/flock locks go at the last
  `__fput`, `locks_remove_file`). `f1` locks (`F_OFD_SETLK F_WRLCK`, or `flock LOCK_EX|LOCK_NB`), `mmap`s,
  closes; `f2`'s same request returns `EAGAIN` until the `munmap` (measured on Linux 7.0 / ext4:
  `/shared/tmp/wallink-attack/mmaplock/main.go`). The model's `Close` drops the fd and its locks (`OsMap` has
  no description), so `LockConflict` is false: plain `fsSem` already excludes `EAGAIN` there (`LockStep`'s
  `nb → EAGAIN → conflict`); under `NoIoErr` with (a) every error is excluded. False texts:
  `locks_close_crash.go` ("a lock surviving its fd's close" excluded), `Impl.lean`'s header sentence,
  `NoIoErr`'s "no other fd of the process conflicts". Fixes proposed: descriptions with identity kept alive
  by mappings (locks released at the last `Munmap`), or `Close` stuck while the description holds a lock
  and a mapping of it is live (bbolt's order munmap → funlock → close stays provable). Untested second
  route: Go's `poll.FD` defers `close(2)` while another goroutine is in a syscall on the file.
- **F2, premise false of real runs (pre-existing since 2026-11-15, kept by (a)):** `RemoveAll` of a
  directory with > 1024 entries while another goroutine creates an entry: Go's chunked passes remove the new
  entry while an original remains (30/30, `/shared/tmp/wallink-attack/rmall/main.go`); the model reproduces
  that only by `Unlink` failing with `ENOENT` and no effect on an existing entry, which `NoIoErr` (`Unlink`
  covered) excludes. The WAL's `RemoveAll`s (no concurrency) are unaffected. Fix proposed: model the 1024-name
  chunking directly (a read that stops before its end) instead of spurious `ENOENT`.
- Checked, no gap: lock errnos without a conflict (`ENOLCK`/memory; `EINTR`/`EDEADLK` need a conflict;
  `EBADF`/`EINVAL` stuck in the model), `getdents64` on live and dead directories (`ENOENT` kept),
  `noIoErr_keeps`, the excluded/allowed lists, not covering `LstatDir`/`PathKind`/`FdKind`. Nit: add "no LSM
  denies a lock" (`security_file_lock`) to C's environment.
- No proof uses (a) yet.

## Session 5 (2026-11-19 u, branch `wal-link`): item 3 narrowed (`PathErrno`); F1's approved fix blocked by bbolt; F2 a known gap

**Decided by etcd-grove-03** (`questions.md`): (a)'s form accepted (`LstatDir`/`PathKind`/`FdKind` left out;
`ENOENT` a success of a directory read); **F2 recorded as a known model gap, no fix now** (below); the nit
"no security module denies a lock" added to configuration C's environment (`Impl.lean`, `env_config.go`).

**F2, a known model gap** (not fixed, 2026-11-19): `NoIoErr` with `Unlink` covered excludes the runs where
Go's `os.RemoveAll` of a directory of more than 1024 entries meets a concurrent creation (its chunked passes
remove the new entry while an original stays, which the model reproduces only by an `Unlink` failing with
`ENOENT` on an existing entry). Every `RemoveAll` of the WAL runs with no concurrent creation in the directory
it removes, so no WAL theorem is affected. A fix models the 1024-name chunking (a directory read that stops
before its end) instead of spurious `ENOENT`. Recorded in `notes/audit.md`.

**Item 3, narrowed (approved by the user 2026-11-19), done:** `PathErrno` (`Premises.lean`): a covered
`unlink`/`rmdir` with no outcome of errno 0 fails with `ENOENT` (no entry, parent a directory), `EISDIR`
(`unlink` of a directory) or `ENOTEMPTY` (`rmdir` of a directory with an entry); `NoIoErr` asks it only when
the semantics has no success (the cases are disjoint from the successes, but the model's `#` is not known
injective on `w64`, so the guard keeps `noIoErr_keeps` provable). `noIoErr_good` (`NoIoErr.lean`) gives the
kept step; `noIoErr_pathErrno` (`NoIoErrSpecs.lean`) is what specs use. Go example: `premise_no_io_err.go`
(`NoIoErrPathErrno`), measurement `TestNoIoErrPathErrno` (passes here, not yet on C).

**F1's approved fix (Close stuck while the description holds a lock and a live mapping exists) breaks bbolt
non-mechanically: STOPPED, not implemented.** `DB.close` (`Proof/go_etcd_io/bbolt/Open/Close.lean`) runs
munmap, funlock, close whatever each returns. The model lets `Munmap` fail keeping the mapping
(`wp_osMunmap`'s second failure disjunct; Linux: a `do_vmi_munmap` allocation failure aborts with no change)
and `flock(LOCK_UN)` fail keeping the lock (`LockStep`'s unlock failure; Linux: `flock_make_lock`'s allocation,
`ENOMEM`). In that run the description holds a lock and a mapping is live at `close`: stuck, so
`DB.close.spec_owned` (any `d`, any errors) has no proof. The same holds for any `d` with an OFD lock (bbolt's
spec takes any `d`). The WAL closes locked files (`LockedFile.Close`) with no evidence about mappings (it holds
no `osMeta` of them there), so the stuck form also needs a resource in `wp_osClose`'s precondition ("no
mapping of the inode": the whole `osMeta` with no maps, or no lock) threaded through ~25 WAL/os proofs.
Options in the session-u report.

### The independent attack on item 3 (`PathErrno`) and on the bbolt claim (2026-11-19 u, read-only subagent, axiom skill)

Measured on this machine (kernel 7.0.0-1014-aws, `/shared` ext4 `idmapped,discard,commit=30`, uid 0: not C);
program `/shared/tmp/wallink-attack2/prog/main.go`.
- **A1, premise false of real runs (also of `NoIoErr` before item 3):** the model bounds neither name nor path
  length (`NameOk`, `CanonBelow`, `TreeName`, `lookup`). A 256-byte name or a path over `PATH_MAX` gets
  `ENAMETOOLONG` (measured: unlink/rmdir/mkdir of a 256-byte name, `36`), where `PathErrno` asks `ENOENT` and the
  existing `succ → ErrnoZero` asks errno 0 (`Mkdir`, `Open` `O_CREAT`, `Rename` succeed in the model). Fix: bound
  names (≤ 255 bytes) and paths (< 4096) in `NameOk`/`TreeName` (longer is misuse, stuck), or leave such paths out
  of `IoCovers`; with a Go example.
- **A2, text inaccuracy:** permissions come first in `may_delete`: `EACCES` (no write on the parent), `EPERM` (sticky
  parent, immutable/append-only attributes, LSM path hooks), measured as uid 65534. Neither `NoIoErr`'s docstring nor
  `Impl.lean`'s Environment states "the process may search and write every covered directory; no sticky denial; no
  immutable/append-only attribute; no LSM denies the path calls" (only the Go example does). Fix: state it in both.
- **A3, nit:** the Go example's "RemoveAll returns nil for an absent path only when rmdir answers ENOENT" is too
  strong (a later `ENOENT` from the parent's open or `unlinkat` also gives nil); "only `ENOENT` guarantees nil".
- Checked, holding: errno order on ext4 (lookup `ENOENT`, then `EISDIR`, then `ENOTEMPTY`); the cases disjoint;
  concurrent-race and dead-directory attacks fail; `noIoErr_keeps` proved; doc.go row and citations accurate.
- **B (the bbolt claim), confirmed:** the model run munmap fails keeping the map → `flock(LOCK_UN)` fails keeping
  the lock → `Close` stuck exists; `spec_owned` also takes any `d` (an OFD lock), and with `ms = none` nothing shows
  the inode unmapped. Whether the run is real Linux: probably not (medium certainty, from memory: a whole-mapping
  munmap fails only with a fatal signal pending; `flock(LOCK_UN)` allocates nothing on recent kernels, so fails only
  via `security_file_lock`/`EBADF`; OFD `F_UNLCK` can fail with `ENOLCK`). The reviewer's route: `flock` unlock
  always drops the lock (to be checked against 7.0's `fs/locks.c` and measured), plus `d.ofd = none` in
  `spec_owned`, or a "no lock or no mapping" resource in the new `Close` spec.

## Session 6 (2026-11-19 v, branch `wal-fsfix`, off `wal-link` e6a0c0a811): F1 by option (a), A2, A3; A1 not implemented

**Approved by the user (via etcd-grove-03)**, replacing the stuck-Close form: F1 (a), A1 (stuck), A2, A3.
Then the user split the work: these go to the follow-up branch `wal-fsfix` (brief `notes/wal-fsfix-brief.md`);
`wal-link` lands L3 without any new trusted file-model text.

- **F1 (a), done (trusted, `Impl.lean`):** `MapDesc` (`live fd` / `held d`), `ProcState.mapDesc` (default `∅`),
  `Mmap` adds `.live fd`, `Munmap` deletes it with the mapping, `Close` maps `MapDesc.close fd d` over it (never
  stuck), `LockConflict` gains a disjunct for held descriptions; header/`OsFd` texts. Untrusted repairs: `Locks.lean`
  (`.inl` at four conflict constructions; `wp_osClose` over `OsState.closeFd`, its statement unchanged: the tokens
  are spent), `Specs.lean` (`OsState.closeFd`, `osWf_closeFd`, `MetaOk.closeFd`, `osCoh_closeFd`; Mmap/Munmap state
  shapes), `World.lean` (`treeFrame_maps`/`treeFrame_fds_delete` take the new `mapDesc`), `Facts.lean`
  (`osCoh_setMaps` takes it). The ghost locks (`LockWf`, `LockCoh`, `lockCtx`) stay fd-only: held descriptions only
  make more lock requests fail. All of `GooseLang/Ext/Fs/*` builds (`/shared/tmp/wallink/b-f1f.log`); bbolt and WAL
  NOT yet rebuilt over it (nothing there names `"Close"`'s state; to check with the follow-up's build).
  Consequence for later no-error lock specs: proving no conflict now also needs "no held description of the
  inode" (e.g. from the file's whole `osMeta` with no maps plus an invariant tying `mapDesc` keys to `maps`).
  Go example `locks_mmap_close.go`, measurement `TestLocksMmapKeepsDescription` (passes here; not yet on C);
  `locks_close_crash.go`'s false "Excluded" fixed; doc.go row.
- **A2, done (trusted text only):** C's permissions in `Impl.lean`'s Environment, `NoIoErr`'s docstring,
  `env_config.go`, `premise_no_io_err.go`; contrast measurement `TestNoIoErrPermissions` (EACCES as nobody, measured
  here; immutable/append-only EPERM where `FS_IOC_SETFLAGS` is permitted, not here).
- **A3, done:** "only ENOENT guarantees that os.RemoveAll returns nil".
- **A1, NOT implemented (cost):** "stuck" for names > 255 / paths ≥ 4096 puts a length premise on every path WP
  spec (`treeName_child` cannot bound `child d b` from `lookup d`), hence on every caller (WAL, bbolt, fileutil, os
  models, walfs/bboltfs/crashlog). Cheaper sound alternative to put to the user: leave such paths out of `IoCovers`
  (and so of `PathErrno`): the plain semantics already lets them fail; the extra success outcomes on long paths are
  an over-approximation; only the no-error specs then need a length premise (a WAL-dir length bound). Measurement
  written: `TestNoIoErrNameTooLong` (ENAMETOOLONG for 256-byte names and 4096-byte paths, passes here).
- **Attack:** an independent read-only attack on F1 (a), A2, A3 was launched from `wal-link`'s working tree
  (programs under `/shared/tmp/wallink-attack3/`); its result belongs to this branch.

## Session 7 (2026-11-19 w, branch `wal-fsfix`): the user's decisions on the attack on 9017eb196d

**Decided by the user (via etcd-grove-03)** on the attack's findings (`notes/wal-fsfix-brief.md` on `wal-link`,
"The attack on 9017eb196d"):

- **(1) The lock refutation, option (b)** (trusted, `Impl.lean`): `LockStep`'s failure arm no longer ties `EAGAIN` to
  `LockConflict`: a non-blocking request may fail with `EAGAIN` whatever the model's locks (true of Linux: another
  process reading `/proc/<pid>/fdinfo/N`, `readlink /proc/<pid>/fd/N`, `pidfd_getfd`, ptrace holds a reference to a
  closed description, so its locks outlive `close(2)`; no environment assumption). Texts: the header's "Locks",
  `LockStep`, `EAGAIN`, `Close`'s comment, `TrustedCode/syscall.lean` (`Flock.impl`, `FcntlFlock.impl`),
  `locks_close_crash.go` ("Excluded"), `locks_ofd.go`, `locks_flock.go`, `locks_blocking.go`. Go example
  `locks_spurious_eagain.go`; measurement `TestLocksProcReaderEagain` (a child reading the fdinfo file; EAGAIN within
  a few rounds here, 0 in 5000 rounds without the reader). `LockStep` keeps its `nb` argument (unused now; the
  calls name the request whole). Proofs: mechanical (`Locks.lean`, `CommitMono.lean`, `NoIoErr.lean`: one conjunct
  fewer). **`wal.Open`'s `TryLockFile`**: no proof used the old clause (`fileutil.lockPost`'s error arm and
  `lockOut` already allow any errno); `TryLockFile.spec`, `Open.spec` unchanged.
- **NoIoErr's lock clause, the form decided** (trusted, `Premises.lean`): `IoCovers "Flock"` only when `how` has no
  `LOCK_NB` (`how.toNat / 4 % 2 = 0`), `IoCovers "OfdLock"` only for `cmd = F_OFD_SETLKW`: blocking lock requests and
  blocking unlocks. Enough for the WAL (`fileutil.LockFile`: `F_OFD_SETLKW` or `flock(LOCK_EX)`); the non-blocking
  `TryLockFile` (wal.Open) keeps its error arm.
- **(2) Permissions** (trusted text): `Impl.lean`'s Environment, `NoIoErr`'s docstring, `env_config.go`,
  `premise_no_io_err.go` extended with each gap: search of the roots' ancestors, read/write of the covered files,
  `fs.protected_symlinks` (a trailing symlink only: measured that an inner symlink component is followed) and
  `fs.protected_regular`, the idmapped mount's `EOVERFLOW`, seccomp, fanotify. Contrasts: `TestNoIoErrPermAncestor`,
  `TestNoIoErrPermFileWrite`, `TestNoIoErrProtectedSymlinks` (pass here on tmpfs; `/shared` is idmapped, so `lchown`
  fails there), `TestNoIoErrProtectedRegular` (skipped here: the sysctl is 0).
- **A3 reverted** to the old sentence ("RemoveAll returns nil for an absent path only when rmdir answers ENOENT (or
  ENOTDIR after unlink's ENOENT)").
- **A1 as "outside IoCovers"** (trusted, `Premises.lean`): `PathFits p` (`p.length < 4096`, every 256-byte infix holds
  a `/`); the path calls are covered only on paths that fit (both of `rename`'s). No stuck, no premise on the WP
  specs; the no-error specs will need the WAL paths to fit.

### The independent attack on the branch's trusted text (2026-11-19 w, read-only subagent, axiom skill): STOPPED

Programs and logs `/shared/tmp/walfsfix-attack4/`; target d1b49ad308 (read-only worktree `/shared/tmp/walfsfix-attack4-ro`).
- **F1', refutation (pre-existing on `lean`):** a blocking lock request (`flock(LOCK_EX)`, `F_OFD_SETLKW`) waiting on a
  conflict holds its own reference to the description (`fdget`); another thread `close`s the fd (returns 0), then the
  conflict is released: the waiting call returns **0** (4/4 cases, `closewait/`). The model's `Flock`/`OfdLock` is one
  atomic step needing `FdOpen` and no conflict: excluded. Variant: with a live mapping, the lock lands on the
  `MapDesc.held` description and outlives the fd. No current proof reaches it (`wp_osFlock`/`wp_osOfdLock`/`wp_osClose`
  each take the whole fd). Proposed fixes: blocking lock as begin/end steps with `Close` stuck while one is in flight;
  or an environment clause "no fd is closed while a lock call on it is in flight".
- **F2', false text:** `FdFree` has no upper bound, so `Open` always has a success and `NoIoErr` excludes Linux's `EMFILE`
  at `RLIMIT_NOFILE` (measured with the soft limit at 64); "does not exclude EMFILE with no free fd" is false. Fix: an
  environment clause "fewer than RLIMIT_NOFILE fds" (NoIoErr, env_config.go), or bound `FdFree`.
- **F3', false text:** "ENAMETOOLONG whatever the tree holds": an earlier missing/non-directory component gives
  ENOENT/ENOTDIR first (the check is in `ext4_lookup`). Soundness unaffected (not covered). Fix the wording.
- **Nits:** "short reference" (a `pidfd_getfd` copy can live indefinitely; a blocking request then waits indefinitely);
  "no other process locks them" → "locks or unlocks them, through any description"; `TestNoIoErrProtectedSymlinks`
  could skip on EOVERFLOW (idmapped mounts); `TestLocksMmapKeepsDescription`'s no-mapping control can flake under an
  fdinfo reader.
- Holding: LockStep without the EAGAIN clause (no text/proof relies on it; EDEADLK impossible; EINTR/ENOLCK in the
  failure arm), the blocking-only coverage, `PathFits` (exactly PATH_MAX/NAME_MAX for canonical absolute paths),
  the permission list (ETXTBSY gone on 7.0; leases/inotify only wait; others outside C), MapDesc; the new tests pass
  (but the noted skips).

## Session 8 (2026-11-19 w): the user's decisions on the attack of session 7

**Decided by the user (via etcd-grove-03)**, with a stopping rule (after one final attack, a corner the WAL's or
bbolt's proofs do not reach is recorded as a known model gap, not fixed):
- **F1'**: environment clause of configuration C, "no fd is closed while a lock call on it is in flight"
  (`Impl.lean`'s "Environment", "Locks", `LockStep`, `Close`'s comment; `NoIoErr`'s docstring, "Fds and locks";
  `env_config.go`). Go example of the excluded run `env_no_close_during_lock.go`; measured `TestLocksCloseDuringLock`
  (4/4: OFD and flock, released by close or unlock: the call on the closed fd returns 0). The WAL (`LockFile`/
  `TryLockFile` return the file only after the lock call) and bbolt (flock/funlock on the goroutine owning the file)
  meet it.
- **F2'**: environment clause "fewer fds than the `RLIMIT_NOFILE` soft limit, system below `fs.file-max`" (no
  `EMFILE`/`ENFILE`); `NoIoErr`'s and `premise_no_io_err.go`'s false "does not exclude EMFILE" removed, the exclusion
  stated. Measured as a contrast: `TestNoIoErrEmfile`.
- **F3'**: `PathFits`'s and `premise_no_io_err.go`'s ENAMETOOLONG wording (when the walk reaches the long component;
  ENOENT/ENOTDIR first); `TestNoIoErrNameTooLong` measures the order.
- **Nits**: "short reference" → a moment for a /proc reader, indefinitely for a `pidfd_getfd`/ptrace copy (Impl.lean
  header, `LockStep`, `Close`); "no other process locks or unlocks them, through any description";
  `TestNoIoErrProtectedSymlinks` skips on `EOVERFLOW`; `TestLocksMmapKeepsDescription`'s control retries `EAGAIN`.
No Lean definition changed (docstrings only).

### The final attack (2026-11-19 w, read-only subagent, axiom skill; target b65bc3e75c): no STOP

Evidence `/shared/tmp/walfsfix-attack5/` (no loop devices in the container: measured on Linux 7.0 with `/shared`'s ext4
and a tmpfs, kernel-wide behaviours). Today only the WAL uses `NoIoErr`, through `fsync_noErr`/`wp_osFsyncNE`,
`wp_osPWriteFinishKNE` and `wp_osDirCloseSNE`; path coverage, lock coverage and `PathErrno` are used by no proof yet.
By the stopping rule, recorded as **known model gaps** (`notes/audit.md`, "Found by the final attack on `wal-fsfix`"),
not fixed:
1. a leaked locked `*os.File`: Go's finalizer closes it and releases its locks, the model keeps them (refutes
   `LockStep` for such a program; `TrustedCode/os.lean`'s "finalizer (D5) unrelated" is false since locks; the WAL and
   bbolt never leak a file);
2. read permission on directories missing from C's permissions (`EACCES` from `os.Open` of a `-wx` directory):
   **becomes reachable once `Create.specNoErr` covers its `OpenDir`/`ReadDir`** — to fix (one wording) before that
   proof relies on it;
3. `ETXTBSY` for an open for writing of an executing file (real on 7.0; session 7's "gone on 7.0" was a flawed run);
4. the idmapped mount must map the entries' owners too (`may_delete`'s `EOVERFLOW` before `PathErrno`'s cases);
5. minor: "memory for their locks and reads" should be "memory for these calls".
Holding (the attack's checks): no `ENOENT` from `open` racing `rename` replacing the name (1M opens); the Go models'
1 GiB chunking; `File.Fd`/`poll.FD` deferred close (stuck in the model); locks (hidden descriptions only make blocking
requests wait; no `EDEADLK`; flock/OFD independent; `MapDesc` with fd reuse); the remaining errnos of the covered fd
calls are the environment's; `PathFits`; `PathErrno`'s order (but 4); `model.stat` consistent under `NoIoErr`.

## Session 9 (2026-11-20, branch `wal-fsfix`): the configuration-C runs

The user ran `examples/osfs/semantics/run-models-on-c.sh` on C (Linux 7.0, ext4 defaults, loop device; `check.sh`'s
line heads each log). Logs: `notes/axiom-review/noioerr-c-runs/`.
- **Run 1, at f5823538f2** (`run1-f5823538f2.out`): every lock test (`TestLocksProcReaderEagain`,
  `TestLocksCloseDuringLock` included), `TestCrossRootRenameExcluded`, `TestNoIoErr{Locks,Readdir,PathErrno,
  NameTooLong,Emfile}` pass. Five failures, each a harness bug (no refutation), fixed in 768dbff487:
  `TestNoIoErrPermissions` (a bare `FS_IOC_SETFLAGS` value clears `FS_EXTENT_FL`, which ext4 refuses: now
  GETFLAGS and the one bit); `TestNoIoErrPermAncestor`/`PermFileWrite`/`ProtectedSymlinks` (the script's
  `mktemp -d` directory, 0700, kept nobody from the mount: now 0755, and `permDir` checks nobody reaches its base;
  reproduced on /dev/shm: a 0700 ancestor gives exactly the run's EACCES); `TestDirRenameScopedToRoot` (root A's
  fsync made 26 renames: now B runs until A made 400); `TestEnoent` (bounded: 200-3000 rounds within 20 s); the
  script's cleanup on Ctrl-C (process group, INT/TERM, unmount retried then lazy, failures printed).
- **Run 2, at 768dbff487** (`run2-768dbff487.out`): every test passes (`TestDirRenameScopedToRoot`: 402 renames
  in A). Skipped: `TestNoIoErrProtectedRegular` (`fs.protected_regular` is 0 on that host). Configuration C does
  not fix that sysctl (`notes/axiom-review/fs-config/README.md` names none), and C's claim does not depend on it:
  the environment clause (`Impl.lean`'s "Environment", `env_config.go`) assumes the sysctl denies nothing, which a
  setting of 0 makes true outright; the test is only the contrast (why it is an assumption where the sysctl is
  set), measured where it is set: not on this host. `TestEnoent`'s bounded form was not in the run (untested on C).

## Session 10 (2026-11-20, branch `wal-fsfix`): the user's decisions of 2026-11-20 implemented; the attack on them

The member-name bound (≤ 200 bytes) in `bootCfgFresh` (`Fs.DirFits cfg.DataDir'`), threaded as `name.length ≤ 200`
premises through etcdstart's specs up to the examples (`memberAt_name_len`, `members_names_len`, `cluster3.cfgOk`'s
`len1`-`len3`); `flock` out of `IoCovers` (`NoMapLockErr` covers it); `PathFits` on the error-free open/rename
lemmas and on the shared-mode name claims.

### The independent attack (2026-11-20, read-only subagent, axiom skill; target 9cff19a579): no refutation

Programs and outputs: `/shared/tmp/walfsfix-attack9/` (`symlen/`, `joinfit/`).

1. **`IoCovers` without `"Flock"`**: survives (for a blocking `flock` the old clause asked what `MapLockOk "Flock"`
   asks; the two premises are always assumed together; no inconsistency). **False text** `Premises.lean` ("Nor
   anything about the OFD lock (`fcntl`), which `NoIoErr` does not name either": `IoCovers "OfdLock"` exists),
   fixed; stale Go texts (`locks_spurious_eagain.go`, `doc.go`, `premise_no_io_err.go`, `TestNoIoErrLocks`'s
   comment) and "one premise per call" (an `open` with no free fd is named by both) fixed. Open: `NoMapLockErr` is
   still marked "pending the user's review" and now carries `flock`; `cut.specNoErr` will need
   `FsStepSat (NoMapLockErr Sio)` too (`fileutil`'s flock fallback, `TrustedCode/syscall.lean`).
2. **`PathFits`/`PathFitsLemmas`**: survives (4096-byte paths rejected; windows = no component over 255; only
   canonical absolute paths reach a covered step; a root under symlinked ancestors resolving to 6049 bytes gave no
   `ENAMETOOLONG` on ext4 and tmpfs of this host: to rerun on C before a trusted text cites it).
3. **`bootCfgFresh`'s `DirFits`, `bootOk`'s `PathFits`**: survives; but `config.snapDirOf` is opaque, so the
   `PathFits` of the snapshot and backend paths in `bootOk`'s claims is ASSERTED by the assumed contract, not
   implied by its precondition (true of Go: `SnapDir` is `filepath.Join(d, "member", "snap")`; `joinfit/` checked
   134 400 adversarial data directories). For the land report (or define `snapDirOf` as Go's `Join`).
4. **mvccrand/mvccfull `Hrfit : Fs.DirFits r`**: satisfiable (a real root's components are ≤ 255; only
   `|r| < 3800` restricts) and sufficient (only `r/<name>` paths, names ≤ 255).
