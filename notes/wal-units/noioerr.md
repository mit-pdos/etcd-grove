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
