# egos (S5) resume — 2026-11-24, egos #5 stopped at the lead's wrap-up

## Session #5 (commits 0c9f56cc16..418f8a955b, pushed)
- `Proof/os/ForLoeb.lean`: `wp_for_loeb` (one doFor iteration, the loop again under ▷ in the
  continue/execute posts) + tactics `wp_for_bind` (wp_auto then bind the loop) / `wp_for_step`.
  Port recipe for the model's old Lean-recursion loops (script gmr-egos/tools/forloop.py FILE N1,N2,..):
  `wp_for_bind; iloeb as IH generalizing ...; wp_for_step`; at a continue: `wp_for_post; inext;
  iapply IH $$ ... [$]×k` (k = the loop's local-var points-tos iloeb reverted); before `iapply HΦ`
  inside the loop: `wp_for_post`. Loop locals that change (b/off/n, nn) get fresh Lean vars via
  `ihave Hxp : (x_ptr ↦ v) $$ [x]` (ReadAt `readat_start`, WriteAt `Hnnp`). tools/wafix.py,
  tools/newfile.py: the WriteAt-family and OpenFile-success edits.
- `IgnoringEINTR.lean` builds; `os.wp_syscallMode` moved there (over io/fs FileMode.Perm:
  `haveI io.fs.Assumptions := os.Assumptions.import_fs_Assumption`, `NotInterface go.uint32`);
  macros `wp_open_stub` (syscallMode then fsOpen stub) and `os_newfile` (the model's `&file{}`
  split: `inner`, `pfd` fields, File hyp renamed `f`); after os_newfile use `wp_for_post_core`
  before `iapply wp_fupd`, then `ipersist name/f/nonblock`.
- Checked clean with lean-check: File__Close, CloseClosed, Fd, Truncate, TruncateAu, Sync, SyncS,
  Off, ReadAt, WriteAt, WriteAtExt, Crash, CrashStSpec, IgnoringEINTR.
- Shared bug fixed: gen-init NET_MAIN += internal.gomodel (Net/Proof/internal/gomodel/Init.lean);
  regenerated (Net/KvNet/Dsverify PkgTables reordered); `gen-init --check` clean.

## In flight / not done
- VM build12 of targets10.txt was started and KILLED (unstarted, ssh mux errors): nothing verified
  on the VM this session. Run it first: `/shared/tmp/vm/vmlake --fetch build $(cat ../gmr-egos/targets10.txt)`.
- Unchecked since build11 (were never reached): CloseNE, OpenFileS/Trunc*, Ns*, Stat*, RemoveAll*,
  Rename*, Remove/RemoveN, WriteFile*, WriteLong*, OffEnd/OffLong, ReadEof, MkdirAll*, PathParent,
  ErrnoPathErr, NsAbove, Proof.io.*, filepathlite Base, TrustedCode runtime.lean (2 errors).
  Apply the same recipes (OpenFile success: os_newfile; os.wp_modelPathError then `iintro %pe`).
- Earlier open items 2-8 below still stand.

## Previous session (#4) notes

Worktree eg-gmr, branch go-models-rest/2026-11-24 (pushed). gen-init: PERENNIAL_DIR=gmr-egos/perennial-lean.
Always `export TMPDIR=GOTMPDIR=/home/ubuntu/.claude-E/jobs/b20ef685/tmp/gmr-egos/tmp`.
Goose regen: `flock ../eg-gmr-goose.lock env PATH=/home/ubuntu/sdk/go1.27.3/bin:$PATH etc/goose.py
--perennial ../pgmR-xtools --project bboltfs` (pgmR-xtools is at 78d6ef937).
Model tests: `PATH=/home/ubuntu/sdk/go1.27.3/bin:$PATH etc/model-tests.sh --perennial ../pgmR-xtools os syscall durable`
(run_in_background directly). Builds: VM only (no local .lake/build); the VM was saturated all
morning (FIFO slot waits of 15+ min): batch targets (gmr-egos/targets9.txt = all Proof/os, Proof/io,
Locks, bboltfs DB, runtime). One vmlake per checkout at a time (lock), so no `vmlake env lean` while a
build runs. To see goals on the VM: `vmlake env lean <file>` after a build left the deps built.

## Done this session (commits after bb9a798186)
- 9ebd61f12e (+ next commit): 
  - `os.ownFile` owns `structFieldRef os.file go!"nonblock" inner ↦□ false` (4th conjunct; lead's
    decision); 52 destructurings got `#Hnb` (`gmr-egos/tools/nb.py`); bbolt `fileOwn` (Inv/Locks) the
    same body; every `structFieldRef os.file go!"fd" X` (Locks, bboltfs DB, io/CopyRound, io/CopyPoll)
    is now `structFieldRef internal.poll.FD go!"Sysfd" (structFieldRef os.file go!"pfd" X)`.
    The model's OpenFile must produce `nonblock ↦□ false` (OpenFileS etc.: persist the field after
    the alloc; not yet done).
  - `Proof/internal/filepathlite/Lexical.lean` (defs): `IsPathSeparator/volumeNameLen/FromSlash/
    VolumeName/Base.wp_lex`, the same triples with precondition `True` (the package has no fact; the
    os specs have no `isPkgInit`). `Base.wp_proof` is now a wrapper over `Base.wp_lex` (the proof
    moved). No spec changed. os proofs call `filepathlite.Base.wp_lex` (File__Stat, StatNE: done
    textually) where the old `os.model.wp_base` was.
  - `Code/os.toml`: `supportsCreateWithStickyBit` translated (it was `opaque`, which made Go's
    `Mkdir` unprovable: `!opaque` is stuck); regenerated (only that constant changed).
  - `Proof/os/IgnoringEINTR.lean` (defs): `os.wp_fixLongPath`, `os.eintrCall`, `os.wp_ignoringEINTR`
    (Go's loop for an `fn` returning `errnoErr e`; `I` kept on EINTR, `Ψ e` otherwise).
  - `Proof/os/MkdirParts.lean` (defs): `os.treeName_child`, `os.mkdirAttempt` (one `fsMkdir` stub
    call from `I`), `os.wp_syscallMode`, `os.Mkdir.wp_tree` (Go's Mkdir below a root, closure via
    `recv_eq_func_mk`), `os.Mkdir.wp_notTree` (PathKind ≠ 1: syscall model's Choose errno, no step),
    `os.Mkdir.wp_takenS` (moved from MkdirAllParts, now over wp_tree).
  - `Proof/os/Mkdir.lean`: `wp_proofSnc` over `wp_tree` (I = spine ∗ call perm ∗ the old state
    disjunction; the attempt is the old loop body), `wp_proofS` unchanged.
  - `Proof/os/PathParent.lean`: old `wp_mkdirAllParent`/`wp_base` gone; new pure lemmas
    `os.backIdx_slash`, `os.parentModel_prefix`, `os.parentModel_slash`, `os.rootsAbove_parent`
    (parent of a root / strict ancestor is a strict ancestor or empty), `os.parentModel_joinPath_snoc`;
    macros `mkdirall_parent P K` / `mkdirall_loop2` / `mkdirall_slice` (Go's two doFor loops of
    MkdirAll on the path P, `if i < 0`, `parent := path[:i]` ⇒ `parent ↦ os.parentModel P`, then
    the tactic K, run once per loop exit; modelled on filepathlite Base's loop proof). ALL UNCHECKED:
    written blind (VM queue). Expect tactic-shape fixes.
- None of the above has been compiled yet: the VM queue held 26 builds at 08:40Z; build10 (targets10.txt, the current tree) was killed unstarted when I stopped. Start there.

## Open items, in order
1. Read build9.log (or rerun: `/shared/tmp/vm/vmlake build $(cat ../gmr-egos/targets9.txt)` plus
   `Proof.internal.filepathlite.Base Proof.os.Mkdir Proof.os.MkdirParts Proof.os.IgnoringEINTR`).
   Fix Lexical/IgnoringEINTR/MkdirParts/Mkdir first (small, everything else builds on them).
2. Off: `os.modelOffMax`/`modelSeekMax` are `@[reducible]` Int literals (Code/os.lean:320); the Seek
   model order changed (whence==0 branch empty, then `e != 0`, `n < 0`, OffMax checks, SeekMax).
3. Not yet ported (still mention `os.model.*`/`unfold os.model.stat`/`arbitraryMode`/`ArbitraryInt`):
   StatS (wp_stat_dirS/absentS/fileS over `modelStat`: fsPathKind stub, fsOpen loop, fsFdKind,
   fsFstat, fsClose/fsDirClose, `filepathlite.Base.wp_lex`, `os.modelMode` = ty | Choose&bits:
   needs a `wp_modelMode` lemma over `ChooseUint64.wp_local`), NsAbove (`wp_stat_aboveS` must
   get a STRONGER post: err = nil → `*fileStat` with `ownFileStat` (Go's MkdirAll calls IsDir on it);
   modelStatAbove allocs `&fileStat{}` and sets name/size/mode), PORT-marked lines (Crash,
   CrashStSpec, NsS, NsFileS, NsSOk, NsChildS, RemoveAllSub, StatNE, Remove), RenameS (inline
   `&LinkError` alloc: `wp_alloc` then `linkError_fmtErrorOk`), Crash/CrashStSpec (`unfold
   os.fsFsync.impl` fails: use `wp_stub os.fsFsync.impl` at the call).
4. MkdirAll family (TODO comment in MkdirAllParts): `os.MkdirAll.wp_aboveS` (strong induction on
   the path length; Stat above, `mkdirall_parent`, VolumeName.wp_lex = [] so `len(parent) > 0`,
   recursion via `os.rootsAbove_parent`, `os.Mkdir.wp_notTree` with `wp_osPathKindAboveS`, Lstat
   above); `wp_spineS` (root case: Stat via `os.Stat.wp_dirS` on `osPathS R r` (cs = []), parent
   above or empty, `wp_notTree` with `wp_osPathKindS` (k = 0, `os.not_treeName_root`), Lstat.wp_dirS;
   cons case: as before but no PathKind step at the start and `mkdirall_parent` instead of
   `wp_mkdirAllParent`), `MkdirAll.wp_proofS` and `MkdirAllDir` the same way. The ENOTDIR error is
   an inline `&PathError{..., Err: syscall.ENOTDIR}` composite literal (alloc).
5. Remove/RemoveN: Go's `Remove` = `ignoringEINTR(unlink)`, then `ignoringEINTR(rmdir)`, then the
   ENOTDIR choice; reuse `os.wp_ignoringEINTR` (attempt = `fsUnlink`/`fsRmdir` stub, as mkdirAttempt).
6. Users outside: WAL TailWriter*/RepairFsync (modelOffMax), Proof/io/Copy*, walfs Boot/DSRename/
   DSRemove; KvNet/RaftNoAx/RaftWitness copies (`etc/copy-part.py`); links (`etc/gen-link.py` modes
   incl. --bboltfs; link_bbolt.py) and interfaces; build the importer cone.
7. stepFollower heartbeat timeouts (build7/8): compare with origin/lean at the same pin; probably
   not ours (the binder removal only drops instance hypotheses); check after the cone builds.
8. tcb-report before/after --check, `#print axioms`, review-trusted (R12), packet.md.

## Decisions taken (record in the packet)
- filepathlite: precondition-free lexical lemmas in a defs module instead of threading `isPkgInit`
  (no spec changes; the package's fact is `True`, its functions read no package variable).
- `supportsCreateWithStickyBit` translated (a constant; was opaque, i.e. stuck).
- `ownFile` gains `nonblock ↦□ false` (lead).
