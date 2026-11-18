# fmt soundness: handoff

## START HERE (2026-11-18, task 3 implemented; full build, gates next, then the land stop)
- Worktree /shared/etcd-grove-fmtfix, branch `fmt-soundness`; lean merged (d87c45b206, conflict only in
  etc/gates.sh: lean's batched collections kept, the errorf-wrap gate after them).
- Done: H0, the term gate, ErrorfWrap premise (commits ed402890f6..35c7b9f54d).
- Done (5a154a66c4): (a) `errOk` = `fmtErrorOk`'s text (type facts: `Error() string`, no `Format`);
  `fmt.ErrorfErrs`/`ErrorfErrsNot`/`ErrorfErrsTerm` premise `fmt.errArgsWf errs format args` (errors
  only under `%v`/`%s`/`%w` without `#`); 22 call sites by the macro `errargs_wf`; producers of `errOk`
  via `errorString_errOk` (gen-init.py templates changed, Init files regenerated).
- Done (next commit): (b) `ErrorfAny` DELETED; Create's `fmt.Errorf("%w (after: %v)", cerr, perr)` uses
  `ErrorfErrs`; the writer contract `io.writerStream*`'s error arm gains `errOkOrNil err`, passed through
  `PageWriter.flush/Flush`, `encoder.flush`, to `WAL.sync.specC`, `Close.specU`, `cleanupWAL` (arms 1-2:
  `fmtErrorOk err`); producers: `os.File.Write.wp_empty`/`wp_long` posts gain `fmtErrorOkOrNil err`
  (`os.wp_wrapErrno_ok`), the tail writers' `wp_tailWriteAt(W)`. No narrower option existed: the cleanup's
  error is formatted, so its producer (the sync's flush through the generic writer) must say it.
- Next: full build (/shared/tmp/fmtfix/full*.log), regenerate Links (`etc/gen-link.py` needs the build:
  run all modes, see etc/gates.sh l.54), rebuild; term gate (errorf-wrap-check: ErrorfErrs now REVIEWED);
  tcb --check --update (ErrorfAny.wp_proof gone; wp_New dropped from ErrorfErrs/ErrorfStrs/closeAll);
  collections; interfaces; gates; STATUS; land stop with old -> new texts.
- Pitfalls: `etc/gen-link.py` on a stale build emits garbage (it diffed bbolt too): build first. In a
  macro, `or_false`/`true_or` are ambiguous with `Iris.BI`; `trivial` on an `ArgWf` disjunction times out.

## Decisions (etcd-grove-03, 2026-11-18, after the refutation stop)
1. ErrorfWrap premise → `fmtErrorOk (.ok inner)` (no Format, `Error() string` signature, the WP), the same
   facts in `wrapErrIs`: APPROVED.
2. Item 3: option (a), the full cascade now (ErrorfAny's callers' posts gain `fmtErrorOk`: OpenDir.spec,
   Fsync.specDirS, os.File.Close.wp_dirS, os.Rename.specDirAnySnc, WAL.Close.specU, cleanupWAL;
   ErrorfErrs' sites `Format = none`); premise NOT on `fmt.argsOk`/`errorfVerbs` where the attack broke
   it: error arguments only under `%v`/`%s`/`%w` (no `#`). Keep post changes minimal and textual (wal-link
   edits the same specs); list every spec touched below.
3. ErrorfErrsTerm/ErrorfErrsNot (WalTester hypotheses): do NOT change now (asked of the user).
   SUPERSEDED: USER APPROVED (2026-11-18, via etcd-grove-03) fixing them on this branch so they are true of
   Go (premise only the errors/verbs the WAL uses, post `fmtErrorOk err`), the old -> new `etcd_wal`
   closed statement shown to the user BEFORE landing.
5. (etcd-grove-03, 2026-11-18) ErrorfAny: continue down the sync/writer path unless a narrower sound
   alternative exists (none found: see START HERE); keep spec changes textual, list every touched spec.
4. Key the gate's review list by constant if cheap.

## Specs touched (for the wal-link merge)
- `Spec/fmt/ErrorfWrap.lean`: premise `fmtErrorOk (ok inner)`; `fmt.wrapErrIs` + `Format = none ∧ Error = noArgStringSig`.
- `Proof/os/NsS.lean` `os.File.Close.wp_dirS`: post `emp` → `fmtErrorOkOrNil err`.
- `Spec/os/File__SyncS.lean` `os.File.Sync.specDirS`, `Spec/.../fileutil/FsyncS.lean` `Fsync.specDirS`:
  error arm `⌜err ≠ nil⌝` → `(⌜err ≠ nil⌝ ∗ fmtErrorOk err)`.
- `Spec/.../fileutil/OpenDir.lean` `OpenDir.spec`: failure arm gains `∗ fmtErrorOkOrNil err` (proof via
  `os.Open.wp_dirSOk`).
- `Spec/os/RenameAny.lean` `os.Rename.specDirAnySnc`: post gains `fmtErrorOkOrNil err ∗` after `osCallPerm 1`.
- `Spec/.../wal/WAL__cleanupWAL.lean` `cleanupWAL.spec`: third arm `Fin err` → `(Fin err ∗ fmtErrorOkOrNil err)`.
- Consumer patterns only: fileutil/wal `syncDir`, `WAL__renameWAL`, `WAL__ReadAll`, `WAL__cut`, `Create`,
  `WAL__cleanupWAL`, WalTester `durable/tryWrite`; `cache/v3/Base` (`ctxWrapErr_fmtErrorOk`,
  `isCtxErr_fmtErrorOk`), `rangeKeys`, `executeTxn`.
- Task 3 (a): `Spec/fmt/ErrorfErrs.lean` (`errOk` with the type facts, `fmt.errArgVerbs/errArgAt/errArgsAt/
  errArgsWf`, `errOkOrNil`, `errargs_wf`, `argWf_uint64`/`argWf_int` moved here from selectWALFiles);
  `Spec/fmt/ErrorfErrsNot.lean`, `Spec/fmt/ErrorfErrsTerm.lean` (premise); `Proof/fmt/ErrorfErrs.lean`,
  `Proof/fmt/ErrorfStrs.lean`, `wal/closeAll.lean` (no `wp_New` hypothesis: `errors.wp_New_errorString`);
  `Proof/errors/ErrorStringOk.lean` (`errorString_errOk`); generated Init files of wal, walpb, fileutil.
- Task 3 (b): `Proof/io/WriterStream.lean` (`io.writerStream`, `writerStreamP`, `writerStreamPNE`: error arm
  `⌜err ≠ nil⌝ ∗ errOkOrNil err ∗ B out xs`); `Spec/.../ioutil/PageWriter__flush.lean`, `PageWriter__Flush.lean`
  (spec, specNE: error arm `+ errOkOrNil err`); `Spec/.../wal/encoder__flush.lean` (spec, specP, specPNE: same);
  `Spec/.../wal/WAL__syncC.lean` (error arm `+ fmtErrorOk err`); `Spec/.../wal/WAL__CloseU.lean` (arm 1
  `fmtErrorOkOrNil err ∗`, arm 2 `+ fmtErrorOk err`); `Spec/.../wal/WAL__cleanupWAL.lean` (arms 1-2
  `+ fmtErrorOk err`); proved internal theorems: `os.File.Write.wp_empty`/`wp_long` (`Proof/os/OffLong.lean`,
  post `+ fmtErrorOkOrNil err`), `wp_tailWriteAt`/`wp_tailWrite` (TailWriter), `wp_tailWriteAtW`/`wp_tailWriteW`
  (TailWriterW), `WAL.sync.wp_core` (error arm `+ fmtErrorOk err`); `Spec/fmt/ErrorfAny.lean` and its proof
  deleted; `Create.wp_proof` takes `fmt.ErrorfErrs.spec` in place of `fmt.ErrorfAny.spec`.

## History

### Earlier START HERE (2026-11-18, checkpoint STOP: refutation)
- Worktree /shared/etcd-grove-fmtfix, branch `fmt-soundness` off lean 49bd7924e6; head = the checkpoint commit.
- Done (commit "fmt soundness (checkpoint)"): H0 — `Spec/fmt/ErrorfWrap.lean` conjunct conditional on
  `Unwrap`, `modelErrIs` with `errStrCell`; `Proof/fmt/ErrorfWrap.lean` a theorem; consumers repaired
  (targeted build + lean-check: ServerKVOn, rangeKeys, apply/Base, cache/Base, executeTxn green).
- Done: term-level gate — `etc/tcb-report.lean` emits `errorf` records; `etc/errorf-wrap-check.py --reuse`
  reads `.lake/tcb.json`; wired in `etc/gates.sh` (sec_tcb) and CI. Tested on the WAL Link group (49 s):
  flags ErrorfStrs/ErrorfAny/ErrorfErrs.
- STOP: the independent attack (axiom skill) REFUTED `fmt.ErrorfWrap.spec`'s premise (A: `inner` with a
  `Format` method; B: `Error()` of a non-`string` signature) — pre-existing, also in the old axiom —
  and confirmed ErrorfErrs/ErrorfAny refuted. Report to etcd-grove-03 lists the fixes and item 3's cost.
- Next (after decisions): ErrorfWrap premise → `fmtErrorOk (.ok inner)`; item 3 per the decision;
  full build; tcb --check --update; collections; interfaces; gates; STATUS.
- Pitfalls: /shared had 12 GB free after seeding; the build slots are often both busy.
- Build: `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-6d3.json build <targets>`
  (LEAN_NUM_THREADS=4); lean-check with `LAKE_OPTS=--packages=/shared/tmp/manifest-6d3.json`.

