# fmt soundness: handoff

## START HERE (2026-11-18, checkpoint STOP: refutation)
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

## Decisions (etcd-grove-03, 2026-11-18, after the refutation stop)
1. ErrorfWrap premise → `fmtErrorOk (.ok inner)` (no Format, `Error() string` signature, the WP), the same
   facts in `wrapErrIs`: APPROVED.
2. Item 3: option (a), the full cascade now (ErrorfAny's callers' posts gain `fmtErrorOk`: OpenDir.spec,
   Fsync.specDirS, os.File.Close.wp_dirS, os.Rename.specDirAnySnc, WAL.Close.specU, cleanupWAL;
   ErrorfErrs' sites `Format = none`); premise NOT on `fmt.argsOk`/`errorfVerbs` where the attack broke
   it: error arguments only under `%v`/`%s`/`%w` (no `#`). Keep post changes minimal and textual (wal-link
   edits the same specs); list every spec touched below.
3. ErrorfErrsTerm/ErrorfErrsNot (WalTester hypotheses): do NOT change now (asked of the user).
4. Key the gate's review list by constant if cheap.

## Specs touched (for the wal-link merge)
