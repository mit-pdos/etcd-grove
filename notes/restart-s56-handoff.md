# Restart S5/S6 handoff (branch `restart-s56`, worktree `/shared/etcd-grove-rs56`, from `lean` `90c3e25e77`)

Stage of etcd-grove-81: restart S5 (constructors: HS1 `NewAuthStore` over `authBoot`, `lateWBR`
deleted) and S6 (`NewServer` over both boots), against the restart/WAL interface
(`notes/wal-crash-handoff/restart-wal-interface.md`). S2 and C6 are deferred (the WAL collaborator).

## Phase: plan approved (D1-D4, etcd-grove-81 under the user's delegation, 2026-11-12; `questions.md`); Phase A, probe

- The WAL interface note got its §5 (S6 introduces `wal.restartOk`; C6 owns its body), commit `8f055a306b`.
- Baseline build at `90c3e25e77` + notes: clean, 17552 jobs, exit 0 (`/shared/tmp/restart-s56/base.log`).
- **P4 (R1) done, by reading: a gap that needs a decision** (`/shared/tmp/restart-s56/p4-snapdir.md`).
  The snapshot directory's authority (`ghostMapAuth γd`) and its files are locked in the stopped
  incarnation's plain `inv snapDirN (snapDirInv ss γd …)`. `γd` is fixed by raft's `Cluster.snapLoc`,
  so the restart cannot use a fresh name. Every fix changes three axioms (`SaveDBFrom`,
  `purgeFile`, `Release`). Recommended: (a) a cancellable invariant that the stop cancels, the image
  carrying `snapDirImage`, as its own sub-stage S6a. Reported to 81 (CP1, early: 81 asked for P4
  first, and for any trusted change beyond HS1/`bootOkR` to be reported).
- What reading found for P5 and P7 (no Lean yet):
  - P5: the image members' peer URLs move only through `ccRest` (conf changes) and `restAfter`
    (`InvRest.lean:304`). Proving the contract's clause (G) needs "the committed `L` has no conf
    change past the boot log that changes peer URLs", from `kvInv`/`srvRule`.
  - P7: `restoreAlarms.spec` takes `(r.lookup "alarm").getD ∅ = ∅`, under the axiom
    `v3alarm.NewAlarmStore.wp_proof`. At a restart the image's alarm bucket is
    `bkRestOf … L "alarm"`, so it needs "no alarm activated in `L`" (the workload, under
    `backendUnderQuota`). Otherwise the axiom must widen: a trusted change, so report it.
    `NewLessor` is the axiom `lease.NewLessor.wp_proof`, already restated for buckets with records.
- Baseline build: exit 0 (2026-11-12).
- R1 decided by 81: option (a), cancellable invariant, as S6a. **CP1 (2026-11-12) found (a) unsound or
  unprovable**: a stale `SaveDBFrom` of the stopped incarnation outlives `HardStop` + `pl.Close` (Go:
  `http.Serve` does not wait for in-flight handlers; model: `http.Serve_spec` keeps the handler and its
  `Rs` for good). Every per-incarnation invariant fails (the kept-file branch of the restarted
  incarnation's own `SaveDBFrom`). Proposed (b′): one invariant per member, allocated by the first start,
  carried by the image (persistent), reused at the restart through `snapDBPath bs.ss' = snapDBPathOf dd`
  (one new conjunct in `bootOk`/`bootOkR`); removal fact a member-level counter `snapRmM γm`; the three
  axioms unchanged (`purgeFile` never took the directory). Package: `/shared/tmp/restart-s56/freeze-s6a.md`.
  Waiting for 81.
- P7 proved in `Scratch/S56Probe.lean` (`probe_P7_alarm`, `probe_P7_auth`): the image's alarm bucket is
  empty and its auth buckets are `authBoot`/∅/∅ at every log (`restModel_keep`); no `NewAlarmStore`
  widening.
- P5 by reading: provable, no premise. A phase-2 invariant (the `members` bucket exactly the encodings of
  `r.mem`, peer URLs `memBoot`'s, `members_removed` empty) makes every `ccApplyOk` `AddNode` invalid
  (`membersOf_decode`: the id is present), and `restUpdateAttrs` keeps peer URLs (`withAttrs`). Builds on
  `RestConf.lean`'s phase 1 (`bootInv`); about 250 lines; not written.
- Not started: P1-P3, P6.

- Plan: `/shared/tmp/restart-s56/plan.md`: the statements old → new (§1 S5, §2 S6), the hard stops
  (§3), the order and checkpoints CP1-CP3 (§4), the files and collisions (§5), the decisions D1-D4 (§6),
  and the risks R1-R5 (§7).
- Decisions go in the worktree's `questions.md` (untracked).

## Next, in order (once approved)

1. A0: baseline build done (clean).
2. A1: probe (P4 done; wait for 81's decision on R1; P1-P3, P5-P7 next) `Scratch/S56Probe.lean` (untracked; P1-P7 of the plan). CP1: report.
3. A2: texts in the files that are not the auth fix's. CP2: Freeze package, spec-reviewer, axiom skill. STOP.
4. Phase B, only after the auth fix lands: merge lean, edit `NewServer.lean`/`AuthSrv.lean`. CP3: STOP before land.

## Build

`export TMPDIR=/shared/tmp`;
`flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G etc/timed-build.py --packages=/shared/tmp/manifest-ddc.json`
(retry once on 143). Targeted builds: the same command without `flock`, with the targets. Checks:
`LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json etc/lean-check.py -a FILE`.

## Pitfalls

- `NewServer.lean`, `AuthSrv.lean`, `InvStart.lean`, `ServerOn*.lean` and `AuthCompRows.lean` are being
  edited by the auth fix (`/shared/etcd-grove-authfix`). Do not edit them before it lands.
- `.lake/build` was copied during another build, so it is partly stale. The first build rebuilds it.
- `Scratch/` is untracked: never `git add -A`.
