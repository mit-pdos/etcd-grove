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

## Phase B progress (2026-11-13, the Phase B agent): next agent starts here

- **Step 1 (forms) done, commit `800a0789bc`**: `lateWBR` deleted (`bootOkR`'s `Hnew` at `fun _ =>
  mvcc.api.mvccW d.gx`); `srvDiskImageAt γ ρ id dd S σ i A D m M` holds the old body verbatim,
  `srvDiskImage := ∃ S σ i A D m M, srvDiskImageAt …` (`srvDiskImage_raft` and `stop_cleanup_image`
  unfold both); `wal.stopImage` gains `∃ l', isCommittedLogLb cl l' ∗ ⌜σ.b ≤ l'.length ∧ DurAgrees S
  l'⌝` (intro/elim restated), `stopCleanupImage.spec`'s `∃ S σ` block gains it, `run` passes
  `raftNode.stop`'s (`#Hdag`). Full build clean (17476 jobs, `/shared/tmp/restart-s56/phaseB-forms-full.log`);
  `tcb-report --check` matches (870, 4); `gen-interface --check` clean for every API; merged `lean`
  (k8s 7f-5) and **landed: `lean` 7b8c866a29** (gates all passed, `/shared/tmp/restart-s56/phaseB-forms-land.log`);
  then merged `origin-lean-3975` (notes only, 81's request) and landed it too.
- **Probes** (`Scratch/S56Probe.lean`, untracked): P1 (`restartOkD`, `restartOkD_facts`,
  `restartOkD_start`, `walReadFactsD` with I4 as `(snap = none ∧ base = (0,0)) ∨ walSnapAtBase σ`),
  P2 (`probe_P2_boot_storageR`: `boot_storage` with the image's `mvccImage D L c u` in place of the
  fresh law), P6 (`probe_P6_cs`, `probe_P6_idx`); P3 by reading, `/shared/tmp/restart-s56/p3-rows.md`.
  **P6 finding**: `bootOkR`'s `%Hraft` spells out `rnStartCfg`'s conjuncts but lacks `maxMsg`
  (`uint.Z cv.MaxSizePerMsg' ≤ 2^20`), which `rnRestartCfg` needs: `bootOkR`'s text must take
  `rnRestartCfg bv cv lok pv` (contract text: in the CP2 package; Go evidence as `rnStartCfg.maxMsg`'s
  docstring, both constructions call `raftConfig`, `TestMaxSizePerMsg`).
- **Probes not yet checked by Lean**: `Scratch/S56Probe.lean`'s P1/P2/P6 sections were written while the
  build ran and never elaborated. First thing: `LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json
  etc/lean-check.py -a Scratch/S56Probe.lean` (under the 64G cap) and fix.
- CP2 package draft (incomplete): `/shared/tmp/restart-s56/freeze-package.md` (HS1, the `bootOkR` slot +
  `rnRestartCfg`, srvRestartRows, H10's `cl.Recover` check done by reading, world assumptions). Missing:
  `NewServer.specR`'s Lean text, `srvBuiltR`, the A2 texts in tracked files, spec-reviewer, axiom skill.
- Next: check the probes; A2 texts (WalApi `wal.restartOk` + laws from P1; InvRestart `bootOkR`'s
  `Hwal` and `rnRestartCfg`, `srvRestartRows`; NodeStart `Hbc`/F3 from the facts; BootStore
  `boot_storageR` from P2; BuiltRestart `srvBuiltR`; `specR`; HS1 patch); finish the package; STOP (CP2).

## Phase B (go from etcd-grove-81, 2026-11-13): next agent starts here

S6a (step 5 + S6a-2) **landed: `lean` 1c3e201cd1** (approved by 81; merged `lean` d922d242f3 first,
gates all passed, `/shared/tmp/restart-s56/s6a-land2.log`). 81's go for Phase B (`NewServer.specR`):
any new trusted text or axiom stops for 81's review; proof-only checkpoints are landed by the agent
(`etc/land.sh`, merge `lean` first), each landing's hash reported.

Phase A's A2 texts and CP2 never happened (P1-P3, P6 not probed), so Phase B starts there. Order:
1. **Forms first (no stop; one full build; land as a proof-only checkpoint):**
   - `lateWBR` deleted (`E/InvRestart.lean:388`; `bootOkR`'s `Hnew` at `fun _ => mvcc.api.mvccW d.gx`).
     Note: `bootOkR` is contract text; deleting an alias is meaning-preserving, still list it.
   - `srvDiskImage γ ρ id dd := ∃ S σ i A D m M, srvDiskImageAt γ ρ id dd S σ i A D m M`, the body
     moved verbatim (plan §2.3); `StopShutdown.stop_cleanup_image` unfolds both.
   - `wal.stopImage` (`E/WalApi.lean:373`, sealed) gains `∃ l', isCommittedLogLb cl l' ∗
     ⌜σ.b ≤ l'.length ∧ DurAgrees S l'⌝`; `stopImage_intro` takes it. Source: `raftNode.stop.spec`'s
     post already has it (`Spec/.../raftNode__stop.lean:62`); `run` drops it (`EtcdServer__run.lean`,
     `wp_apply hRStop … as ⟨…, #Hwcert, -⟩`): name it, add it to `stopCleanupImage.spec`'s
     `∃ S σ` block (an extra premise its only caller discharges: a form), pass it to `stopImage_intro`
     (`StopShutdown.lean:718`).
2. **P1, P2, P3, P6 probes** in `Scratch/S56Probe.lean` (plan §4 A1), then the A2 texts (plan §4).
3. **CP2: STOP for 81** with the Freeze package (`/shared/tmp/restart-s56/freeze-package.md`): HS1
   (`auth.NewAuthStore.spec`, axiom restated; text `/shared/tmp/r2d-hs1-newauthstore.patch`),
   `bootOkR`'s WAL slot `wal.restartOk` (contract text), `srvRestartRows` (D3), `NewServer.specR`,
   and H10's `cl.Recover` check. spec-reviewer + `axiom` skill per the plan.
4. After approval: B2/B3 (`wp_proofB` over `SrvBoot`), CP3 stop before land.

## S6a-2 (2026-11-13, the S6a-2 agent): next agent starts here

- `lean` (51ee20f154: auth-schema-fix, k8s 7f-4/7f-5, the bbolt port) merged, `fc4ee3a900`
  (decisions.md: both appended sections kept; STATUS and status-history as `lean`'s).
- The fork pin 2eaeb872b is pushed: `etc/goose.py --check` passes **without** `ETCD_SRC`
  (`/shared/tmp/restart-s56/goose-check-s6a2.log`). The `ETCD_SRC` instruction below is obsolete.
- Done (S6a-2): `m1-s6a2.patch` applied (no adaptation needed: NewServer's hunk at +32 lines);
  `srvSnapRm` alias deleted, NewServer allocates at `snapRmM γt`; the `Spec/.../NewServer.lean`
  comment at `Hsdir` (the map's authority only; the directory is `bootOk`'s `Hsdo`); `srvSnapRO`'s
  pure part gains, last, `snap.snapDBPath ss = snap.snapDBPathOf cfg.DataDir'` (NewServer: `Hssp`);
  `srvDiskImage`'s directory part gains `snap.snapDBPath ssₒ = snap.snapDBPathOf dd` (the stop:
  `srvSnapRO`'s equation at its `DataDir` field, = `srvDataDir`'s `dd`).
- `idm = C.rn.id` was already closed by step 5 (`f14b569984`): `stopCleanupImage.spec` takes
  `srvMemberIDAddr C.s ↦□ C.rn.id`, `run` passes `srvSnapBagN`'s, `stop_cleanup_image` combines it
  with `srvSnapRO`'s `srvMemberIDAddr s ↦□ idm`.
- Verified at `615233ed56`: full build clean (17475 jobs, `/shared/tmp/restart-s56/s6a2-full.log`);
  `tcb-report --check` matches the baseline (870 axioms, 4 sorries: `lean`'s, no change;
  `/shared/tmp/restart-s56/s6a2-tcb.log`); `gen-interface --check` clean for every `etc/api` list.
  `etc/gates.sh`: everything passed but `featuregate` (lean's new k8s 7f-5 gate): its allow list
  named the etcd modules at the old pin 0b50f0426; updated to 2eaeb872b (the fork change touches only
  `snap/db.go`, `feature_gate.go` identical), `etc/featuregate-check.py` ok; gates rerun
  (`/shared/tmp/restart-s56/s6a2-gates2.log`): **all passed**.
- Final texts: `/shared/tmp/restart-s56/freeze-s6a.md` §3.2-S6a-2. Approved by 81 and landed
  (`lean` 1c3e201cd1).

## S6a: fork fix and step 5's image (2026-11-13, the S6 agent, fresh): next agent starts here

- **Fork fix (the user's decision via 81).** upamanyus/etcd@2eaeb872b (`goose-lean-snaplink`, local
  clone `/shared/tmp/restart-s56/etcd-fork`, on 0b50f0426 = origin `goose-lean`; **not pushed**):
  `SaveDBFrom` links (`os.Link`), `ErrExist` = kept file. Test `TestSaveDBFromConcurrentSameIndex`
  fails at 0b50f0426, passes at 2eaeb872b (`go test ./etcdserver/...` all ok). Pin bumped in
  `etc/goose.py` and the three examples' go.mod/go.sum (hashes computed from the local clone through
  `GIT_CONFIG_GLOBAL=/shared/tmp/restart-s56/gitconfig-fork GOPRIVATE=github.com/upamanyus/etcd`, an
  `insteadOf` to the clone); retranslation: 0 files. `goose.py --check --src
  etcd=/shared/tmp/restart-s56/etcd-fork` passes (`/shared/tmp/restart-s56/goose-check-snaplink.log`).
  **Until the user pushes the fork branch, run gates/goose with `ETCD_SRC=/shared/tmp/restart-s56/etcd-fork`.**
  Docstring, nonissue (fixed in the fork, `blocks-proof: yes`), decisions.md, freeze-s6a.md: updated.
- **Step 5's remaining part, done except the equation (S6a-2):** `srvDiskImage` carries the member's
  directory invariant at `γ.snapLoc id`, the removal counter's authority, `c ≤ i + 1`
  (`InvRestart.lean`); `stop_cleanup_image` builds it from `srvSnapOwn`'s `srvSnapRO`; the member-id
  link is a new premise of `stopCleanupImage.spec` (`srvMemberIDAddr C.s ↦□ C.rn.id`), which `run`
  discharges from `srvSnapBagN`. Forms in `questions.md`.
- Next (after the auth fix lands): S6a-2 (`m1-s6a2.patch`, the `srvSnapRO` and image equation, the
  NewServer comment), then Phase B.

## S6a item 4: soundness finding (2026-11-13, the S6 agent): next agent starts here

81 accepted the M1 forms (snapDirIs inside snapDirInv, snapDirOwn a definition, purgeFile unchanged,
the NewServer comment in S6a-2; `questions.md`) and asked first whether `img i` determines `D`, which
SaveDBFrom's M2 docstring paragraph assumes. **It does not**: `mvccImage`'s `imageOk` leaves the Key
bucket's compaction progress (`entsCutAt`), the compaction records and `u` free, and `imageRestAt`
holds the term key existentially. The difference is real in Go: an unfinished `scheduleCompaction`
at one applied index makes two merged snapshots at that index carry different data. With the double
rename, the invariant then claims `fileHolds p D1` over a file holding `D2`. No refutation found
(clients see the data only through the persistent `img`), but the docstring's argument (1) is false.
Finding, scenario and fixes: `/shared/tmp/restart-s56/s6a-imgfun-finding.md` (recommended: (A) the
fork's `SaveDBFrom` keeps atomically through `os.Link`). **Stopped for 81's decision. Step 5's
remaining part (below) is not started.**

## S6a review answered (2026-11-13, the S6a agent continued)

The S6a axiom review (READY WITH CHANGES) is answered; texts and reasons in
`/shared/tmp/restart-s56/freeze-s6a.md` §3.2-review, decisions in `questions.md` and
`notes/decisions.md` ("Restart S6a: the snapshot directory's right, and the double rename").
**Stopped for 81's review of the M1 texts.**
- Done: `snap.snapDirOwn`/`snap.snapDirIs` (`api/snap/Defs.lean`, defined, no axiom); `bootOk`'s
  `"Hsdo" ∷ snap.snapDirOwn (snap.snapDBPathOf cfg.DataDir')`; `snapDir_alloc` deleted; `SaveDBFrom`'s
  docstring (M2); `nonissues/etcd-snap-savedbfrom-concurrent-rename.md` with the test; m1, m2.
- **S6a-2 (with `NewServer.lean`, after the auth fix):** apply `/shared/tmp/restart-s56/m1-s6a2.patch`
  (`snapDirInv` holds `snapDirIs (snapDBPath ss) γd`; `snapDir_init` takes the right and the path
  equation; `snapDir_take` carries the record; NewServer's call passes `Hsdo`, `Hssp`). Only its
  `Net.lean` part was checked. Also: a comment next to `NewServer.spec`'s `Hsdir` pointing at
  `bootOk`'s `Hsdo` (the review's fallback ask, `Spec/.../NewServer.lean:305-308`, still says
  `snapDir_alloc`); then the deferred `srvSnapRO` equation and the image's (S6a-1 notes below).
- **Step 5's remaining part not started** (the image's `∃ ssₒ γm c, inv … ∗ monoNatAuthOwn γm 1 c ∗
  ⌜c ≤ i + 1⌝` at `srvImageM γ.authOn γ`, `InvRestart.srvDiskImage` + `StopShutdown.stop_cleanup_image`;
  the member-id link). Findings so far: `applyResStopR` holds `srvSnapOwn C.s C.ci B.E C.γr B.γ ai`
  (the snapshot index `ai`, named `ai0g` in `stop_cleanup_image`'s `icases Hres`), whose `srvSnapRO`
  has `srvMemberIDAddr s ↦□ idm`, `γr.raft.raft.snapLoc idm = some γd` and the invariant at
  `srvImageM γr.raft.raft.authOn γr.raft.raft`; the image is at `C.rn.id` and `C.ρ.rd.raft.raft`
  (`hρ`, `hγ : C.γr.raft.raft = C.rn.node` in the proof). Still open: `idm = C.rn.id` (lead below).
- Verified at `e338bf455a`: full build clean (17552 jobs, `/shared/tmp/restart-s56/s6a-m1-full.log`), `tcb-report --check` matches the baseline (865 axioms, 4 sorries: no change), `gen-interface --check` clean for every `etc/api` list, `etc/gates.sh` all passed (`/shared/tmp/restart-s56/s6a-m1-gates.log`).

## S6a-1 progress (2026-11-13, the S6a-1 agent)

Done (full build clean, 17552 jobs, `/shared/tmp/restart-s56/s6a1-full.log`; `tcb-report --check` matches the baseline: the opaque adds no axiom, and the baseline lists axioms and sorries only; `gen-interface --check` clean for every `etc/api` list; `etc/gates.sh` all passed, `/shared/tmp/restart-s56/s6a1-gates.log`): steps 1, 2, 3, 4 and 6 of the list
below; targeted builds clean (`SnapRO`, `SnapTake`, `InvBoot`, `InvRestart`, `InvRun`,
`EtcdServer__snapshot`, `…snapshotIfNeededAndCompactRaftLog`, `SnapApplyWalk`,
`EtcdServer__applySnapshot`, `ApplyAllSnap`, `EtcdServer__applyAll`, `EtcdServer__run`, `StopShutdown`,
`NewServer`, `EtcdServer__HardStop`). Final texts and the list of forms: `freeze-s6a.md` §3.2-final.
- `NewServer.lean` untouched: `srvSnapRm` stays as `abbrev srvSnapRm γm _γr := snapRmM γm` (SnapRO),
  and `bootOk`'s `Hssp` is left unused by its `iNamed Hb`.
- `snapshot`'s `Release` facts: `srvSnapDisk` split; the directory is the new `srvSnapDir s γm`
  (SnapTake), which `snapshot.spec`/`snapshotIfNeeded…specBatch` take with `monoNatLbOwn γm ai`;
  `applyAll`'s batch raises the counter (`snapRm_raise`) and derives it (`srvSnapDir_of_RO`,
  ApplyAllSnap).
- **Step 5 not done, and its equation cannot be done in S6a-1**: the equation `snapDBPath ss =
  snapDBPathOf cfg.DataDir'` in `srvSnapRO` breaks `NewServer`'s proof (it builds `srvSnapRO` with a
  fixed `refine ⟨…⟩` of the pure conjuncts and an `isplitr` chain), so the stop has nowhere to get it.
  Defer the equation (srvSnapRO and the image) to S6a-2. The rest of step 5 (the image's `∃ ssₒ γm c`,
  invariant, counter) can be done now in `InvRestart` + `StopShutdown` (`stop_cleanup_image`). Findings:
  - In `stop_cleanup_image`, `icases Hres` names the snapshot index `ai0g` and the ghost index `ai`;
    the image's `i` is the ghost `ai`, and `ai0g ≤ ai` (`hAG`), so `c ≤ ai0g + 1 ≤ i + 1`.
  - Write the image's invariant at `srvImageM γ.authOn γ` (form: then it is literally `srvSnapRO`'s at a
    restart, `γr.raft.raft = γ`), not `srvImageM false γ`.
  - InvRestart does not import SnapRO: write the removal fact inline
    (`fun j => monoNatLbOwn γm (uint.nat j + 1)`, defeq `snapRmM γm`) or move `snapRmM` lower.
  - Open: `γ.snapLoc id = some γd` needs `srvSnapRO`'s `idm` to be the image's `C.rn.id`; no lemma in
    the stop's context links `srvMemberIDAddr C.s` to `C.rn.id` yet (`srvSnapBagN`, `InvApplyAll`'s
    `isServerApplyAll` and `InvNet` hold `srvMemberIDAddr s ↦□ γn.id` at some `γn`). Lead:
    `InvNet.srvProcOk γn s id γd` has `srvMemberIDAddr s ↦□ id`, `rnNodeAddr (srvRAddr s) ↦□
    rnNodeIface γ` with `γ.id = id` and even `γ.node.snapLoc id = some γd`; `isRaftNode Er C.rn` holds
    the node's address at `C.rn`, so agreement may give `id = C.rn.id` if `rnNodeIface` determines the id.
- Probes P1-P3, P6 not done (not cheap: each drafts restart texts; plan §4 A1).

## S6a (decided 2026-11-13; `questions.md`): next agent starts here

(b′) decided by 81. The `bootOk`/`bootOkR` conjunct `⌜snap.snapDBPath bs.ss' = snap.snapDBPathOf
cfg.DataDir'⌝` was approved by the user (2026-11-13). Design and texts are in
`/shared/tmp/restart-s56/freeze-s6a.md` §3.

**S6a-1 (go; stay out of `NewServer.lean`, `AuthSrv.lean`, `InvStart.lean`, `ServerOn*.lean`,
`AuthCompRows.lean`).** In order:
1. `Proof/.../etcdserver/api/snap/Defs.lean`: `opaque snapDBPathOf [GooseExts] (dd : GoString) (id :
   w64) : GoString`, with a docstring giving the Go evidence (`bootstrapSnapshot` returns
   `snap.New(cfg.Logger, cfg.SnapDir())`, `bootstrap.go:252`; `SnapDir() = filepath.Join(MemberDir(),
   "snap")` and `MemberDir() = datadir.ToMemberDir(DataDir)`, `config.go:300,309`;
   `dbFilePath(id) = filepath.Join(s.dir, "%016x.snap.db")`, `db.go:117-119`; `s.dir` is set only in
   `New`, `snapshotter.go:34-40`). `etc/tcb-report.py --check --update` will list the new opaque, so
   record it in the package.
2. `E/InvBoot.lean:260` (`bootOk`) and `E/InvRestart.lean:409` (`bootOkR`): add
   `"%Hssp" ∷ ⌜snap.snapDBPath bs.ss' = snap.snapDBPathOf cfg.DataDir'⌝`. The text is approved
   exactly as written. The first start's proof (`NewServer.lean`) just drops `%Hssp` until S6a-2;
   check that the auth-fix files need no edit for that (an `icases` pattern may need `-`). If they do,
   defer and tell 81.
3. `E/SnapRO.lean`: `srvSnapRm γt γr` → `snapRmM γm j := monoNatLbOwn γm (uint.nat j + 1)`. In
   `srvSnapRO`, `srvSnapBoot` and `srvSnapOwn`, `⌜nt ≤ ai⌝ ∗ monoNatAuthOwn γt 1 nt` →
   `⌜c ≤ ai + 1⌝ ∗ monoNatAuthOwn γm 1 c`. Restate `snapDir_take` (it refutes `Rm i` for
   `c ≤ a + 1 ≤ i`, then raises to `i + 1`). Check `srvSnapOwn_mono`.
4. Follow the importers: `etc/importers.py --uses srvSnapRm --files` (`SnapTake`, `ApplyAllSnap`,
   `SnapApplyWalk`, `InvRun`, `EtcdServer__snapshot` (`Release`'s `Rm j` by raising `γm` to `ai`, not
   from `appliedAtLeast`), `Spec/.../EtcdServer__applySnapshot.lean:209` (a proved internal spec, a
   form), `EtcdServer__applySnapshot`, `SnapApplyDefs`). **`NewServer.lean` also uses `srvSnapRm`**
   (allocation): if the rename breaks it, keep a compatibility alias or defer that line to S6a-2, and
   tell 81.
5. The image: `srvDiskImage` (`E/InvRestart.lean:157`) gains `∃ ssₒ γm c, inv snapDirN (snapDirInv ssₒ
   γd (srvImageM false γ) (snapRmM γm)) ∗ ⌜snap.snapDBPath ssₒ = snap.snapDBPathOf dd⌝ ∗
   monoNatAuthOwn γm 1 c ∗ ⌜c ≤ uint.nat i + 1⌝`, with `γ.snapLoc id = some γd`. The stop chain
   (`E/StopShutdown.lean`: `applyResStopR`, `stop_cleanup_image`) carries `srvSnapOwn`'s parts there.
   The first start's `Hssp` reaches the image only through `NewServer` (S6a-2), so the stop needs it in
   the apply thread's persistent bundle (`srvSnapRO`: add the equation there; it is filled in S6a-2).
6. A lemma `snapDirInv_ss_congr : snapDBPath ss = snapDBPath ss' → snapDirInv ss … = snapDirInv ss' …`
   (Net.lean, or a new file of the server, so that Net.lean is not touched).
7. `etc/lean-check.py -a` on each file, then a full build under the lock and the cap. Then
   `tcb-report --check` (expect +1 opaque, `snapDBPathOf`), `gen-interface --check` for the APIs, and
   the gates. Then fill §3.2 of `freeze-s6a.md` with the final Lean texts and **STOP for 81's
   `axiom`-skill review** (target: the unchanged `SaveDBFrom` with two incarnations' snapshotters of
   one directory and a stale writer; `snapDBPathOf`).

**Also: probes P1-P3 and P6** in `Scratch/S56Probe.lean` (plan §4 A1). They are independent of S6a, so
do them while builds run.

**S6a-2 and Phase B** wait until the auth fix lands.

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
