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

## S5 leftovers done; S7 Scope written (2026-11-14, the S5/S7 agent): a fresh agent starts here

- **S5's leftovers (proofs and forms only, no trusted text):**
  - `authSrvTP_off`'s call site already took HS1's `Or.inl` (in `authStoreKit_off`): nothing left there.
  - `authStoreKit` (`E/AuthSrv.lean`) widened: its triple's auth bucket is `∅ ∨ (M = .off ∧ authBoot)`
    (mode-dependent: `authStoreKit_on` needs it empty, through `authSchemaSrv`). `authStoreKit_off` passes
    `Hr.1.imp_right And.right`, `authStoreKit_on` `Hr.1.resolve_right`. `NewServer.lean` passes `Or.inl`.
  - `NewServerR.lean` uses `hTP`'s kit directly (`Or.inr ⟨hMo, …⟩`). `wp_proofRG`'s premise `h30` is gone
    (the wrapper `wp_proofR` keeps it for `authSrvTP_off`). `authStoreKitR`/`authStoreKitR_off`
    (`NewServerRFacts.lean`) are deleted.
  - Docstrings: `NewServerR.lean`'s header (no more "skeleton"), `NewServerRFacts.lean`'s STATUS, and
    `SE/NewServerR.lean` ("linked, used by no closed theorem"). `notes/decisions.md`: "Restart S5: the
    constructors at a restart".
  - Verified: full build `/shared/tmp/restart-s56/s5-full.log`, then tcb `--check` and gates (see the report).
- **S7 Scope:** `notes/restart-s7-scope.md`, notes only. STOP for etcd-grove-81's review. Recommended: one
  member (`restart1`), in-process `Put`s of distinct keys, `HardStop`, restart, `Range`; no R2s-A. Est. 7-10 wk.

**Next, in order:** 81's answers on the S7 Scope (D-S7-1..6, N1/N2 for the user), then S7.0 (the Go program)
and S7.1 (the probe) in a new worktree. The proof cleanup (item 3 below) is still open.

## S6 B2 DONE: `NewServer.specR` proved and linked (2026-11-14, CP3 approved by etcd-grove-81): a fresh agent starts here

The restart constructor's spec is proved, with no `sorry` (`wp_NewServerR` in the server's `Link.lean`). It is
on `lean` (the hash is in the STATUS entry of 2026-11-14 and in 81's records). CP3 approved:
- `bootOk`'s `Hsnone` text (the first-start instance);
- raft's interface diff and `MemStorNamesRec`'s new name;
- the gate baselines (mode lit-mode etcdserver 156, bounds stock etcdserver 33).

**Next, in order:**
1. **S5's leftovers** (`/shared/tmp/restart-s56/plan.md` §1 and §4 B1-B3; `notes/restart-scope.md`, S5). HS1 and
   `lateWBR` are done (CP2, Phase B). What is left:
   - S5's call sites (`E/AuthSrv.lean`'s `authSrvTP_off`, an `Or.inl`);
   - widening `authStoreKit` itself to the auth bucket `∅ ∨ authBoot`, so that `authStoreKitR`/`authStoreKitR_off`
     (NewServerRFacts.lean, copies) go;
   - B3's callers and docstrings, and `notes/decisions.md` ("Restart S5/S6").
   Check against plan.md §1 what is not yet on `lean` before starting.
2. **S7 (R2s-A)**: follow the merged snapshot. `Hwpend` and the restart-only rows (`srvRestartRows`, row 4
   `rnSnapTermAbove`) are removed (`notes/restart-scope.md`, "S7"; 6-9 weeks est.). It needs its own Scope for
   81 first.
3. **Proof cleanup (follow-up, with the proof-cleanup skill):** factor the shared tail of `NewServer.wp_proofG`
   (`NewServer.lean`) and `NewServer.wp_proofRG` (`NewServerR.lean`) into lemmas. This is what brings the
   bounds stock (etcdserver 33, raised by +3 for the restart proof's copies of `wp_proofG`'s replicate
   stocks) back down, and the mode lit-mode count with it. Also: the private helpers copied into
   `NewServerR.lean`.

Pitfalls:
- `NewServer.lean`'s compile peaks at 8.1 GiB, `NewServerR.lean`'s at 8.6 GiB (2026-11-14); keep the 64G cap
  anyway (it once hit 80 GB).
- No bare `iframe` with the replicate stocks in context.
- `NewServer+R`'s link list entry is `NewServer`'s minus the four compaction-mode callees; keep them in sync.
- The lock invariant's `Hsn_inv` is spatial now: a new MemoryStorage method lists it in its `Unlock` frame.

## B2: both sorries proved, wp_proofR linked; CP3 checks running (2026-11-14, fourth B2 agent): next agent starts here

81 approved the raft-side generalization (questions.md; freeze package §11.8). Commit `f75195aa23` (WIP), then fixes.
- **Raft (API):** `MemStorNames.s0`. The lock's `Hsn` is `∃ s0, ghostVar γs.s0 ½ s0 ∗ (⌜sv = s0⌝ ∨ pr ≥ 1)`,
  now spatial: every method lists `Hsn_inv` in its `Unlock` frame. `memSnapNone γs sv₀`, `memSnapNone_open`
  at `sv₀`'s index, `memSnapNone_open_empty`, `memSnapNone_eq`. `Snapshot.spec`'s token is
  `t : Option SnapshotM`. `ApplySnapshot.spec` has four triples, `.2.2.1`/`.2.2.2` being the token variants
  (`wp_ApplySnapshot_gen` takes `w`). `NewMemoryStorage`'s token is at `memSnapEmpty`.
- **Users:** the kv/kvreconf/kvdurable examples (`none` for `false`, `memSnapNone_open_empty`). `InvBoot`'s
  `bootOk` `Hsnone` and `rnSnapOnce_of_tok`. `InvRunRes.rnSnapOnce`. `bootstrappedWAL__MemoryStorage` (the
  token variants, no `memSnapNone_open`). `BaseRestartStor.memStorRestarted` (`memSnapNone γs (walSnapCS σ cs)`).
  `NodeStart` (`srvMem_restartStorage` threads the token to `F`; `NodeStartSpecR`'s post returns it).
  `NewServerR` (`Hmsnone`).
- **`restart_snapOnceR` proved** over the token (`csPts_of_csOptA` new). It is restated: premises
  `memSnapNone γs (walSnapCS σ cs)` and `confStateIs cs …`, no certificate or log premises.
- **Link:** `NewServer.specR` moved to `Spec/.../NewServerR.lean` (text unchanged). `NewServer.wp_proofRG`
  is the proof, and `NewServer.wp_proofR` the wrapper with `NewServer.wp_proof`'s callees less the four of
  the compaction mode. Entry `etcdserver_NewServer+R` in `etc/link-lean-first-server.txt`, and
  `Link.lean` regenerated (`wp_NewServerR`).
- **Verified (commits `912b6d73ff`, `367565ac58`):** full build clean, 17482 jobs
  (`/shared/tmp/restart-s56/cp3/full4.log`). Peak memory 8.6 GiB `NewServerR`, 8.1 GiB `NewServer`
  (`cp3/report1.txt`, `report2.txt`). `tcb-report --check` matches (870 axioms, 4 sorries), and
  `wp_NewServerR` reaches no `sorry`. `gen-interface` changes raft only (`cp3/raft-interface.diff`); the
  other lists `--check` clean. Gates: `cp3/gates.log`.
- **Next:** CP3 report to 81; land only on 81's go.

## B2: `restart_peerURLs` proved; `restart_snapOnceR` STOPPED for 81 (2026-11-14, fourth B2 agent): next agent starts here

Branch `restart-s56`; **not landable** (one `sorry`: `restart_snapOnceR`, `E/NewServerRFacts.lean`).
- **`restart_peerURLs` proved** (P5), no statement change: `RestReplay`'s phase-2 invariant already existed
  (`memSync_boot`, `fold_sync`: past the boot log the members are `foldMem R` of the boot fold's);
  new pure lemmas in Facts (forms): `memBootFold_notin`, `memBoot_lookup` (the saved ids distinct),
  `bootFold_mem` (the boot entries put back `memBoot`'s members), `foldMem_peerURLs`; both prefix cases
  (`A` past the boot log, or within it). Facts now imports `RestReplay`. `NewServerR.lean` checks
  (`chk.sh -a`, 0 errors, 156 s).
- **`restart_snapOnceR`: 81 decided the raft-side generalization** (token "no write since attach" at the
  attached snapshot `sv₀`). Go confirmed (fork `2eaeb872b`, raft `565c2bd`): `bootstrappedWAL.MemoryStorage`
  (`bootstrap.go:741`) is `NewMemoryStorage`, `ApplySnapshot(wal.snapshot)`, `SetHardState`, `Append`;
  nothing writes the storage's snapshot before `run`'s `s.r.raftStorage.Snapshot()` (`server.go:755`;
  `s.r.start`, which owns `ApplySnapshot`, is at 801; raft's `RestartNode` only reads its `Storage`; the
  apply thread, `CreateSnapshot`/`Compact`, starts later). The MemoryStorage specs and
  `bootstrappedWAL.MemoryStorage.spec` are proved (no axiom, no sorry). **But the change reaches trusted
  meaning, so STOPPED before any edit**: `memStorRestarted` (BaseRestartStor.lean) is what the trusted
  `bootOkR`'s `Hrest` row promises; it holds `memSnapLb γs σ.b`, whose `monoNatLbOwn γs.pr 1` is the
  persistent write permission, so pr must stay 0 there (the row's meaning changes: stronger, still the
  proved post), and the detached `ApplySnapshot` must take the token instead of `memSnapLb γs 0`. The
  agreement on `sv₀` needs a new ghost name in `MemStorNames` (`MemStorNamesRec`, the registry's tuple, is
  in `bootstrapRestartContract`'s type through `memStorRegAuth M`). Reported to 81 with the design.

## B2 post done; `restart_snapOnceR` blocked (2026-11-14, third B2 proof agent): next agent starts here

Branch `restart-s56`; **not landable** (two `sorry`s left, both in `E/NewServerRFacts.lean`). Check loop as
below (`/shared/tmp/restart-s56/b2tail/chk.sh -a`, ~50-150 s; `lc.sh --fast -q -a` on the Facts file, seconds).
- **Done, checked (0 errors):** `wp_proofR`'s post (`NewServerR.lean`, from "the post: `srvBuiltR`" on):
  `srvBuiltRC .off`'s rows in order (`simp only [AuthC.isOn]` first: it also drops the trivially true
  `%Hρrd` and the `0 = 0` parts of `%HEr`), `#Hrdb` at `srvReadBuilt` with the store's log at
  `kvModel A`, `#Hkvi` through `srvKVInvsM_C`, `HBr` at `P := A.take σ.b` (`applyBuiltR .off` at
  `st₀ = ⟨0, γA.m0.1, 0, false⟩`, `g₀ = i`; the uber-applier's `isConsistentIndexer` by `srvCiC`'s own
  `stLoaded` conjunct, not `hLoaded`; `applyKV` at `restartKV` with `leasesKnown_noLease`; `srvRest`
  by the new `srvRest_restart`; `srvApRes`'s `srvMemOk` by the new `srvMemOk_of_keys` from `Hpurl`),
  the lessor's records (`hrecs` through `rbData_real_lookup`). G's comment block and the first-start
  `token_alloc` for `Hwpend` are gone. New in Facts (forms): `restartBk_eq`, `srvRest_restart`,
  `srvReqs_of_recs`, `srvMemOk_of_keys`; Facts now imports `SnapApplyRest`, `SnapApplyKVLemmas`.
- **`restart_noGrant` proved** (`kv_log_plain` + `kvTableOf_plainM`).
- **`srvRestartRows` parenthesized** (81's decision on the reviewer's finding): `|==> (rnSnapTermAbove γn
  ∗ srvWinPend s γr γn)`; `wp_proofR` takes both from one `imod`; recorded in decisions.md ("Restart S6 B2")
  and the freeze package §11.7.
- **Left:** `restart_peerURLs` (P5, ~250 lines, not started; the plan is in the sections below) and
  **`restart_snapOnceR`, which is unprovable from raft's current `MemoryStorage` specs (reported to 81)**:
  `rnSnapOnceR` asks `Snapshot()` to answer exactly index `|A.take σ.b| = σ.b`, but the restarted storage is
  attached (`NodeStartSpecR`'s post: `memStorInv`), and `MemoryStorage.Snapshot.spec` in the attached mode
  gives only `c ≤ index` (`memCompacted γs c`) and `index = 0 ∨ snapshotValid …`; the one exact answer it
  has is `b = true → sv = memSnapEmpty` under `memSnapNone` (pr at 0), which a restart cannot hold (the
  stored snapshot is the WAL's, so the invariant's `Hsn` needs `pr ≥ 1`; `memStorRestarted` already has
  `memSnapLb γs σ.b`, which includes `pr ≥ 1`). Recommended fix (a raft-side spec change, so 81's call):
  generalize the "no write since attach" token from `memSnapEmpty` to the attached snapshot (the invariant's
  `Hsn` as `sv = sv₀ ∨ pr ≥ 1` with `sv₀` the snapshot at attach, `Snapshot`'s `b = true → sv = sv₀`), the
  restart's `memStorRestarted` keeping `pr` at 0 until `run` opens it (`rnSnapOnceR`'s `|==> memSnapLb γs 0`).
- Then: link, measure peak, full build, tcb, gen-interface, gates; STOP before landing (CP3).

## B2 proof in progress (2026-11-14, second B2 proof agent): next agent starts here

Branch `restart-s56`; **not landable** (four `sorry`s: tcb --check). Files: `E/NewServerR.lean`
(`NewServer.wp_proofR`, statement unchanged; one new callee hypothesis `h30 : auth.NewAuthStore.spec`)
and `E/NewServerRFacts.lean` (sub-facts; now imports `AuthSrv`). Check loop:
`/shared/tmp/restart-s56/b2tail/chk.sh -a` (= `lc.sh --fast --split -q -a` on `NewServerR.lean`,
filtered by `/shared/tmp/restart-s56/b2tail/err.py`: each message's header and its goal's tail; `N=60`
for more lines). **Always `-a`**: without it an edit in the middle reports "stopped when the edited
declaration was done, 0 errors" while later blocks still fail. A full check of the file: ~50-120 s.

**Done, checked (0 errors; `sorry` at `NewServerR.lean:2019`):** everything of `wp_proofG`'s tail up to
its post (`unfold srvBuiltG`, G line ~2420), adapted:
- the lessor's aftermath: `γlt` at `(appliedTable ρ.rd A).ids`, no `lessorAt_empty` (the recovered
  snapshot `HlAt0`, NewLessor's), `Hrbo` normalized to `(rbData d.P D).insert "lease" ((D.lookup
  "lease").getD ∅)` (the lessor's post unfolds `rbData`'s lookup to `Option.filter`);
- `mvcc.api.New.spec` at the image's state `srvApi.stAt (kvModel A) (crevOf A)`, `u` general (an
  unfinished compaction resumed through the unset hook, `Hhk0`/`Hupre`/`Hupost`, `commitReq_true`),
  `Ls = (appliedTable ρ.rd A).ids`, no item (`LogNoLease` from `kv_log_plain`); the store invariant by
  the new `restartStore_holds` (Facts; `bootStore_holds`' restart form);
- the auth store: the mode `off` from `hTP`'s `M.isOn = false` (`isOn_false_iff`), the kit
  `authStoreKitR` (Facts: `authStoreKit`'s body copied, the auth bucket `∅ ∨ authBoot`, built by
  `authStoreKitR_off` from `h30` with HS1's second disjunct), its premise by `imageRestAt_auth` (Facts);
  `restoreAlarms` by `imageRestAt_alarm` (Facts); no `restBootBk_of_fresh` (the buckets after the
  constructors stay `(((((rbData d.P D).insert lease (D's)).insert auth authBoot).insert authUsers
  ∅).insert authRoles ∅).insert alarm ∅`: relate them to `restModel … A` at `srvRest`);
- the compactor's branch dead (`exact absurd hcmpT (by decide)`), the `cmp` reader branch dead;
- the node's names: `Hrnames` has 17 parts at a restart (`Hrnt0 Hrnc0 Hrns0` added);
  `srvRestartRows` used right after (`HsTA` to the installer, `Hwpend` kept for the post). **Its text
  parses as `(|==> rnSnapTermAbove γn) ∗ srvWinPend s γr γn`** (the `|==>` binds tighter than `∗`):
  harmless for the proof, but the trusted row is not what its docstring says (report to 81);
- the snapshot directory from the image (`Hsdimg`: `ssₒ γd γt ct`, `snapDirInv_ss_congr` with `Hssp`,
  `Hsloc`), the counter `Hγt : monoNatAuthOwn γt 1 ct` with `ct ≤ i + 1`, in `HsnapB : srvSnapOwn s cil E
  ρ.rd γA (W64 0 + W64 |A|)` (route (C); was `srvSnapBoot`);
- the read names: `γk.hi` updated to `|kvModel A|`; the writer's facts at `kvModel A`; the indices by
  the new `srvIndices_allocR` (Facts: the ghost applied index at `i`, `appliedLogAt γr i (kvModel A)`;
  Go's atomic fields stay 0, the invariant asks `v ≤ a`); the certificates by the new
  `kvCertInv_allocR` (Facts: `hi = |kvModel A|`, `#HkcA : kvCert ρ.rd.kv (kvModel A)`);
- `bootKVOf false` → `restartKV ρ.rd.kv A` everywhere (the environment `srvErM`);
- `run`'s snapshot: `HlastT : lastTermIs (A.take σ.b) σ.base.term'` (`restart_lastTerm`) and
  `HsnapR` (`restart_snapOnceR`, Facts, **sorried**), in place of `srvBuildGap`/`Hsnone`;
- `lease.srvInvAt false s E m (recMap (recs.zip ls), ∅, recTTLs minTTLsecs recs)` (`HLsrv`, from
  `HlAt0`); no `leaseTTLRowR`; the post's existentials end with `at₀ := σ.base.term'`; `HBF` dropped.

**Next, in order:**
1. The post. `wp_proofG`'s assembly from `unfold srvBuiltG` on is in the block comment after the proof
   (and `/shared/tmp/restart-s56/b2tail/post-tail.lean.txt`). Retarget it at `unfold srvBuiltR
   srvBuiltRC` (rows: `AuthCompRows.lean:203`). Differences from `srvBuiltG` (ServerOn.lean:163):
   `srvFieldsBuilt` (not `NA`), `srvReadBuilt` (not `NK`), `srvKVInvsC .off` (not `srvKVInvsM`),
   no `Hua`/`Hsnapb`/`Hloop`/`Happly` at top level: they go into `HBr : srvBuiltRestartR .off s γA cil b
   E ρ.rd γrn 0 σ.base.term' 0 (restartKV ρ.rd.kv A)` with `P := A.take σ.b` (`List.take_prefix`,
   `HlastT`), `⟨msR, HmsR, HsnapR⟩` (rewrite `γrn.node.reg`, `γrn.γs` by `Hrn1`, `Hrn8`; `γrn.a0` by
   `Hrna0`; `|A.take σ.b|`), `Hloop`/`Happly` (at `A.take σ.b` already), `applyBuiltR .off … A (W64
   |P|)` (P3's table, `/shared/tmp/restart-s56/p3-rows.md`: `applyThread` at `γA.m0.1 = i` from
   `bootOkR`'s `Hthr`/`Hm0` and `loopOk` since `|P| ≤ i`; `srvAppliedOwn`/`appliedLogAt` at `i` from
   `Haown`/`Hal0`; `kvRunM false ρ.rd 0 0 A x₀` = `kvRun` from `Hkhi2` (now at `|kvModel A|`),
   `#HkcA`, `HAr`, `x₀.chain = ch0`, `x₀.crev = crevOf`; `srvRest E ρ.rd A`: at `lg = false` the
   bucket map above as `restModel 0 boot A` through `imageRestAt`'s `bkRestAtL` (`Himg`), at `lg = true`
   the leased arm (`ltHalf` from `HltS`, `srvGrantable`, `srvReqs` from `#HlReq`, `srvEver` from
   `HlEv : leaseEver γl (recs.map (·.1))`); `srvApRes s ρ.rd A` needs P5), and `HsnapB`. `HEr`'s
   `uint.Z c₀ ≤ uint.Z ai₀ ∧ γn.pre = [] ∧ ai₀ = 0`; `Hwpend` from `srvRestartRows`. The lessor's
   `leasesLive` (G's tail, `iexists []`): `iexists (appliedTable ρ.rd A).ids`, the items empty by
   `hpi`/`LogNoLease`, `Hlown : leaseOwn γl Lr (pendItems … )` already at `∅` (`rw [hpi]`), `Hlt1`.
   The spec's lease existential: `iexists recs, ls, minTTLsecs`, `HLsrv`, `Hls`, and `hrecs` at `D`
   by `rbData_real_lookup d D _ (by decide)`.
2. The sub-facts (`NewServerRFacts.lean`, all `sorry`): `restart_peerURLs` (P5, ~250 lines; also gives
   `srvApRes`'s members at `A`), `restart_noGrant`, `restart_snapOnceR` (new: open `memStorInv` for
   `memStorAt` as `rnSnapOnce_of_tok` does, `MemoryStorage.Snapshot.spec` at the restarted storage's
   justification; may need `memStorMeta`/`memCompacted γs σ.b` from `NodeStartSpecR`'s post: a form).
3. When no `sorry` is left: link (`etc/gen-link.py --server`, `etc/link-lean-first-server.txt`; the new
   callee `h30` is `NewAuthStore`'s axiom, already in Link), measure the full compile's peak, full
   build, tcb --check, gen-interface, gates; STOP before landing (CP3).

Forms this session (questions.md): `restartStore_holds`, `srvIndices_allocR`, `kvCertInv_allocR`,
`imageRestAt_auth`/`imageRestAt_alarm` (the P7 probes), `authStoreKitR`/`authStoreKitR_off` (a copy of
`authStoreKit` widened to `authBoot`; cleanup: widen `authStoreKit` itself once `NewServer.lean` is
rebuilt anyway), `restart_snapOnceR` (stated, sorry), `wp_proofR`'s extra hypothesis `h30`, the
private helpers of `NewServer.lean` copied into `NewServerR.lean`.

## B2 contract rows done (2026-11-14, the B2 agent): next agent starts here (write `wp_proofR`)

**Landed: `lean` 6b99efd348** (full build clean, 17479 jobs; tcb --check 870/4; gen-interface clean; gates all passed: `/shared/tmp/restart-s56/b2rows/`). 81 approved the restatement (questions.md; decisions.md "Restart S6 B2", "B2 contract rows"; freeze
package §11.6): `bootOkR` now has `bv.lg' = cfg.Logger'` in `%Hraft`, `"Hlate" ∷ mvcc.api.mvccWReg d.gx`
and the last row `"#Hbfile" ∷ backend.bFile d.γB (config.backendPathOf cfg.DataDir')`, all `bootOk`'s.
**The skeleton `E/NewServerR.lean` is removed from the tree** so that no `sorry` lands: restore it first,
`git show c081768592:Proof/go_etcd_io/etcd/server/v3/etcdserver/NewServerR.lean >
Proof/go_etcd_io/etcd/server/v3/etcdserver/NewServerR.lean` (statement unchanged; body `sorry`). Then
follow "B2 plan from the reading" below; with the three rows the boot section has what it needs from the
contract (`Hrlg` → `Hrzl` as in G; `Hlate` straight to `boot_storageR`; `Hbfile` for `srvSnapRes`).
Do not land while the file has a `sorry` (tcb --check).

## B2 blocked on `bootOkR` (2026-11-14, the B2 agent; resolved above)

Reading `wp_proofG` against `bootOkR` before any Lean (no edit to `E/NewServerR.lean`, still the skeleton
`c081768592`): **three rows the restart proof needs are missing from the restart contract's `bootOkR`**
(trusted text, `E/InvRestart.lean:404`). STOP for 81 (questions.md, "B2: bootOkR gaps").
1. `%Hraft` lacks `bv.lg' = cfg.Logger'` (`bootOk`'s, premise-fixes-6). `NodeStartSpecR` takes
   `#Hlgz : zapLoggerOk bv.lg'` (`newRaftNode` logs through `b.lg`); `rnRestartCfg` gives only
   `bv.lg' ≠ null`, so no proof can give it. Go: `bootstrapRaftFromWAL` sets `lg: cfg.Logger`
   (`server/etcdserver/bootstrap.go`, as `bootstrapRaftFromCluster`).
2. No `"#Hbfile" ∷ backend.bFile d.γB (config.backendPathOf cfg.DataDir')` (`bootOk`'s last row). specR's
   post needs it: `srvBuiltR` → `HBr` (`srvBuiltRestartR`) → `srvSnapOwn` → `srvSnapRes`'s last conjunct,
   at the backend `bootstrap` just opened (`d.γB` is fresh: the image cannot give it). Go: both paths
   open the backend in the shared `bootstrapBackend(cfg, haveWAL)` at `cfg.BackendPath()`.
3. `"Hlate" ∷ mvcc.lateReg d.gx`, where `boot_storageR` (mvcc's `etcdStorage_open.law`) takes
   `mvcc.api.mvccWReg d.gx` (sealed `@[no_expose]`, by definition `lateReg`). Same meaning; either restate
   the row in `bootOk`'s form or add an mvcc API law `lateReg gx ⊢ mvccWReg gx` (EtcdBackend.lean).
Recommended: one restatement of `bootOkR` with all three in `bootOk`'s form (strengthens a premise of the
unlinked `specR` only; no axiom; tcb count unchanged); then B2 proceeds.

**B2 plan from the reading (for after the fix).** Write `wp_proofR` as a copy of `wp_proofG`'s body
(`NewServer.lean:389-2682`) with `on`/`cmp` replaced by `false` (perl, not after `.`/before ` :=`: `.on γa`,
`cmp :=`, `.cmp` are fields/constructors), the image binder `M` named `Mr` (the proof names an auth mode
`M`), and the private helpers (`newServer_cmp_peek`, `rep_join`, `rep_cons1`, `mvccReaders_rep`,
`rep_cast`) copied. Boot section (418-546 of G) replaced:
- the image: `iunfold srvDiskImageAt at Himg`; `wal.stopImage_elim` (σ.b ≤ i ≤ commit, `StorageHolds`,
  `walSnapCert`, a committed log), re-intro for `wal.restartOk_start`; `HρRaft`, `restartNames`
  (`ρ.rd.raft = ρo.rd.raft`) give `pre = []`, `ai0 = 0`, `uint i = |A|`;
- the contract (`HbootR` at `σ i A D Mr`): antecedent from the image, `Hbco`/`Hfnc`/`Hdwd`/`Hbwb`,
  `Hdisk` (`dbOpensOk`, `walSaveOk`), `restart_clusterVerLogOk`; **clause (G)** (peer URLs at `A` the boot
  log's) is P5's phase-2 RestConf invariant (~250 lines, not written); the existential at `ρo.rd.kv`
  (`mvccImage` is persistent: keep it for `boot_storageR`);
- the WAL: `wal.restartOk_start` at `l₀ = srvLE ⟨γ,[],0⟩ (A.take σ.b)` (committed: from `srvRLogLb`'s
  `isCommittedLogLb`, prefix as in `NodeStart.lean:1147`);
- the node: `raftNode_of_RestartNode` at `ctxs = []` (`pv = []`), `cs` from `Hrest`, `confStateIs cs
  (simple γ.cfg)` from the image's `∀ cs, v3ConfStateIs D cs → confStateIs cs mb` and `mb = simple γ.cfg`
  (`srv_confAt_simple_ind`, SrvRaftLog.lean:1082, and `confAt_agree`), F3 by `walReadFacts_F3`,
  `restart_cs_bound`, `restart_idx`;
- the store: `boot_storageR` at `kvModel ρo.rd.kv A`, `crevOf`, `u` (`u = false` at `cmp = false`: a
  lemma from `imageStOk`/the log having no compaction, to find), `mvcc.api.New.spec` at
  `stAt (kvModel A) crev`, `Ls = Lr` (the lease bucket's ids), its item premise from `LogNoLease
  (kvModel A)` (the KV invariant's `plainLogM`, as `SnapApplyWalk.lean:599-608`);
- the lessor: `NewLessor.spec` at the image's `lease` bucket records (`recs`, `reqOf` from the image),
  `Lr`; its `lessorAt γl 0 (recMap …)` is specR's `srvInvAt` snapshot;
- rest buckets: G's `hDl`/`HDr`/`restBootBk_of_fresh` (1096) replaced by `imageRestAt`'s buckets;
- the snapshot directory (G 1230-1261): the image's `inv snapDirN …` via `snapDirInv_ss_congr` and
  `Hssp`, its counter `c ≤ i + 1` for `srvSnapOwn` at `0 + W64 |A|`;
- the post: `srvBuiltR` (= `srvBuiltRC .off`) directly, `HBr` from P3's rows
  (`/shared/tmp/restart-s56/p3-rows.md`: `applyBuiltR` at `A`, `srvRest`'s leased arm the largest item,
  `srvApRes` at `A` from P5's invariant, `rnSnapOnceR` at `|P|`: `NodeStartSpecR`'s post may need the
  snapshot token, a form), `Hwpend` and the installer's `rnSnapTermAbove` from `srvRestartRows`; no
  `leaseTTLRowR`, no auth-on conjunct; `lease.srvInvAt` at the recovered snapshot.
Suggested order: P5's invariant and clause (G) first (a lemma file), then the boot section to the node,
then the tail by `lean-check --fast --split` errors, sorried sub-facts as named lemmas in a separate file.

## Route (C) and the CP2 landing (2026-11-14, the route-C agent): next agent starts here (CP2 landed)

81 decided route (C) for finding 1 (`questions.md`; freeze package §11.1a, superseding (A)).
- **Done, commit `033c31e5fd`**: `srvSnapOwn`'s index is the apply thread's ghost index `g`
  (`c ≤ g + 1`): `applyAll.specBatch` (pre `g`, post `g'`; `snapRm_raise` takes the ghost bound and
  `ai ≤ g`), `applyAll.specSnapM` (pre `g`; `snapDir_take` from `hgi : g < sv.Index`), `applyResR`,
  `applyResStopR` (the stop's image bound now direct), `srvRestartAtR` (at `g₀`), `srvBuiltRestartR`'s
  row at `ai₀ + W64 |γn.a0|` (`start` rewrites it to `applyBuiltR`'s `g₀`). `applyRes`/`applyStart`
  (InvRunRes) and `applyResOn`/`applyStartOn` (RunOn) unchanged: their `ai` is the ghost index. No
  trusted text changed. Targeted build clean (`/shared/tmp/restart-s56/routeC/targeted.log`).
- Merged `lean` (570cea0725, k8s 7f-3b mvcc); STATUS entry added (ten kept, oldest to status-history).
- Verified (after the merge): full build clean, 17479 jobs (`/shared/tmp/restart-s56/routeC/full.log`);
  `tcb-report --check` matches the baseline (870 axioms, 4 sorries; `routeC/tcb.log`); `gen-interface
  --check` clean for every `etc/api` list.
- **Landed: `lean` 77f542f56c** (`/shared/tmp/restart-s56/routeC/land2.log`, gates all passed). The
  first land.sh failed two gates, both from `NewServer.specR` (CP2): bounds +6 (its copies of specG's
  `threadBound`, `receiptBound` x2, `etcdMaxRequestBytesOk`, `maxTxnOpsOk`, the `srvServeRes`
  replicate) and mode +3 (its auth-off literals); baselines raised and specR classified `lit-mode
  unmoved` (commit 77f542f56c; `questions.md`, a form for 81's checkpoint review).

### B2: decided by 81 (2026-11-14): the fallback, a separate `NewServer.wp_proofR`

81 confirmed the gate baselines and decided D1's fallback (`notes/decisions.md`, "Restart S6 B2"):
`NewServer.wp_proofR : NewServer.specR` in its own file `E/NewServerR.lean` (never in `NewServer.lean`,
whose compile hit 80 GB; check peak memory, keep the 64G cap, 2^28 counts symbolic, no bare `iframe`
over replicate lists), reusing `raftNode_of_RestartNode`, `wal.restartOk_start`, `boot_storageR`.
Unlinked until done; land proof-only checkpoints via `land.sh` only when no `sorry` sits under a linked
result **and** `tcb-report --check` matches (a `sorry` anywhere in the repo changes the baseline, so do
not land a file with a `sorry`).
- **Skeleton, commit below (not landed: it has a `sorry`)**: `E/NewServerR.lean`, `NewServer.wp_proofR`
  with `wp_proofG`'s callee hypotheses at `authSrvTP false`/`uberKitM false`, the four compaction-only
  ones dropped (`cmp = false`); body `sorry`. Imports `NewServer` (the public olean: proofs not loaded)
  and `BuiltRestart`. Builds (1.7s). Next: `intro` `specR`'s binders, `wp_start`, `iNamed Hpre`, then
  follow `wp_proofG` from line 418 with the restart's boot steps (B2 map below), checking with
  `LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json etc/lean-check.py --fast --split
  Proof/go_etcd_io/etcd/server/v3/etcdserver/NewServerR.lean` under the cap; measure the full compile's
  peak (`etc/timed-build.py` + `etc/build-report.py`).
- **Follow-up (proof cleanup, after `wp_proofR` is done):** factor the shared tail of `wp_proofG` and
  `wp_proofR` into lemmas.

### B2 map (for the next agent)

`NewServer.wp_proofG` (`E/NewServer.lean:277`, ~2700 lines) uses the first-start boot rows in a few
places only (line numbers at 77f542f56c):
- 418-700: the bootstrap call (`Hboot`, 444-446: `Hrauth`, `Hwdf`), the WAL (`wal.bootOk_start`, 476),
  the meta rows (`Hmeta`/`Hmsmeta`, `HmEmpty`, `Hm0`, `Hthr` 478-485), the node (`Hnboot`, `Hraft`,
  `raftNode_of_StartNode`, 514-542), the store (`boot_storage`, 672-700, `HnoCmp` 688);
- 1230-1261: the snapshot directory (`Hsdo`, `Hsdir`; at a restart: the image's invariant through
  `snapDirInv_ss_congr` and `Hssp`, the image's counter for the `srvBuiltRestartR` row, route (C):
  `c ≤ i + 1 = |A| + 1`);
- 1613 (`Hsnone`), 1996-2019 (`Hrauth`'s later use), 2212-2359 (the apply rows at `[]`, `Hlog0`,
  `Hthr`); `Hkvinv` 1578-2226 (unchanged text).
The tail between is shared but runs in the context the boot built. Numbers for D1's fallback decision:
a lemma-factored `wp_proofB` must thread the bootstrap's whole context (`bootOk` and `bootOkR` differ in
~25 named rows); a separate `wp_proofR` copies ~2700 lines and adapts ~400. Recommendation to ask 81
first: the fallback (separate `wp_proofR` reusing `raftNode_of_RestartNode`, `wal.restartOk_start`,
`boot_storageR`), since the factoring would touch every step of the frozen first-start proof.
- NodeStart's `Hbc` from I3: not needed for B2. `NodeStartSpecR`'s `σ.b ≤ |A₀| ≤ σ.commit` follows from
  the image (`wal.stopImage`'s `σ.b ≤ i ≤ σ.commit`, `uint.Z i = |A|`, `A₀ = A`).
- **For B2**: the restart's `srvBuiltRestartR` row is `srvSnapOwn … (0 + W64 |A|)`, i.e. `c ≤ |A| + 1 =
  i + 1` with the image's `c ≤ i + 1` (`uint.Z i = |A|`, the image's) -- no WAL link needed.

## Route (A) for finding 1: superseded by route (C) (2026-11-13, the CP2-fix agent)

81 approved route (A) (and the forms; the obsolete generator is deleted). Before any edit, reading
the sites showed (A) is not the small change §11.1 estimated:
1. `applyAll` raises the counter to Go's new applied index `ai'` after **every** batch
   (`EtcdServer__applyAll.lean:172`, `snapRm_raise`, for a possible `snapshot`'s `Release`), not only
   when a disk snapshot is taken: in the ghost state `c` tracks the applied index, so `c - 1 ≤ WAL
   base` is false. (A) must first move the raise into `snapshot.spec` (the counter's authority in
   and out, raised after `SaveSnap`), and through `snapshotIfNeededAndCompactRaftLog.spec`.
2. The stop cannot compare: `Close` consumes `walRecs` (the trusted `isWalStorage` law), inside the
   raft loop's `onStop` (`raftNode__onStop.lean:73`), and `rnWalClosed` is the opaque `walFiles`. The
   apply thread's `walBaseLb` would have to be handed to `onStop` through `raftNode.stop`'s
   protocol (`rnWalTokA`/`rnStopClaim`/`rnDurInv`) to get `⌜k ≤ σ.b⌝` into the stop's escrow.
Proposed instead, route (C): index `srvSnapOwn`'s bound by the apply thread's **ghost** index `g`
(`c ≤ g + 1`) in place of Go's `ai`. Every use holds: `applySnapshot` already has the snapshot strictly
above `g` (`applyAll.specSnapM`'s `uint.Z g < uint.Z sv.Index`, `hgi`), so `snapDir_take`'s `c ≤ j`
follows; `applyAll`'s raise to `max c ai'` stays `≤ g' + 1` (`ai' ≤ g'`); the stop's image already
uses the ghost index (`c ≤ i + 1`, `i` the ghost index); at a restart `g₀ = |A| = i`, so the image's
bound is exactly what `start` needs: B2 provable with the image unchanged, no WAL link, no raft-loop
change, nothing trusted. Cost: `srvSnapOwn`'s index argument moves from Go's `ai` to `g` at its uses
(SnapRO, applyAll, ApplyAllSnap, InvRunRes's `applyRes`, `srvRestartAtR`, `srvBuiltRestartR`'s row at
`ai₀ + |γn.a0|`, start, run, RunOn, StopShutdown). **Waiting for 81's decision: (C) or (A) with the
two extensions above.**

## CP2 review fixes (2026-11-13, the CP2-fix agent)

81's decisions on the CP2 review (journal `wf_1e0c6340-ec5`); texts old → new in
`/shared/tmp/restart-s56/freeze-package.md` §11. **STOP for 81's re-review.**
- Finding 1 (BLOCKER), `start`'s side done: `srvBuiltRestartR` holds `srvSnapOwn s ci E γr γ (W64
  P.length)` (the counter at most `|P| + 1`); `isServerBuiltC` lost `Hsnapb`; `srvBuiltRestartR_first`
  takes `srvSnapBoot`; `srvSnapOwn_ro` (SnapRO); `start` adapted. **Open, decision needed**: B2 needs
  `c ≤ σ.b + 1` from the image, which gives `c ≤ i + 1`; recommended route (A) in §11.1 (`srvSnapOwn`
  carries `walBaseLb w (c - 1)`, the image gains `c ≤ σ.b + 1`, ~8 proof files).
- Finding 2 (MAJOR): `lease.srvInvAt on s E m σ₀` (LeaseApi, sealed), `lease.srvInv := srvInvAt … (∅,∅,∅)`;
  `specR`'s post at the recovered snapshot of the image's `lease` bucket.
- Minors: (a) contract docstring "The WAL's read facts" + `walReadFacts`' docstring; (b) interface note
  row I4 corrected (I4 unchanged); (c) `major.minor.0` (contract docstring, `clusterImageOk_restModel`'s
  docstring); (d)-(f) freeze §1, §8, §11.4; (g) `srvBuiltRC` (AuthCompRows) is the one text,
  `isServerBuiltC := srvBuiltRC ∗ "Hskeep" ∷ slot`, `srvBuiltR := srvBuiltRC .off` (the CP2 pitfall
  about the generator is obsolete).
- B2 additions: §11.4 (HS1's `Or.inr` or a widened `authStoreKit`; S8's `memberBuiltR` over `srvBuiltR`
  and `srvInvAt`; finding 1's image half first).
- Builds (at `48858f7fb4`): targeted and full clean (17479 jobs), tcb --check matches (870, 4),
  gen-interface --check clean: `/shared/tmp/restart-s56/cp2fix/{targeted,full,tcb}.log`.

## CP2 (2026-11-13, the CP2 agent): next agent starts here

- **CP2 texts in tracked files, commit `fbc609c3d1`** (on `0032b2e8f4`): `wal.restartOk` (sealed,
  defined) with `walReadFacts` (I1-I4), laws `wal.restartOk_facts`/`_start`, `walReadFacts_F3`,
  `durAgrees_prefix` (`E/WalApi.lean`); `bootOkR`'s `"Hwal" ∷ wal.restartOk cfg id cid bw.w' σ` and
  `%Hraft` over `rnRestartCfg`; the restart contract's antecedent `clusterVerLogOk L` (81's decision 1:
  derived, no world assumption) and its docstring "The cluster version"; `srvRestartRows`
  (`E/InvRestart.lean`); HS1 (`Spec/.../auth/NewAuthStore.lean`, axiom restated) with `authStoreKit_off`'s
  `Or.inl`; `boot_storageR` (`E/BootStore.lean`, P2); new `E/BuiltRestart.lean` (`restartKV`, `srvBuiltR`
  generated from `isServerBuiltC .off` less `Hskeep` by `/shared/tmp/restart-s56/cp2/gen_builtR.py`,
  `srvBuiltR_C`, P6's `restart_cs_bound`/`restart_idx`, `restart_clusterVerLogOk`); `NewServer.specR`
  (`SE/NewServer.lean`, not linked, not proved).
- Targeted build clean (`/shared/tmp/restart-s56/cp2/targeted.log`); full build clean (17479 jobs), tcb --check matches (870, 4):
  `/shared/tmp/restart-s56/cp2/full.log`; tcb: see the CP2 report.
- **Freeze package: `/shared/tmp/restart-s56/freeze-package.md`** (T1-T6, H10, world assumptions, exported
  statements). STOP: 81 runs the reviews (spec-reviewer on specR/srvBuiltR/srvRestartRows; axiom skill on
  HS1 and bootOkR's slot).
- After approval (B2): `NewServer.wp_proofB` over `SrvBoot`; NodeStart's `Hbc` from I3 (`wal.restartOk_facts`)
  instead of `σ.b ≤ |A₀| ≤ σ.commit` (interface §4; not done in CP2); P5's phase-2 RestConf invariant for
  the contract's clause (G); P3's rows (`/shared/tmp/restart-s56/p3-rows.md`), the lease-granting `srvRest`
  branch the largest unknown; apply `restart_clusterVerLogOk` at the contract call.
- (Obsolete since the CP2 fixes: `srvBuiltR` is `srvBuiltRC .off`, no generator.)

## Phase B progress (2026-11-13, the Phase B agent)

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
- **Probes checked**: `etc/lean-check.py -a Scratch/S56Probe.lean`: 0 errors, no `sorryAx` (P1's
  `restartOkD_start`, P2's `probe_P2_boot_storageR`, P6, P7). Pitfall: `$$ [H1 H2]` with persistent
  hypotheses opens a framing side goal; write `$$ [$H1 $H2]`.
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
