# Per-type stage B: handoff (2026-11-11)

Stage B fixes the grpc handler-pool soundness bug (`notes/STATUS.md`, "Soundness bugs: grpc.serve's
handler pool"). Coordinator: etcd-grove-81. Worktree `/shared/etcd-grove-stageB`, branch `stage-b`, cut
from `lean` `5fde200c15`. Scratch: `/shared/tmp/stageB/`.

## Done

- **Scope revision 5**: `/shared/tmp/stageB/scope-r5.md` (folds in review `wf_b189d821-c60` and
  etcd-grove-81's decisions; §1 is the changes table). r4: `scope-r4.md`.
- **B0** (in progress; no Lean statement on `lean`):
  - Go tests T1-T12, T5b, T8b, T9b: `examples/stageb/grpcruns/grpcruns_test.go`, all pass
    (`cd examples && systemd-run --scope -q -p MemoryMax=32G env GOWORK=off TMPDIR=/shared/tmp
    PATH=/usr/local/go/bin:$HOME/go/bin:$PATH go test -count=1 -v ./stageb/grpcruns/`).
  - Census script: `etc/stageb-census.py` (sections bounds, pools, lessor, handlers, start, consts;
    output in `/shared/tmp/stageB/census.txt`).
  - Spike: `Scratch/StageB/Spike.lean` (scratch, NOT in any lean_lib glob; must not land): the adapter
    with one `£ 1` (A4-MAJ-3), the carrier's identification (agree + joint Nodup), the fork over a
    model-only `#` name. Check: `env LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json
    etc/lean-check.py -a Scratch/StageB/Spike.lean`.

  - Spike (4) done: `spike_grpcFullName_inj`, `spike_names_nodup`, `spike_v3rpc_nodup` (etcd's lists in
    `v3rpc.Server`'s registration order, from `svcDescsOk`'s facts and the restated health post).
  - goose `trusted = ["Server.Serve"]` dry run: works (scratch `/shared/tmp/stageB/goose-dry/`; needs
    `GOWORK` unset; adds `ptr_Serve_unfold`; `Server` is axiomatized, the model cannot name its
    fields). `etc/verified-code.py` counts a trusted function proved over its model as "verified":
    B1a must make the `Serve` model's leaves count as assumed.
  - Statements touching B's names: `/shared/tmp/stageB/stmt/stmtlist.md` (script `stmtlist.py`).

  - Full build clean (retry after one exit 143 while queued; 2nd run exit 0); `etc/tcb-report.py
    --check` matches the baseline (865 axioms, 5 sorries). Reach: 74 of 5179 roots rest on
    `grpc.serve`/`grpc.serveStream`, 18 of them `*_safe`.

  - Gate, report-only: `etc/AxiomTokCheck.lean`, `etc/axiom-tok-check.py`, selftests in
    `etc/axiom-tok-selftest/` (21/21). Run over pf7's `tcb.json` copy (`da225483c9`), stale oleans,
    36 roots replaced by sub-modules: 811 Prop axioms, 706 pass, 90 need an entry, 15 capped.
    Token mint: only `goose_adequacy_start_files`. Rule-3/7 hits to triage: `grpc.serve(Stream)` (the
    bug), `grpc.NewClient`, `heap.Init_`/`Pop`, `http.CloseIdleConnections_ok`, `backend.Snapshot`,
    `lease.NewLessor`, `v3alarm.NewAlarmStore`, `adjustTicks`, `monitorStorageVersion`,
    `etcd_noRefusal`, `io.MultiReader`; rule 5 is mostly a cascade. Report:
    `/shared/tmp/stageB/gate/report.txt`. Memory: 8.68 GiB peak, 334 s. Rerun on the fresh
    `.lake/tcb.json` is a cheap follow-up (`--json .lake/tcb.json`).

- **B1a** (after CP0; additive, nothing landed): commits `bcc4e72331`, `97feddd906`.
  - Gate triage: no soundness finding; every rule-3/7 hit but the bug is an artefact, entries with
    reasons in `etc/axiom-tok-allow.txt`; `axiom-tok-check.py` recomputes rule 5 with the entries
    (`retaint`). Fresh run: `/shared/tmp/stageB/gate2/`; new texts: `/shared/tmp/stageB/gate4/`.
  - `Proof/google_golang_org/grpc/InvGrpcRun.lean` (vocabulary, 5 axiom constants, 2 agree axioms,
    run contracts, `grpcAccepted`, `grpcServeTokR`, unary adapter, `grpcFullName_inj`);
    `TrustedCode/google_golang_org/grpcServeModel.lean` (the model); four leaves
    `Spec|Proof/google_golang_org/grpc/model/{acceptRun,acceptRunConns,respond,finishStream}.lean`;
    `grpc.model.Serve.wp_proof` proved (`Proof/google_golang_org/grpc/model/Serve.lean`).
  - `etc/verified-code.py`: `ASSUMED_MODELS`, model-only names skipped.
  - CP1a Freeze package: `/shared/tmp/stageB/freeze-cp1a.md`; reviewed (`wf_85371608-bdd`: B1, B2
    blockers, M2 and minors), decisions by etcd-grove-81 in `questions.md`.
  - **Review fixes done** (freeze-cp1a.md §8, the commit after `ea85f7b661`): handlers typed `GoFunc`
    (`GrpcSrvCfg`, `grpcSrvStreamChain`, `grpcAccepted`, `isGrpc*At`, the model's run values), the
    `isPanic` conjunct dropped; docstrings (ErrServerStopped, flags/:1446, links, respond's range,
    address strings, si-nil comparison); gate entries finding-specific (`entry NAME KEY,... reason`,
    stale keys reported), `Dn` entries, selftests 26/26; verified-code's exact model-only names;
    Go test T10b.
  - **CP1a APPROVED** (etcd-grove-81, after re-verification). Then: `grpc.serveStream`'s same flag gap
    recorded in STATUS/decisions as a known overclaim until B1b; gate keys carry the counts
    (`3:E:produced2/consumed1`, `produced∞`, callback hand-off) and stale axioms are reported;
    selftests 30/30 + stale check. **Waiting for pf8c C3 before B1b.**

- **B1b, in progress** (after merging `lean` `47d7b2f2cd`, merge commit `179bbad313`; commits
  `7eb2d150b4`, `6706577eb1`). Done and checked with `etc/lean-check.py -a` (0 errors):
  - grpc package restated: the shared vocabulary moved from `InvGrpcRun.lean` to `InvGrpc.lean`
    (`GrpcSrvCfg`, the axiom constants, `grpcAddrIs`/`grpcSrvCfg` and their agree laws,
    `grpcRunOkMd`, `isGrpcRpcAt`, `grpcServerAt` as a definition) and `InvGrpcStream.lean`
    (`grpcStreamRunOk`, `isGrpcStreamAt`, `grpcStreamServerAt`); `isGrpcRpcMd`/`isGrpcStreamMd`
    over them; `isGrpcRpc := isGrpcRpcMd (GrpcSpec.md _)`; `grpc.serve`/`grpc.serveStream`
    theorems; `grpcServes*`, `grpcSlotPool`, `grpcStreamMethodOkR`, the `_intro`s and
    `grpc_serve(Stream)_rpcs` deleted; `grpcStreamMethodOk`/`grpcStreamHandlerOk` return `S`;
    `GrpcMethod.handler`/`GrpcStreamMethod.handler : GoFunc`.
  - `InvGrpcServer.lean`: `grpc.start` (joint `Nodup`, new post), `grpcSrvNew`/`descRegs`/
    `descSRegs` over `GoFunc` with the flag invariant, `grpcServeTok` axiom gone, header fixed;
    `grpcFullName_inj` and the new `grpcNames_nodup`, `descRegs_names` live here.
  - `InvGrpcRun.lean`: `grpcServeTok` (renamed), `grpc.start'`, the stream adapter
    `grpcStreamRunOk_of_pools` (with `srvStreamChainWP_fupd`/`_wand`).
  - `trusted = ["Server.Serve"]` (`etc/goose.py --project etcd`); the model moved to
    `TrustedCode/google_golang_org/grpc.lean` with `Server.Serve.impl := model.Serve`;
    `ManualProof/google_golang_org/grpc.lean`; `grpc.Server.Serve.wp_proof` a theorem over
    `grpc.model.Serve.spec` (takes `[google_golang_org.grpc.Assumptions]`).
  - `RegisterService` + the six `Register*Server`: the stream-flag premise; flag facts added to
    `etcdserverpbDescs` (KV, Lease, `pbDescOk`) and v3rpc's `svcDescsOk`/`descOk` (proved by the
    generated init; `etc/gen-init.py` updated, `--check` clean); `RegisterHealthServer`'s post;
    `bridge.New` over `grpcAddrIs`; `Invoke`/`NewStream` docstrings.
  - Axioms vs `lean` (repository files): +11 (B1a) −10 = **+1**, as frozen.

- **B1b, mechanical remainder** (2026-11-11, fresh agent; decisions 1-3 of etcd-grove-81 in
  `questions.md`): done and checked with `etc/lean-check.py -a` where the file's imports build:
  - `v3rpc/InvGrpcStart.lean`: `kvRegs` … `leaseSReg` over `GoFunc` (`functions X []`);
    `descRegs_eq`/`descSRegs_eq` over `GoFunc`; `func_intoVal_inj`, `handlers_eq` (handlers from the
    generated facts' values, `[go.CoreSemantics]`); `kvDescFuncs`/`authDescFuncs`/`leaseDescFuncs`
    with `*_eq : … = …Funcs.map … := rfl`; `server_nodup` (the spike's `spike_v3rpc_nodup`, ported,
    hypotheses as per-service `descNames` Nodup). 0 errors.
  - `v3rpc.Server` spec (retyped; post gains `((regs ++ sregs).map Prod.fst).Nodup`) and proof (the
    six flag discharges, health post's Nodup, `server_nodup`). 0 errors.
  - `NoRefusal.lean` (two axioms, binders retyped only: freeze §8.2), `InitializeMetrics` spec
    (retyped, §8.2), `etcdstart/Defs` (`grpcUp`/`grpcUpOn`/`grpcUpM` retyped and their pure part
    gains the joint Nodup as last conjunct; `grpcLeaseUp` retyped), `etcdstart/Serve.lean` (passes
    `Hregs.2.2.2.2.2`). Defs 0 errors; Serve.lean not checkable until B3 (imports boundary files).
  - `cluster3/Defs`: `forwards` is `(□ ∀ γ, grpcAddrIs b γ -∗ grpcAddrIs a γ) ∗ ⌜noRefusal…⌝`; the
    three `_forwards` lemmas re-proved; the 9 `icases Hfw with ⟨-, %Hf, -⟩` sites → `⟨-, %Hf⟩`;
    `StartBridge` post pattern. Not checkable until B3 (imports `client/v3/Results`, `ServedLease`).
  - `srvInterceptorOk`'s lend (r5 §2.5): handler continuation `R -∗ WP … {{ …, srvErrOk err ∗ R ∗
    (R -∗ Ψ v) }}`; `srvChainWP_of_ok` re-proved (the chain lends `[∗list] Rs`);
    `newLogUnaryInterceptor` (lends `srvLgReader`), `newUnaryInterceptor` (wp_join's `Q`,
    `handler_tail`'s `ispecialize Hk $$ [//]`). 0 errors.
  - Link lists: `grpc_Server__Serve: model_Serve`, `model_Serve: model_acceptRun …` and the four
    leaves in `etc/link-lean-first-{common,cluster3}.txt`; both `Link.lean` regenerated.

- **B2, started** (2026-11-11):
  - Lease pools at level 0 (r5 §2.6): `lease.lessorLvl`/`leaseLvl` (`abbrev … := 0`, so `levelTok 0`
    from `threadTok_level0` unifies); `lessorRdPool`, `isLeaseObj`'s two pools `isThreadPoolL`;
    `initL`/`borrowL`/`giveBackL`; specs `threadTok` → `levelTok lessorLvl/leaseLvl` (pre and post):
    `Lease.Remaining`, `leasesByExpiry.Less`, `lessor.Leases`, `Lease.Keys`' `.reader` (`keysPre`),
    the trusted `lessor.Renew` and `EtcdServer.leaseTimeToLive` (axioms; Freeze §2.2),
    `checkLease{Renew,TimeToLive,Leases}`, `EtcdServer.Lease{TimeToLive,Leases,Renew}`. Callers with
    a whole `threadTok` split it (`ServerLeaseRead`, mvccfull `runner__checkLeases`); handler `S`
    in `InvLeaseRead`/`InvLeaseKeepAlive` still says `threadTok` (B3: `E.RD ∗ levelTok 0`). D3
    census: no nesting; the apply thread uses `Keys .owner` only (sub-agent report). Note for the
    Freeze review: the two axioms now claim level 0 suffices (Renew's checkpointer path and a
    follower's `leaseTimeToLive` HTTP path are not run by closed results).
  - Inner pool `I` at level 2 (`RevokeCtx.lean`: pools, borrow/give-back laws, header table;
    `revokeExpiredLeases`' inner goroutine splits levels 1 and 2; `NewServer`'s `initL … 2`).
  - `srvLevelK := srvRevokeK` (`RevokeLevels.lean`); `srvLevels : Prop := srvLevelK ≤ threadBound GF`,
    `srvLevels_iff` (`Iff.rfl` with `srvRevokeLevels`, kept a def, not an abbreviation: `word`
    proofs unfold it), `srvLevels_of_max` (`RevokeCtx.lean`).
  - Built with `lake build` (0 errors): the lease package, the server's lease specs, `NewServer`,
    `revokeExpiredLeases`, v3rpc `ServerLeaseRead`/`InvLeaseKeepAlive`, mvccfull/mvccrand Links.

## Next, in order

1. **B2, rest** (CP2), per r5 §4.2/§3.2: `srvServeStock` in `InvServe.lean` (raw stock `P =
   srvRevokePoolN` of `mvccReaders E.γ 1 ∗ srvBemuReader s`, the counted Start stock) in
   `NewServer`'s post beside `srvServeBuilt` (keep counts symbolic: the 80 GB compile; pair lists at
   their elements' own forms, as at `NewServer.lean:2010`); `srvKeepRdN := mvccReaderN - P - 130`
   (`InvRestart.lean:325`), `srvKeepRdN_total` (`StopShutdown.lean:392`), `StopReaders.lean`;
   `EtcdServer__start.lean`'s `readMu` raw stock `P` beside `B` (`:572-588`); a narrow run-borrow
   law for `I` at level 2 (as `srvRevokeCtx_innerBorrow`, from what `memberUp` holds); `memberUp`
   (`etcdstart/Defs.lean:307-423`) builds the run pool (`initL` level 3, of `mvccReaders 1 ∗
   srvReadReader ∗ srvBemuReader`) and gives its handle; adequacy lemmas with `srvLevelK`
   (`etcdstart/Adequacy.lean:161,215`, `AdequacyMembers.lean:63,93`); k8s
   `k8s/etcd3/Adequacy.lean:160,217` (`max (n + 2) srvLevelK`, `realThreadsBelow_mono`).
2. **B3**: the callers in `/shared/tmp/stageB/b1b/boundary.txt` (+ `ServeFromStart`, `cluster3/Defs`
   become checkable), `Watch` made exact, the 64-stocks removed, `srvLevels` where used; the chain
   consumers of `srvChainWP_of_ok` (`client/v3/Results`' `etcdIcRs` …) pass the lent `Rs` to the
   handler.
3. CP3: full build, tcb `--check --update` (net +1), collections, interfaces, gen-init, gate
   enforcing (capped walks fixed), `tcb-report --roots`; delete `Scratch/`. STOP before land.sh.

## Pitfalls

- Every lake command: `--packages=/shared/tmp/manifest-ddc.json`; full builds under
  `flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G`
  (`/shared/tmp/stageB/fullbuild.sh`).
- `Scratch/` is a lean-check-only directory; delete it before any landing.
- GooseLang steps `App f (Val v)` and a `let:` of `v` only if `v.isPanic = false`: a raw `val`
  (a handler `mh`) needs the fact (`grpcAccepted`'s stream arm has it); `#x` has it by
  `isPanic_intoVal`. `#mh` with `mh : val` is NOT `mh` (`intoVal` is abstract).
- `--goal L` of `etc/lean-check.py` shows the state before line L's tactic.
- Gate entries are finding-specific (keys with counts): after changing an entry's axiom, rerun and
  update its keys (`finding_key`); a stale key, or an entry for an axiom not in `--json`, is reported
  (a run over a subset of names, like gate5's, shows the others as stale). New texts' run: `/shared/tmp/stageB/gate5/` (command:
  `lake env lean --run etc/AxiomTokCheck.lean --axioms=names.txt <modules>`, then
  `etc/axiom-tok-check.py --json names.json --reuse-raw raw.jsonl`).
- `Scratch/StageB/Spike.lean` predates the `GoFunc` typing (not rechecked; scratch).
- The examples pin etcd at `a4d2bb1720b9` (not `673da07c8f` as the brief said).
