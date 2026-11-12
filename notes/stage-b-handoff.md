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

- **B2, rest done (CP2)** (sub-agent, built with targeted `lake build`, 0 errors: `RevokeCtx`,
  `InvServe`, `InvRestart`, `StopReaders`, `StopShutdown`, `NewServer` (proof and Spec), etcdstart
  `Defs`, `Start`, `newServerMode`, `NewMember`, `Adequacy`, `AdequacyMembers`):
  - `InvServe.lean`: `srvServeStock s E := srvRevokeBuilt s E ∗ replicate srvRevokePoolN
    (mvccReaders E.γ 1 ∗ srvBemuReader s) ∗ srvLgReader s ∗ srvLgReader s` (the handle a started
    member lacked, the raw stock, Start's counted 2); `srvRunReadStock s γr` (`srvRevokePoolN`
    `srvReadReader`s); `srvRunN`, `srvRunPool s E γr` (level 3, persistent, not sealed);
    `srvRunPool_init : srvServeStock ∗ srvRunReadStock ⊢ |={Em}=> srvRunPool ∗ srvRevokeBuilt ∗ 2
    lgMu readers` — **the run pool is built at the serve step (B3), not in `memberUp`** (r5 §0
    item 5 / D6: a non-cancelable pool would break `memberUp_stop`'s exact census);
    `srvServeStock_built`, `replicate_pair`.
  - `RevokeCtx.lean`: `srvRevokeBuilt_innerBorrow` (`£ 1 ∗ srvRevokeBuilt ∗ levelTok 2`),
    `srvRevokeBuilt_bound`; `raftPool` via `srvRevokeBuilt_raftPool`.
  - `NewServer.specG` post gains `srvServeStock srv E`; `srvKeepRdN := backend.rdStockN - 7 -
    srvRevokePoolN - 64 - 64 - 1 - 1` (= `mvccReaderN - srvRevokePoolN - 130`; written over
    `rdStockN`: over the sealed `mvccReaderN` the kernel recursed too deep); `srvStopReaders`,
    `srvKeepRdN_total`, `srvStopReaders_intro` follow; `mvccReaders_ofRep`.
  - etcdstart: `memberBuilt` gains `srvServeStock`; `memberUp`/`memberUpOn` gain `srvServeStock s E ∗
    srvRunReadStock s ρ.rd` (carved in `Start.lean` from `srvStartReadN`: `memberReadN :=
    srvStartReadN - srvRevokePoolN`, `srvStartReadN_split`, `srvStartReaders_split`; the server's
    `start` untouched); `memberUp_served`/`memberUpOn_served` drop the new stocks (B3 surfaces them,
    ~18 example callers); adequacy lemmas at `max (n + 2) srvLevelK`; `k8s_etcd3_adequate` proof only.
  - Unchecked (import boundary files): `restart/startMember`, `restart/Defs`, `etcdstart/Served`,
    `auth/startServer`, `k8s/etcd3/Adequacy`.
  - `etc/bounds-check.py --check`: 377 vs baseline 374 (`srvRunReadStock`, `srvStartReaders_split`):
    allow entries or baseline at CP3.

- **B3, in progress** (2026-11-11, fresh agent; `lean` `e891d049fc` merged; CP2 decisions in
  `questions.md`). Design (forms, recorded in `questions.md`):
  - **The lend reaches the handler**: `wp_unaryHandler*` (`UnaryHandlerLemmas.lean`) and the 15
    `Spec/.../etcdserverpb/_*_Handler.lean` take the handler contract at `iprop(S ∗ [∗list] R ∈ Rs, R)`
    (pre/post still `S ∗ [∗list] Rs`); `_Watch_Watch_Handler`'s post gains `S`. Done, checked.
  - **The bundle**: `srvRunBundle s E γr := levelTok 0 ∗ srvLgReader s ∗ (srvLeadTimeReader s ∗ E.RD)
    ∗ (mvccReaders E.γ 1 ∗ srvReadReader s γr ∗ srvBemuReader s)` (new
    `Proof/go_etcd_io/etcd/server/v3/etcdserver/RunAdapt.lean`): the run's own level 0 (the lease
    handlers' lessor/lease pools), `raftPool` (level 1), `I` (level 2), the run pool (level 3). The
    generic adapters `grpcRunOkMd_of_pools`/`grpcStreamRunOk_of_pools` (`InvGrpcRun.lean`) now hand
    the handler `levelTok 0 ∗ R₁ ∗ R₂ ∗ R₃`. `srvRunOk_of_pools`/`srvStreamRunOk_of_pools` (RunAdapt):
    `srvLevels → □ grpcMethodOkMd … (srvRunBundle s E γr) Spec ∗ srvRevokeBuilt s E ∗ srvRunPool s E γr
    ⊢ grpcRunOkMd …`; `srvRevokeBuilt_runPools` (RevokeCtx) gives the two pools.
  - **lgMu**: the bundle has ONE `srvLgReader` (r5 §3.2): it is `etcdIcRs`'s, lent by the log
    interceptor to the handler. So the KV handler's own resource is the bundle minus it, and the
    quota servers' inner contract must take the lent reader: planned restatement of
    `quotaKVServer.Put/Txn` and `quotaLeaseServer.LeaseGrant` specs: pre/post keep `S ∗ quotaRd s`,
    the inner handler contract becomes `grpcHandlerOkMd … iprop(S ∗ srvLgReader s) Spec` (the check
    and the inner call use the reader in turn). (Alternative r5 wording: `quotaRd` shrinks to
    `srvBemuReader`; same accounting.)
  - **Serving**: `memberUp_served`/`memberUpOn_served` surface `srvServeStock s E ∗ srvRunReadStock s
    ρ.rd` in place of `srvWatchReaders s E 64 ∗ kvServeStocks`; a serve site runs `srvRunPool_init`
    (its 2 `lgMu` readers are dropped) and passes `srvRevokeBuilt`/`srvRunPool` + `srvLevels` to the
    served theorems, which take run contracts (via `srvRunOk_of_pools`) in place of `N`, `S`, `F`,
    `h1`, `h2` and `replicate N S`.

  - **State at this handoff** (commits `20ac8c68dd` and the next): checked with `etc/lean-check.py
    -a`: `UnaryHandlerLemmas`, `_Watch_Watch_Handler`. Written, NOT yet checked (a full build held
    the lock): `RevokeCtx.srvRevokeBuilt_runPools`, `RunAdapt.lean`, the level-0 change of the two
    generic adapters in `InvGrpcRun.lean`, the three quota servers' specs/proofs
    (`quotaKVServer__Put/Txn`, `quotaLeaseServer__LeaseGrant`: inner contract at `S ∗ srvLgReader s`).
    Probe build `b3-probe1` (log `/shared/tmp/stageB/logs/b3-probe1.log`) was run before these edits;
    its only failures then were `_Watch_Watch_Handler` and `UnaryHandlerLemmas` (both fixed), so
    nothing downstream of them was tried: run a new full build to get the real error list.
    It finished (lock released); its failures also included `client/v3/InvLeaseGrant`,
    `v3rpc/QuotaLeaseLemmas` and `Spec/.../etcdstart/Serve` (still with the pre-B3 texts).
  - **B3, second agent** (2026-11-11; the probe's PIDs and its orphaned `lake` were killed, a fresh
    full build `b3-full2` run: failures `InvLeaseGrant`, `RunAdapt`, `etcdstart/Serve` (spec), and
    `v3rpc/Results`). Done, `etc/lean-check.py -a` 0 errors: `RunAdapt` (`unfold srvRunBundle`; now
    also holds `grpcMethodOkMd_slot` (moved from client `Results`), `grpcHandlerOkMd_slot`,
    `grpcHandlerOwnOk_slot`, `grpcHandlerOk_slot`, `bigSepL_cons_intro'`), `InvLeaseGrant`
    (`isGrpcRpc_mono_with` re-proved over `isGrpcRpcMd`), `QuotaLemmas`/`QuotaLeaseLemmas` (inner
    contract at `S ∗ srvLgReader s`). Written, being checked:
    - `v3rpc/Results`: the five auth `*MethodOk` take the handler at `iprop(S ∗ [∗list] Rs)`;
      `grpcHandlerOwnOkMd_frame` (new); `etcdAuthMethods` over `functions … []`; `etcd_auth_served`
      restated (drops `N`/`replicate`; takes `γr γ F h1 h2` with `h1 : srvRunBundle ⊢ (authSlot ∗
      [∗list] Rs) ∗ F`, `h2` back, `srvLevels`, `grpcServerAt … γ ∗ srvRevokeBuilt ∗ srvRunPool`;
      `grpc.serve`, each method via `grpcMethodOkMd_slot` + `srvRunOk_of_pools`). Pitfall: give
      `srvRunOk_of_pools` the handler and service explicitly (with `_` and `$$ [H]; iframe #` the
      frame picks any persistent hypothesis); build a method list with `bigSepL_cons_intro'` +
      `iexact` (neither `iframe #` nor `simp`/`dsimp` reduce the records' projections there).
      The Watch part (`etcd_watch_served*`, from line ~1720) is step (3), untouched.
    - client `Results`: `etcdKVSlot` (= `etcdRunSlot` minus `lgMu`), `etcdGrpcSlot := (etcdKVSlot ∗
      srvBemuReader) ∗ [∗list] etcdIcRs`, `etcdLeaseSlot S := (S ∗ srvBemuReader) ∗ [∗list] etcdIcRs`,
      `etcdRunSlot_split`, `quotaRd_lent`, `etcdGrpcSlot_bundle : srvRunBundle ⊣⊢ etcdGrpcSlot ∗
      levelTok 0`, `etcd_quotaHandler(Own|Plain)_lent`, `etcd_runOk_of_slot`, `etcd_runOks_of_slot`;
      the KV/lease method lemmas take the handler at `iprop(S ∗ [∗list] Rs)`; method lists over
      `functions … []`; restated (exported, CP3 freeze list): `etcd_kv_servedM_with`,
      `etcd_kv_served_with`, `etcd_kv_served` (drop `N S F h1 h2 hnd`, `replicate`; take `γ`,
      `srvRevokeBuilt ∗ srvRunPool`, `srvLevels`, others `ms` as `□ [∗list] grpcRunOkMd`),
      `etcd_kv_started(_with)` (`grpc.start'`; take `hnd : ((regs ++ sregs).map Prod.fst).Nodup`,
      the pools, `srvLevels`; post `∃ γ, grpcServeTok gs lis γ ∗ grpcStreamServerAt … γ ∗ …`),
      `etcd_lease_served`, `etcd_kv_lease_served` (`raftLessor` at `etcdKVSlot`),
      `client_lessor_isEtcdLease_served`, `client_new_isEtcdLeaseClient_served` (take `F h1 h2` over
      `etcdLeaseSlot`, `γ`, pools, `srvLevels`).
    State at commit (after `1af900e9de`): `v3rpc/Results` checked up to the Watch section: the auth
    part has 0 errors; the 8 errors left are all in `etcd_watchMethodOk`/`etcd_watch_served*`
    (from line ~1749: step (3), Watch exact; the stream contract returns `S` and the stream lend).
    client `Results` is written but NOT checked (it imports `v3rpc/Results`, which does not build
    until Watch is fixed; to check it earlier, temporarily `sorry` the watch theorems in a scratch
    copy, never committed). Lean pitfall found: a method list's element at `pbXRequestT` does not
    unify with a hypothesis at `pbXRequest` under `iexact`/`iframe` (`ProtoMsgT` defs are not
    unfolded at the IPM's transparency); `change Iris.ProofMode.Entails' _ (grpcRunOkMd (Req :=
    pbXRequest) (Rep := pbXResponse) _ _ _ _)` first (as the old Txn case did).
    Next: Watch (3), then check client `Results`; then the callers (`AuthnServedOn`, `LeaseReadServed`,
    `LeaseGrantServed`, `ServeFromStart`, `cache/v3/Results`, etcdstart `ServedLease`/`Served`,
    `watch/Served`, `auth/MainServe` (calls `grpc.start` directly), cluster3), then (3)-(8) below.
  - **B3, third agent** (2026-11-11; the second agent's forms accepted by etcd-grove-81, recorded in
    `questions.md`). Done, `etc/lean-check.py -a` 0 errors (commits `caddf7c80e`, `42fbb4c75c`):
    - **Watch exact** (step 3; form decided by the agent, see `questions.md`): `serverWatchStream.recvLoop`
      loses its (unused) `threadTok` and gives back `r.srv.E.RD`; `serverWatchStream.close`'s post is
      `▷ P` (the wait's deposit); `watchServer.Watch` takes `∀ N₂ N₃ γ₂ γ₃ F₂ F₃`, pre
      `⌜threadBound ≤ actualMaxReaders ∧ 4 ≤ threadBound⌝ ∗ isThreadPoolL N₂ 2 γ₂ (F₂ ∗ R.E.RD) ∗
      isThreadPoolL N₃ 3 γ₃ (mvccReaders W.γm 1 ∗ F₃) ∗ mvccReaders W.γm 1` (was `R.E.RD ∗ ⌜tb⌝ ∗
      mvccReaders 2`), post `+ mvccReaders W.γm 1`. The proof: the send loop's reader goes back through
      the wait group (`wp_Add (mvccReaders W.γm 1)`, `close` returns it); the receive loop's goroutine
      (`wp_fork_tok_upd`, its `£ 1`) splits its token into levels, borrows `I` (2) and the run pool (3),
      runs `recvLoop`, gives both back and reassembles its token.
    - `v3rpc/Results` watch section: `watch_streamHandlerOk` at the slot `mvccReaders W.γm 1` with the
      two pool handles; `etcd_watchMethodOk` at any slot `S` with `h1 : S ⊢ (mvccReaders W.γm 1 ∗
      [∗list] Rs) ∗ F`/`h2`; **restated (exported, CP3 freeze list)**: `etcd_watch_served` (drops `n`,
      `replicate`; takes `γ γr F h1 h2` over `srvRunBundle R.s R.E γr`, `hγ : W.γm = R.E.γ`, `Htb`,
      `srvLevels`, `grpcStreamServerAt … γ ∗ srvRevokeBuilt R.s R.E ∗ srvRunPool R.s R.E γr`; sregs over
      `GoFunc`, `hreg` at `functions _Watch_Watch_Handler []`), `etcd_watch_served_chain` (same, with
      `srvRunBundle_watchSlot` for the `[True, True]` chain), `etcd_watch_served_etcd_chain` (post wand
      over the pools). `watchRunSlot` (InvWatch.lean:498) is now unused by v3rpc: delete it when the
      callers (`ServeFromStart.watchRunSlots_of`, the examples) are moved.
    - client `Results` checked: `quotaRd_lent`/`etcdGrpcSlot_bundle` (a `[∗list]` over a literal list is
      `.rfl` to its `∗`-chain: `simp` does not unfold it), the Compact method via
      `grpcHandlerOwnOk_slot` from `etcdRunSlot` to `(etcdKVSlot ∗ bemu) ∗ [∗list] etcdIcRs`, the slot
      lemmas with explicit slots, new `srvRunOks_of_slot` (generic list form, used by
      `etcd_lease_served`).
    - Pitfalls found: `grpcHandlerOkMd_slot _ _ S' F _ h1 h2` fails when `S` is `_` (h1 elaborates
      first): give `S`; an `ihave … $$ [H]` of a premise whose hypotheses are persistent still needs its
      `· iframe #` bullet; `change … (grpcRunOkMd (Req := …) _ _ _ _)` with holes keeps the record
      projections: write the arguments in full, or avoid splitting lists (`srvRunOks_of_slot`).
    Next: the callers (step 3 of the brief): `AuthnServedOn`, `LeaseReadServed`, `LeaseGrantServed`,
    `ServeFromStart` (`watchRunSlots_of`, `etcdGrpcSlots_of_started` go), `cache/v3/Results`, etcdstart
    `ServedLease`/`Served`/`WatchSrv`, `watch/Served`+`Main`, `auth/MainServe`+`Main` (calls `grpc.start`
    directly), cache/compactwatch/k8s-compactor `Main`, `cluster3/StartMember`; then (4)-(8) below.
  - **B3, fourth agent** (2026-11-11; the third agent's forms accepted by etcd-grove-81, in `questions.md`).
    Done (commit `0ed49b0fac`, `lean-check -a`/targeted build 0 errors): `ServeFromStart` (deleted
    `etcdGrpcSlots_of_started`, `watchRunSlots_of`, `grpcCfgOk_of_started_w`; `grpcCfgOk_of_startedM`
    takes `srvWatchBuilt`, no `K`); etcdstart `Defs` (`grpcUp`/`grpcUpOn`/`grpcUpM` lose
    `mvccReaders E.γ 64`), `Served` (`kvServeStocks s E γr := srvServeStock s E ∗ srvRunReadStock s γr`, a
    def; `kvServeStocks_pools`; `kv_served` takes `srvLevels`, post `(∃ γ, grpcServeTok gs lis γ) ∗ …`;
    `memberUp(On)_served` surface `srvWatchBuilt ∗ kvServeStocks`), `Serve` spec/proof (`srvWatchBuilt`
    for `srvWatchReaders 64`; the ghost step returns `∃ γ, grpcServeTok gs lis γ`), `watch/Served`
    (`wk_served_nd` over the pools, `hs`, `hγm`, `hnd`, `Htb`, `HL`); putget `Main` (+ spec premise
    `srvLevels`, Adequacy `srvLevels_of_max HT`), the model for the other Mains.
    Then (commits `76a5b297a4` … `56004b1936`, each module checked by targeted `lake build`, 0 errors):
    step (5) (`srvServeBuilt s E cfg := srvServeFacts ∗ srvBemuReader ∗ 2 srvLgReader`; `srvServeStock`
    without `lgMu`; `srvRunPool_init` post `srvRunPool ∗ srvRevokeBuilt`; NewServer hands out neither
    stock nor `srvWatchReaders` (deleted); `srvKeepRdN := rdStockN - 7 - srvRevokePoolN - 1 - 1`;
    `srvStopReaders E := mvccReaders E.γ srvRevokePoolN`; memberUp/memberUpOn/memberBuilt without the
    64-stocks); client `LeaseReadServed`/`LeaseGrantServed`/`AuthnServedOn`, `cache/v3/Results`
    (`etcd_cache_served` over the pools, + `hnd hs hγ Htb HL`); the lease contracts discharged at
    `E.RD ∗ levelTok 0` (`raftLeaseRead(_of)_server`, `raftLeaseRenew(_of)_server`); `ServedLease`;
    `watchRunSlot` deleted; every Main/start spec that serves takes `srvLevels` (adequacies
    `srvLevels_of_max HT`; leaseexpiry via `srvLevels_iff`), auth `ak_served_kv`/`ak_served_watch`,
    cluster3 `StartMember` (no `hRS`; `etc/link-lean-first-cluster3.txt` and its Link regenerated).
    (7): STATUS soundness section records the Renew/leaseTimeToLive level-0 known overclaim (reach at
    CP3). `lean` `a259c0efd1` merged (`7e5a97c6b2`, no conflict).
    **CP3** (2026-11-11): full build `b3-full4` exit 0 (first try); `tcb-report --check --update`: trust
    base 870 = 870 (−10 grpc.serve/serveStream/Server.Serve/grpcServes*/grpcServeTok/grpcServerAt/
    grpcStreamServerAt, +10 the model's 4 leaves, grpcAddrIsRaw, grpcConnsLink, grpcReplyTo,
    grpcSrvCfgRaw, grpcSrvCfg_agree, grpcSrvLink); repository axioms +1 (`grpcAddrIs_agree`, reached by no
    result); 24 collections updated (grpc lines only); interfaces regenerated (etcdstart only),
    `api-check` clean; `gen-init --check` clean; `goose --check` clean; bounds 331 (baseline lowered from
    374; allow entry for `watchServer__Watch`'s levels); `--roots '_safe$'`: no `*_safe` rests on
    `grpc.serve`/`serveStream` (`/shared/tmp/stageB/logs/cp3-safe-roots.txt`); `Scratch/` removed.
    The gate (`046eb5681b`): `axiom-tok-check.py --check` enforcing, step in `etc/gates.sh` (24G cap);
    0 capped (closing atoms, monotone pruning); checker gaps fixed; 72 s, 8.6 GiB. `--check` FAILS today:
    5 server axioms the cap used to hide (`EtcdServer.{ensureLeadership,leaseTimeToLive,purgeFile,
    waitAppliedIndex,waitLeader}`, ~23 keys each, all inside the consumed `isServerReqM`/`isServerReadM`)
    + 48 rule-5 cascade. Proposed entries (unverified per key):
    `/shared/tmp/stageB/gate10/proposed-server-entries.txt`; run output `/shared/tmp/stageB/gate10/`.
    Next: triage those keys (decision asked of etcd-grove-81), rerun the gate, then land via etc/land.sh
    when etcd-grove-81 says go.
  - **B3, fifth agent** (2026-11-12): the level-0 overclaim of `lessor.Renew`/`leaseTimeToLive` closed
    by option (b), T1-T5 of `/shared/tmp/stageB/lease-level-fix.md` (approved by etcd-grove-81, in
    `questions.md`): `NewDefaultServerFeatureGate` post `+ featureIs … "LeaseCheckpoint" false`;
    `NewServer.spec` pre `#Hlcp` (callers `newServerMode`, `auth/startServer`: `#Hflc` from the gate);
    `FeatureEnabled.spec` takes `ob : Option Bool` (callers pass `none`); `lessorExtra`'s `cp` fixed at
    `func.nil` (lessor proofs Grant/Recover/Revoke/Leases/Checkpoint adjusted); `lessorCkptOk` deleted
    (`InvBoot`, `NewLessor` post; mvccfull `runner__open`, mvccrand `runChecks` patterns); `Renew` and
    `leaseTimeToLive` docstrings; STATUS entry closed (moved to status-history), decisions.md "Stage B:
    the lessor's checkpointer is nil" (with the planned `ckptEffectsOk` removal, not in stage B).
    Targeted build: modules in `/shared/tmp/stageB/lease-fix-targets.txt`, log
    `/shared/tmp/stageB/logs/lease-fix-build*.log` (build2: 0 errors). Gate: the five server entries
    added to `etc/axiom-tok-allow.txt` with etcd-grove-81's reason (independent triage: artefacts),
    `NewAuthStore`/`NewAlarmStore` `3:Pre` reasons rewritten (hook vs no-lock exclusivity); follow-ups
    (purgeFile/adjustTicks `Logger()`, binder-path gate keys, `ckptEffectsOk`) in STATUS/decisions.
    **Next (steps 4-5 of etcd-grove-81's 2026-11-12 message)**: merge `lean` (`49fff2f95c` or later);
    full build under the lock and the 64G cap; `tcb-report --check` (net 0 vs CP3 expected; report);
    collections; interfaces (`etc/gen-interface.py` per affected `etc/api/*.txt`: features, lease,
    etcdserver); the gate `axiom-tok-check.py --check` must pass; then, if no trusted change goes
    beyond CP1a/§8, the B2 lease specs and T1-T5, `etc/land.sh` with
    `LAKE_PACKAGES=/shared/tmp/manifest-ddc.json PERENNIAL_CHECKOUT=/shared/perennial-ddc0f0acc`,
    logging to `/shared/tmp/stageB/land.log` (go given by etcd-grove-81 under those conditions).
  - **B3, landing** (2026-11-12): `lean` `49fff2f95c` merged (`a23c25f600`; STATUS's line kept both
    new entries, `premise fixes 8, S1` moved to status-history); full build exit 0 (the first run hit the
    64G cap, the retry passed; `/shared/tmp/stageB/logs/fullbuild-cp4b.log`); tcb `--check` 865 axioms,
    5 sorries (net 0 vs lean: 10 grpc axioms out, 10 in); collections, interfaces (no regeneration diff),
    gen-init, goose, axiom-tok `--check`, bounds (331) pass; `--roots '_safe$'`: no `*_safe` rests on
    `grpc.serve`/`serveStream`/`Server.Serve` (gone), only `sorry out_size`. Then `etc/land.sh`
    (log `/shared/tmp/stageB/land.log`).
    **land.sh refused (gates FAILED, lean unchanged)**: two gates CP3 had not run fail on the new grpc
    trusted texts: `etc/model-param-check.py` rule 1 (9 hits: `grpc.model.acceptRun.wp_proof`,
    `acceptRunConns.wp_proof` bind `grpcAccepted`'s `Req`/`Rep` `.toProtoMsg.M`/`.toStreamMsg.M`, and
    `respond.wp_proof` binds `spec`'s `Rep.toProtoMsg.M`, with no registry premise) and
    `etc/errdesc-check.py` (`Spec/google_golang_org/grpc/model/respond.lean` names `errDesc`, not in
    `REVIEWED`). Every other gate passed. Waiting for etcd-grove-81's decision (trusted text).
  - **B3 next, in order**: (1) check the unchecked files above; fix `QuotaLemmas.lean`/
    `QuotaLeaseLemmas.lean` (`quotaKV_*HandlerOkMd_of`, the inner contract now at `S ∗ srvLgReader s`)
    and the generated handler proofs (`Proof/.../etcdserverpb/_*_Handler.lean`, should follow);
    (2) client/v3: `etcdGrpcSlot` restated so that it is `srvRunBundle` up to rearrangement (the
    handler's part `S_q := levelTok 0 ∗ (srvLeadTimeReader ∗ E.RD) ∗ (mvccReaders 1 ∗ srvReadReader ∗
    srvBemuReader)`, the quota servers' `S := etcdRunSlot` minus its `lgMu` reader, plus the lent
    `etcdIcRs`); `etcd_kv_servedM_with`/`_served_with`/`_served`/`etcd_kv_started(_with)` take
    `srvRevokeBuilt s E ∗ srvRunPool s E γr`, `srvLevels`, and the other methods `ms` as
    `□ [∗list] grpcRunOkMd …` (drop `N S F h1 h2`, `replicate N S`; exported: CP3 freeze list), then
    `grpc.serve`; `ServeFromStart` (`etcdGrpcSlots_of_started` goes), `LeaseReadServed`,
    `LeaseGrantServed`, `AuthnServedOn`, `v3rpc/Results` (auth served; lease handlers' `S` as
    `E.RD ∗ levelTok 0` in `InvLeaseRead`/`InvLeaseKeepAlive`), `cache/v3/Results`;
    (3) Watch exact (r5 §4.3 "Watch": `watchServer.Watch` pre `threadTok ∗` the pool handles, post
    `+ threadTok`; recvLoop borrows `I` and the run pool and returns `E.RD`; sendLoop: interval borrow,
    then run-pool loan); `etcd_watch_served(_chain)` with `srvStreamRunOk_of_pools`;
    (4) etcdstart: `memberUp_served`/`memberUpOn_served` surface `srvServeStock ∗ srvRunReadStock`
    in place of `srvWatchReaders 64 ∗ kvServeStocks`; `kv_served`, `ServedLease` run
    `srvRunPool_init`; `Serve.lean` spec, `restart/serveClient`; the ~18 example callers, `srvLevels`
    on the serving Main/Start specs; (5) remove the 64-stocks (`srvServeBuilt`'s, `srvWatchReaders`,
    `InvWatchBuilt`, `NewServer`'s hand-out, `srvKeepRdN` to `mvccReaderN - srvRevokePoolN - 2`,
    `StopShutdown`, `StopReaders`, etcdstart `Defs`/`Start` (Start spends `srvServeStock`'s two
    `lgMu` readers), auth `startServer`); `holdToken` comments (r5 §4.3); (6) the unchecked files
    (cluster3/Defs, StartBridge, etcdstart Serve/Served, restart/startMember and Defs,
    auth/startServer, k8s/etcd3/Adequacy); (7) the Renew/leaseTimeToLive scope (CP2 decision 2);
    (8) CP3 (brief: full build, tcb `--check --update` net +1, collections, interfaces, gen-init,
    goose, gate enforcing with capped walks fixed, bounds allow entries, `tcb-report --roots` on the
    18 `*_safe`; delete `Scratch/`; STOP before land.sh).

## Next, in order

1. (done, see above) **B2, rest**, per r5 §4.2/§3.2: `srvServeStock` in `InvServe.lean` (raw stock `P =
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
- The etcd pin is `etc/goose.py`'s `71f99a4bf` (checked 2026-11-12, on `lean` too; the examples' `go.mod`
  replaces etcd by it). Earlier briefs' `673da07c8f` and this file's former `a4d2bb1720b9` are stale.
