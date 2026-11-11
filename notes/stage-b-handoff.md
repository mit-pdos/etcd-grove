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

## Next, in order

1. **The boundary (STOP reported to etcd-grove-81):** B1b cannot build past the grpc package
   without B2/B3. Pool-dependent: every serve site turns `grpcServerAt … ∗ replicate N S` and
   `grpcMethodOkMd … S` into registrations, and now needs `□ grpcRunOkMd` per method, i.e. pool
   handles (`isThreadPoolL` at levels 1-3) from B2 and B3's adapter instances:
   `client/v3/Results.lean` (`etcd_kv_servedM_with`, lease served), `client/v3/AuthnServedOn.lean`,
   `v3rpc/Results.lean` (auth served, `etcd_watch_served`), `etcdstart/{Served,ServedLease}.lean`,
   `examples/etcd/auth/MainServe.lean`, `examples/etcd/watch/Served.lean`, `cache/v3/Results.lean`.
   Stream `S` return: `_Watch_Watch_Handler` (spec and proof; `watchServer.Watch` keeps its slot:
   B3's Watch restatement). Per-file list: `/shared/tmp/stageB/b1b/boundary.txt`.
2. Mechanical B1b work left, not pool-dependent: `v3rpc/InvGrpcStart.lean` (`kvRegs` …
   `leaseSReg` over `GoFunc`; membership lemmas through `intoVal_inj_func`,
   `PostLifting.lean:725`); `v3rpc.Server` spec/proof (retype; flag discharge: KV `HkvD.2.2`, Watch
   from `HwD.2`, Lease `HlD.2.2`, Cluster `HcD.2`, Auth from `asds` names `= []`, Maintenance
   `HmD.2`; the joint `Nodup` post from `grpcNames_nodup`, ported from the spike's
   `spike_v3rpc_nodup`); `NoRefusal.lean`, `ServerMetrics__InitializeMetrics` spec, `etcdstart/Defs`,
   `cluster3/Defs` (bridge relation → `grpcAddrIs`); `srvInterceptorOk`'s lend (r5 §2.5);
   link lists (`etc/link-lean-first-{common,cluster3}.txt`: `grpc_Server__Serve: model_Serve`,
   `model_Serve: model_acceptRun model_acceptRunConns model_respond model_finishStream`, leaves).
3. Then B2, B3; full build, tcb `--check --update` (net +1), collections, interfaces, gen-init,
   gate; delete `Scratch/`.

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
