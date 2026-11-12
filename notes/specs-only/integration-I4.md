# Integration I4: the server (2c, 2d, 2e, 2f)

Owned: `SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/` (but `api/v3rpc/`, `apply/`, `txn/`, the
v3lockpb/v3electionpb message files): the package's `ApiReq`/`ApiApply`/`ApiBoot` and specs,
`errors/`, `read/`, `cindex/`, `api/{membership,snap,v2stats,v3compactor,v3alarm,v3election,v3lock,
rafthttp}/`; `storage/*.lean`, `storage/wal/`; `config/`, `features/`; `pkg/v3/{wait,idutil,notify,
schedule}/`; the snippets `examples/specreq/{etcdserverreq,wait,etcdserverapply,cindex,schedule,
etcdserverboot,rafthttp}/`.

## Build

`etc/specs-build.sh --dir` of every owned directory in one run (`etcdserver`, `etcdserver/{errors,
read,cindex}`, `etcdserver/api/{membership,snap,v2stats,v3compactor,v3alarm,v3election,v3lock,
rafthttp}`, `storage`, `storage/wal`, `config`, `features`, `pkg/v3/{wait,idutil,notify,schedule}`):
**OK, 399 modules** (each directory passes; they were built together). The directories that import
these and that I do not own also build: `etcdserver/{api/v3rpc,apply,txn}`, `auth`, `lease`,
`net/http` (375 modules, OK).

Snippets: `cd examples && go vet ./specreq/{etcdserverreq,wait,etcdserverapply,cindex,schedule,
etcdserverboot,rafthttp}/...` clean; `gofmt -l` of the seven directories (the `//go:build ignore`
files of `etcdserverapply/` included) prints nothing. No snippet needed a change: the one mention
of `urlsRight` (`etcdserverboot/boot.go:167`) names W0's right now, unchanged.

## What changed, by file

### `etcdserver/ApiReq.lean` (2c)
- **`traceAt` removed** (I5 switched 3a to `TraceUtil.traceOpt`; no user left).
- **`IrrBody` is 3h's** (the coordinator's decision). 2c's own `IrrBody`, `opMsgDepth`,
  `opsMsgDepth`, `txnMsgDepth` and the provisional `alarmReqOwn` are gone; `export EtcdServerPb
  (IrrBody opMsgDepth opsMsgDepth txnMsgDepth alarmReqOwn)` keeps the names under `EtcdServer`
  (3a's `apply/ApiResult.lean` and 2a's `v3rpc/Api.lean` build unchanged). 3h's `.authToken name`
  carries no password (Go proposes none, `v3_server.go:872`), so the update's request is now
  separate from the message:
  - `irrAsks ir ao` (new): which client request `ao : Option Req` the commit fires (a client
    request its own; the token the `authenticate name pw` the server checked; an alarm activation a
    client's `.alarmActivate` or none (the quota's); publications and `.noop` none);
  - `irrUpd γ p tls lo ao rep Q`, `irrFired ao Q` (new): the update and its fired `Q`;
  - `IrrBody.fires`/`irrStep`/`IrrBody.backOk`/`IrrBody.wf` → `irrAsks`/`irrUpd`/`irrBackOk`/`irrWf`
    (functions, not dot-notation in 3h's namespace);
  - `irrReply` over 3h's constructors: an activation's reply is the `*AlarmResponse`
    (`reqReply γ (.alarmActivate al)`), as a client's `Alarm(ACTIVATE)` reads it (3a's item 12).
  - `irrOwn p dq ir` stays (3h's `irrOwn` has no fraction for the inner messages the writers lend);
    new law `irrOwn_own`: at `dq = 1` it is 3h's `EtcdServerPb.irrOwn`.
- **`srvFiredAns`** (new) and **outcome 1 of `SrvCallTriple`** now carries `⌜srvFiredAns res⌝`: no
  token refusal (`errRetryAuth`) nor learner refusal is fired (2a's `firedAns`, I3 item (a)); the
  apply-time ones change nothing, so the invariant gives them back.
- **`srvStep_step`** (new law, I3 item (b)): with `tls ∈ {none, p}`, no empty-key range and a fired
  answer, `srvStep p tls` is `Step p`.
- **`txnChecked_safe`** (new law, I3 item (e), 3b's request): `txnChecked t → Txn.txnSafe t`.
- **`ctxNoIncoming`** is now a definition over 2a's `Grpc.ctxInMD ctx none ∗ Grpc.ctxPeerCN ctx
  none` (I3 item (f)).
- **`srvWatchable_hist`** (new law; 3f's item 3, the bridge from mvcc's history to the cluster's):
  `srvNode ∗ srvWatchable ∗ watchableAt w γm ∗ mvccLb γm h ⊢ srvMvcc s γm ∗ |={⊤}=> ∃ σ, etcdLb ∗
  ⌜KVHist.IsView σ.kv h⌝`. `ApiReq` now imports `ApiApply` (no cycle) and `etcdserverpb/Api`,
  `txn/Api`.
- Header: `permittedSince` (W0 round 6) for `authOffSince`; the internal-request paragraph and the
  vocabulary list rewritten.

### `etcdserver/errors/Api.lean` (2c)
- **`srvErrShape` strengthened** (I3 item (c); 2a's `srvErrOk` is an abbrev of it): the non-context
  branch carries `⌜Grpc.cmpErr err⌝`, and the unmapped case `srvMsgIndef m` (new: a message that is
  the description of a mapped error names an indefinite one: 2a's `indefMsg`). Imports rpctypes.
- **`errors_init`** (new law; 3a/I5's request): `etcdserver/errors`' 20 mapped sentinels hold
  `srvErrVal` of their `EtcdErr`.

### Request-path specs (2c), `EtcdServer__*.lean`
- **`srvGate s q`** (2e's round-1 decision, "from 2e, round 1", item 1, unmet until now) in the pre
  and post of every client-facing method: the 26 `SrvCallTriple` specs (`Range`, `Put`,
  `DeleteRange`, `Txn`, `Compact`, the lease, auth, user and role methods, `Authenticate`,
  `LeaseTimeToLive`), `RangeStream`, `LeaseRenew`, `Alarm` (binder `q : Qp`). The internal paths
  (`raftRequest`, `processInternalRaftRequestOnce`, `doSerialize`) do not take it: their other
  callers are `GoAttach` goroutines, which the stop drains (`wg.Wait`) before `Cleanup`.
- `raftRequest`, `processInternalRaftRequestOnce`: over `ao`/`irrAsks`/`irrUpd`/`irrWf`/`irrBackOk`;
  outcome 1 with `srvFiredAns`.
- `Alarm`: `ir` is 3h's message model, `ao` whose update; the reply is `reqReply γ aq` for a client's.
- `AddMember`, `UpdateMember`, `PromoteMember`, `RemoveMember`, `configure`, `LeaseRenew`: outcome 1
  with `srvFiredAns` (they already took `srvGate`, or got it above).
- Sketches: `Put`, `Txn`, `Authenticate` (the password is the update's; the invariant decides
  firing by the step at the commit, no `rv` needed), `Range` (the read slot realized, below).

### `etcdserver/ApiApply.lean` (2d)
- **New laws, the bridge to 2e's `Cluster`** (W0 declined making `Cluster` a structure, so the
  bridge stays): `srvNode_raftNames` (raft's namespace `etcdN .@ "raft"`, `dup = false`, 2e's
  `srvNet γ.etcd ν` over `γ.raft` with `ν.img = imgAt γ`): it discharges `histPropose`'s namespace
  premise and 2c's one-shot assumption. With `isServer_names`, `srvMember_node`, `srvNode_agree`,
  one `Names` per member.
- **The read slot realized over the owners' read vocabulary** (2d's round-1 F1): new persistent
  `srvMvcc s γm`, `srvLessor s γl`, `srvAuth s γa`; laws `srvStores_agree`; `srvReadAt_mvcc` (a
  persistent atomic accessor over 3e's `mvccState`, committing a history point `≥ k` with the same
  KV history: what `txn.Range`'s update needs); `srvReader_mvcc`, `srvReader_lessor` (a reader
  token of 3e's/3c's pool for a thread token: 3e's item 1, 3c's round-1 item 4, I3 item (d));
  `srvReadAt_lessor` (3c's history lower bound, its later states' ids a lease table of a point
  `≥ k`); `srvReadAt_auth` (3d's store-index to cluster-index link: 3d's round-1 S1, for
  `permittedSince`).
- **`srvNode_raftOk`** (new law; 2f's round-1 F4): the server's interface value is 2f's
  `Rafthttp.raftOk ν (W64 id)`, from `srvNode` (which holds from the server literal, so before
  `tr.Start()`).
- `expiredLeases` (provisional, 3c's) **removed**: `revokeExpiredLeases.spec` takes 3c's
  `Lease.expiredSl γl sl ids` with `srvLessor s γl`.
- Docstrings after 2e's round 2: the durability paragraph, `srvStopped`, `rnCfgOk`, `rnStopped`
  (the durable state is the program's `diskState`; the loop deposits `readyEnter` through
  `diskAcc` before `Save`).
- Imports mvcc's `Api`/`ApiWatch`, lease's, auth's `Api`.

### `etcdserver/ApiBoot.lean`, `NewServer.lean` (2e)
- **`ApplyCfg`, `applyCfgIs`, `clusterApplyCfg` and their laws dropped** (2d round 1b: members may
  differ; nothing used them): `cluster_alloc.spec` and `NewServer.spec` lose the `mc` binder and
  premise.
- **`urlsRight`/`urlsRight_excl` deleted**: W0's `EtcdModel.urlsRight` (moved by I1); `urls_reserve`
  mints it; `AddMember`/`UpdateMember` resolve to it.
- **Slots filled from their owners**: `mvccBootCfg` = 3e's `storeCfgOk` condition (a definition);
  `leaseBootRes cfg ecfg` = `⌜ecfg.leaseExpiry = false → Lease.leasesOutliveRun⌝` (3c item 6);
  `authBootRes cfg γ` = simple or 3d's `Auth.jwtTokOk γ cfg.AuthToken` (3d item 11; now takes the
  cluster; `NewServer` and `authBootRes_intro` follow); `backendEnvOk` = `⌜Backend.etcdVerifyUnset⌝`
  (4a).
- `irrIsRevoke` (provisional) → 3h's `EtcdServerPb.irrIsRevoke` (exported); `transporterOk tp`
  (provisional) → 2f's `Rafthttp.transporterOk tp ν id` (`isConnectedSince`,
  `isConnectedToQuorumSince`, `numConnectedSince` take `ν`, `lid`).
- **`crashScope`'s docstring** (and the header's scope paragraph): its first conjunct guards a
  reproduced raft safety bug (`issues/raft-commit-lost-with-entries-kept.md`): outside it a restart
  is unsound, not merely unproved.
- Sketches with an "Integration (I4)" paragraph: `NewServer` (the checkpointer's `ckptGate` at `R :=
  srvStarted`, the compactor's `Rev` token, the lessor's `beOk`), `applySnapshot` (the whole
  `mvccRestoreGate`, the lessor's `Recover` with `beOk` and the deleter's `rdOk`, the auth store's
  `Recover`), `applyEntryNormal` (`Promote`'s `ckptGate`, `rdOk` after an install, `ErrNoSpace`
  after a write), `monitorKVHash` (a `mvccRestoreGate` share), `raftNode.start` (the `readyEnter`
  deposited through `diskAcc` before `Save`, fired inside `Save`'s update; `disk_crash`).

### URLs (I1's / the coordinator's request)
- `config/Api.lean`: provisional `Config.urlsStrs` removed; `cfgHeap_intro` over 1c's
  `Types.urlsStrs`. `urlsMapStrs` stays (no `NewURLsMap` spec).
- `rafthttp/Api.lean`: provisional `urlsHosts`, `urlsAt` removed; every rafthttp spec and 2e's
  membership/`ApiBoot` uses `Types.urlsHosts`, `Types.urlsAt`. `urlsNoComma` stays (`NewURLs`
  accepts a comma). Imports `client/pkg/v3/types/Api`.

### v2stats (2e) and rafthttp (2f)
- 2f's provisional `serverStatsOk`, `followerStatsOk` are abbrevs of 2e's `V2stats.isServerStats`,
  `isFollowerStats`; `leaderStatsOwn` of 2e's new `V2stats.leaderStatsOwn` (exclusive, with
  `leaderStatsOwn_is`), which `NewLeaderStats` now returns (the transport deletes followers without
  the stats' lock: exclusivity was 2f's need).

## Provisional names

Resolved: `traceAt`; 2c's `IrrBody` (and depths, `alarmReqOwn`); `ApplyCfg`/`clusterApplyCfg`;
`urlsRight`; `Config.urlsStrs`, `Rafthttp.urlsHosts`/`urlsAt`; `serverStatsOk`, `followerStatsOk`,
`leaderStatsOwn`; `expiredLeases`; `irrIsRevoke`; `transporterOk`; `mvccBootCfg`, `leaseBootRes`,
`authBootRes`, `backendEnvOk`; `srvErrShape` = 2a's `srvErrOk` (identified by I3, strengthened
here); `ctxNoIncoming` (now 2a's).

Left, with why:
- `irrOwn p dq ir` (2c): 3h has no fractional variant; requested of 3h: wrap/unwrap laws of a
  request message lent at `dq` (`&pb.InternalRaftRequest{Put: r}`), `irrOwnH` at a fraction for the
  inner messages. `irrOwn_own` ties the whole-fraction case.
- `rsSink` (2c's slot for 2a): 2a has `rsSinkOf`/`rsChunk` but no `rsSink`; 2a should state it.
- `txnChecked` (2c's, opaque; 2a introduces it): stays 2c's by I3's reading.
- `srvWatchable` (2c's slot): kept; realized by `srvWatchable_mvcc` (3f's `watchableAt`) and the
  new `srvWatchable_hist`.
- 2d's `entryAt` (3h's raftpb: no such predicate yet; 3a's `apply/Apply.lean` uses it too),
  `beSnap bs γ k` (4a's `Backend.beSnap γ s I bs` is over images, not history points: needs a
  predicate "image `I` is the state machine at point `k`", 2d's or 4a's), `dbReader rc γ k` (same:
  2e's `Snap.dbReader r img` over images), `mergedSnap`, `httpForbidden` (2e's etcdhttp `httptypes`,
  untranslated names only).
- 2e's `raftNodeBuilt` (2d's `rnInit` is over the value, `raftNodeBuilt` over the pointer and a
  `Cluster`: the identification `raftNodeBuilt rn γ id st ⊢ ∃ v N n, rn ↦ v ∗ rnInit v N id n ∗
  ⌜N.etcd = γ⌝` is a law to add once 2d's `rnCfgOk` names the WAL storage `st`), `v3rpcBootCfg`
  (2a's), `raftNodeBootCfg` (2d's, introduction stated), `gaugeVecOk` (no prometheus boundary yet).
- 2f's `urlsNoComma`, `snapMsgOwn`, `imgBytes`, `errChanOk` (`errChanOk` is the server's, used by
  2d's `srvNode_errorc` as is: no change needed).

## Sketches checked against callees, and fixes

- **`Authenticate`**: its sketch relied on `.authToken name pw rv` carrying the password and the
  checked revision; 3h's message carries the name only. Fixed by `irrAsks` (the update over
  `authenticate name pw`); the invariant fires iff the step admits the apply's answer at the commit,
  which is the revision argument without needing `rv` in the model.
- **Client `Alarm(ACTIVATE)`**: 3h's `alarmReqHolds` maps `ACTIVATE` to `.alarmActivate al` for
  both the client and the quota; 2c's spec distinguished them by the model. Fixed by `ao`.
- **`Range`** (and every linearizable read): the sketch cited "3b's `Range` over the member's store,
  at an applied point" with no law turning 2d's `srvApplied` into 3e's update or 3d's auth index.
  Fixed by the `srvReadAt_*` and `srvReader_*` laws.
- **Request path vs `HardStop`**: 2e's stop takes the whole `srvGate`, but no request-path spec took a
  share, so the stop's premise was unprovable for a program that ran any request. Fixed (above).
- **2a's handlers vs 2c's outcome 1**: token refusals could be fired, which 1c's `AttemptTriple`
  cannot take. Fixed by `srvFiredAns`.
- **`togRPCError` vs `srvErrShape`**: missing `cmpErr` and the unmapped message's meaning. Fixed.
- **`histPropose`'s namespace premise** and 2c's `dup = false`: no law gave them. Fixed by
  `srvNode_raftNames`.
- **2f's `Process` needs `raftOk` from `tr.Start()`**: no law. Fixed by `srvNode_raftOk`.
- **`raftNode.start`'s write**: still said the WAL's durable invariant holds `raftState`
  (pre-round-2). Fixed (the `diskAcc` deposit).
- **The compactor's `Rev`** (not fixed: a gap, see below).

## Needed from directories I4 does not own

- **3e** (`storage/mvcc/Api.lean`): `V3compactor.revGetter` is persistent (`isCompactor` is, and
  `Run` may fork its loop more than once), but `KV.Rev.contract` takes `revRd γ true` =
  `mvccRevTok γ`, exclusive. Needed: a persistent `Rev`/`FirstRev` right once a token is lent (Rev
  reads no storage, only the read transaction's lock), e.g. `mvccRevTok` made persistent, with the
  shutdown law counting `mvccRevLent` as now. Until then `NewServer`'s compactor wiring is not
  provable from 3e's specs.
- **3h** (`api/v3/etcdserverpb/Api.lean`): `irrOwnH` at a fraction for the inner request messages,
  and the wrap/unwrap laws (`&pb.InternalRaftRequest{Put: r}` with `r` lent at `dq`, back out);
  2c's `irrOwn p dq ir` is then a definition.
- **2a** (`api/v3rpc/Api.lean`): identify `V3rpc.firedAns` with `EtcdServer.srvFiredAns` (same
  body), use `srvStep_step` for the composition, cite `txnChecked_safe`; state `rsSink` (2c's slot)
  over `rsSinkOf`/`rsChunk`; every handler over a 2c method now passes a `srvGate s q` share (the
  `v3rpc.Server`'s realization holds one per in-flight call: the gRPC server is drained before
  `HardStop`).
- **3a** (`apply/`): nothing breaks (I5 already switched to 3h's `.authToken name`); `irrReply` of
  `.alarmActivate` is now the `*AlarmResponse` reply (`reqReply γ (.alarmActivate al)`), which
  `ApiResult`'s `resultAt` must give for an activation (it was `True`).
- **4a/2d** (backend): a predicate "image `I` is the state machine at history point `k`" so that
  2d's `beSnap bs γ k`/`dbReader rc γ k` become definitions over `Backend.beSnap`/`Snap.dbReader`.
- **Goose configuration** (I1's item for 2e): `v3client.New` (`server/v3/etcdserver/api/v3client`)
  is not translated, not even names-only, so it has no spec; the in-process client of
  v3election/v3lock is taken as `ClientV3.isClient c γ none` by their specs (`isLockServer ls c`),
  established by untranslated embed code. Translating `v3client` (names at least, `New` with a
  body) would let 2e state `New.spec` (from `isServer s γ` and a gate share, 1c's
  `NewCtxClient.spec`/`clientBare_assemble`); recorded, not done.
- **R1** (via I2): the stored entries' term bound at a start (2d's `applyBatch_terms` for the
  restart's first batch) is still asked; `applyAll`'s sketch handles `raftTerm = 0` meanwhile.

## Requests to my batches, checked

- W0/I1 `urlsRight`: met. I1's URL names: met. I3 (a)-(f): met ((d) by `srvReader_mvcc`, the
  thread-token pool law over `srvNode`; handlers reach `srvNode` through `isServer_names`).
- 3c: items 3 (expiry channel: met), 4 (history tie: `srvReadAt_lessor`), 6 (`leaseBootRes`: met),
  round 1 items 1, 2 (`rdOk`, `ckptGate`: sketches), 4 (reader tokens: `srvReader_lessor`).
- 3d: items 5 and round-1 S1 (the index link: `srvReadAt_auth`), 11 (`authBootRes`: met).
- 3e: items 1 (`srvReader_mvcc`), 2 (the compactor's token: gap above), 3 (`mvccRestoreGate`:
  sketches), 5 (images: realization of `memberDisk`, unchanged).
- 3f: items 1, 3 (`srvWatchable_mvcc`, `srvWatchable_hist`); item 2 (two readers per stream):
  by `srvReader_mvcc` twice.
- 4b: `traceAt` dropped (met); `beStoredCI`/`txStoredCI` (cindex's provisional backend names) not
  restated: still provisional in `cindex/Api.lean`, to become the cindex's view family `R` over
  4a's meta key (4b's item 2): left.
- 3a: items 1-5 of "from 3a" to 2d are realization of 2d's invariant (sketched in
  `applyEntryNormal`); `nextOk`, `authnIdx`, `kvSt`/`kvOk`, `statusOk`, `ciOk`, `snapSrvOk` remain
  3a's provisional slots that 2d's realization supplies (I5's list): no statement of mine changed
  for them.
