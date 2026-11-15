# Batch 2c: the server's request path (report)

Scope: `server/etcdserver/v3_server.go` (the request path), `server/etcdserver/read/` (the
linearizable read loop), `pkg/{wait,idutil,notify}`. Everything builds (`etc/specs-build.sh --dir`
of the five directories: 162 modules, with 2d's and 2e's files of the same directory); the snippets
pass `go vet`.

## Files

Vocabulary:
- `SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/ApiReq.lean` (namespace `EtcdServer`)
- `SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/read/Api.lean` (namespace `Read`)
- `SpecPlan/Spec/go_etcd_io/etcd/pkg/v3/wait/Api.lean` (`Wait`), `idutil/Api.lean` (`IdUtil`),
  `notify/Api.lean` (`Notify`)

No shared `etcdserver/Api.lean`: when I started, 2e's `ApiBoot.lean` already had the handle
`isServer s γ` and 2d's `ApiApply.lean` the cluster-level vocabulary (`Names`, `histAt`,
`answered`, `srvApplied`). My specs take 2e's handle, and my sketches cite 2d's laws.

Specs (`SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/`):
- client-facing: `EtcdServer__{Range,RangeStream,Put,DeleteRange,Txn,Compact}`,
  `EtcdServer__{LeaseGrant,LeaseRevoke,LeaseRenew,LeaseTimeToLive,LeaseLeases,Alarm}`,
  `EtcdServer__{AuthEnable,AuthDisable,AuthStatus,Authenticate,UserAdd,UserDelete,
  UserChangePassword,UserGrantRole,UserGet,UserList,UserRevokeRole,RoleAdd,RoleGrantPermission,
  RoleGet,RoleRevokePermission,RoleDelete,RoleList}`, `EtcdServer__Watchable`;
- internal: `EtcdServer__{raftRequest,processInternalRaftRequestOnce,doSerialize,AuthInfoFromCtx,
  requireAuthInfo,checkLeaseRenew,checkLeaseTimeToLive,checkLeaseLeases,newHeader,
  parseProposeCtxErr,waitAppliedIndex,waitLeader,leaseTimeToLive}`, `getRequestType`.
- `read/`: `NewRead`, `Read__LinearizableReadNotify`, `Read__LinearizableReadLoop`,
  `Read__requestCurrentIndex`, `Read__sendReadIndex`, `uint64ToBigEndianBytes`, `isStopped`.
- `pkg/v3/wait/`: `New`, `list__Register`, `list__Trigger`, `list__IsRegistered`, `NewTimeList`,
  `timeList__Wait`, `timeList__Trigger`; `idutil/`: `NewGenerator`, `Generator__Next`, `lowbit`;
  `notify/`: `NewNotifier`, `Notifier__Receive`, `Notifier__Notify`.

Snippets: `examples/specreq/etcdserverreq/{kv,lease,auth,read}.go`,
`examples/specreq/wait/{wait,idutil,notify}.go`.

## Exported vocabulary

`ApiReq.lean`:
- `srvStep who rq` is the relation the server fires updates by. It is W0's `Step`, plus two
  disjuncts:
  - for a linearizable read, the `AuthEnable` race (`authOff`);
  - `LeaseRenew`'s permission denial, which W0's `leaseStep` lacks.
- `SrvCallTriple e P B γ who rq rep reply` is the call shape every client-facing method uses. The
  call ends in one of three outcomes:
  - (1) fired: the update fired, the reply sent (`srvReply`);
  - (2) unfired: the update given back (`srvUnfired`);
  - (3) unsettled (`srvIndef`).
- `srvErrOf err e` (opaque, pure): the server error value that `togRPCError` maps to `e`.
  - Laws `srvErrOf_ne_nil`, `srvErrOf_fun`.
  - Law `readErr_indef`: the read loop's errors are unsettled.
- `reqPrin ctx who` (opaque, persistent): the principal of the request context. Law
  `reqPrin_persistent`.
- `reqReply γ rq`, `srvReply`: the replies, built from W0's and 1c's reply predicates.
- The model of an internal request:
  - `IrrBody`: a client request, an alarm activation, a publication, `authToken`, `noop`;
  - `irrStep`, `IrrBody.fires`, `IrrBody.depthOk`;
  - `opMsgDepth`, `opsMsgDepth`, `txnMsgDepth`;
  - `respTy`, `irrReply`, `applyResult`.
- Provisional slots, to be identified with their owners' predicates:
  - `irrOwn`, `alarmReqOwn` (3h's);
  - `txnChecked`, `rsSink` (2a's);
  - `srvWatchable` (2d's and 3f's);
  - `traceAt` (4b's).

`read/Api.lean`:
- `readEnv srv rf rγ γi A`: the contract of the server and raft interfaces, plus the right to
  register read contexts. Its pure part is `readEnvOk`.
- `readNew`, `readAt` (persistent), `readLoopTok`.
- `readErr` (pure): the read path's errors.
- `recvAny`, `readLbQ`, `be64`, `readStateVal`.
- Laws: `readNew_init` (start the read path once its environment is known), `readAt_persistent`.

`wait/Api.lean`:
- `listAt l γw P` (persistent): the registry; the triggerer of `id` supplies `P id x`.
- `waitToks`/`waitTok`: the right to register an id once.
- `waitRecv γw id ch`: the one receiver of `id`'s value.
- `timeListAt tl P`, `timeChan ch P d`.
- Laws: `waitToks_take`, `waitRecv_recv`, `timeChan_recv`, persistence, timelessness.

`idutil/Api.lean`:
- `IdSpace`; `idPrefixes`, `idPrefix` (one token per run of a member's prefix); `idGen`.
- `idFresh γi id`: the id was issued once and is not `0`.
- Laws: `idSpace_alloc` (distinct, non-zero prefixes), `idPrefixes_take`, `idFresh_excl`,
  `idFresh_ne_zero`.

`notify/Api.lean`:
- `notifierAt`, `notifyLb γ k` (at least `k` notifications), `notifyChan γ ch k` (the channel of
  epoch `k`).
- Laws: `notifyChan_recv` (a receive completes only after the `k + 1`-th notification),
  `notifyLb_mono`, persistence.

## Main changes from the old specs

- **W0's model throughout.** The old vocabulary is gone:
  - the server records `E`, `ρ`, `ReqNames`;
  - `kvState`, `kvOpStep`, `putPermit`;
  - the logs' certificates (`idxCert`, `kvRevLb`);
  - `srvLeadTimeReader`, `E.RD`, the reader slots;
  - `idCred`.

  Every spec takes `isServer s γ`, a thread token, the request's principal and the caller's update
  over `etcdState γ`, written in the triple.
- **Relaxed premises:**
  - Put: `op.leaseID = 0` dropped (leases are modelled).
  - Compact: the revision certificate dropped (`ErrFutureRev` and `ErrCompacted` are fired answers).
  - Auth on and off are one spec; the mode is part of the state.
  - The trace-context premises dropped (`EnsureTrace` makes a trace).
  - The id credit dropped (the receipt bound is at its owner).
- **Strengthened: the update is given back when the request never took effect** (outcome 2). This
  covers refusals before proposing and the apply's `ErrAuthOldRevision`. W0's K4 asks for it: "a
  write rejected for a stale auth revision is not fired".
- **Reads go through a read registry** (2d's cluster invariant). The caller's persistent update is
  registered at the call and fired at every history point after it, so a linearizable read is
  answered at the state the member read. The read loop's spec is restated over R1's read API only:
  `committedLb` in; the applied index and a covering committed log out.
- **The wait registry, ids and notifier** are restated as small generic APIs with no client
  bookkeeping:
  - wait: one answer predicate per registry, registration tokens;
  - ids: one freshness token per id;
  - notifier: an epoch counter.

## Functions left out

| Functions | Why |
|---|---|
| `Downgrade`, `downgradeValidate`, `downgradeEnable`, `downgradeCancel` | Untranslated; W0's model has no downgrade. |
| `rangeStream`, `adjustChunkLimit` | Untranslated; `RangeStream`'s assumed contract covers them. |
| `newNotifier`, `notifier.notify` | Internal to `readAt`'s realization. |
| `wait.NewWithResponse`, `waitWithResponse.*` | No server user. |
| `interface.go`'s methods | 2e's file; their spec is item 7 of my `req/` section. |
| `exceedsRequestLimit`, `isPriorityRequest`, `firstCompareKey` etc. | 2e already wrote them (`util.go`, `tracing.go`). |

Untranslated, so these specs are **assumed contracts** until their bodies are translated:
`RangeStream`, `Alarm`, `waitAppliedIndex`, `waitLeader`, `leaseTimeToLive`. **Suggestion:** add
them to `Code/.../etcdserver.toml`.

## Decisions for the user

1. **The `doSerialize`/`AuthEnable` race** (`nonissues/etcd-doserialize-auth-enable-race.md`,
   blocks-proof).
   - What the code does: a linearizable read whose permission check ran while auth was disabled can
     be answered from a state where auth is enabled, without a check.
   - How I stated it: as the code does. `srvStep`'s race disjunct answers by the step at that state
     with auth off. With it the server's specs are true, but 2a cannot meet the client's `Step`-only
     contract.
   - Options:
     - (a) a fix on the fork: re-check the permission after the read when auth is enabled by then.
       The disjunct goes.
     - (b) a scope premise: no `AuthEnable` while reads are in flight. A cluster-level premise; it
       has no local statement.
2. **`Authenticate` needs a persistent update.** Its answer rests on a state the member read, which
   only the read registry can fire at. The client passes a one-shot update today. W0 would need to
   make the update persistent without making the client resend
   (`req/go_etcd_io_etcd_api_v3.md`, "from 2c", item 2).
3. **W0's `leaseKeepAlive` lacks a permission refusal** (`checkLeaseRenew`). Asked of W0; until then
   `srvStep` carries the disjunct.
4. **The registries' predicates are client parameters.** `listAt`'s `P` and `timeListAt`'s `P`
   are, as in Perennial's lock and channel idioms. This departs from "TaDa, not HoCAP" for generic
   synchronization primitives. The alternative is ghost tokens per id, which every client would
   thread.
5. **Request-id freshness.**
   - Across members: an allocation premise (`idSpace_alloc`: distinct, non-zero 16-bit prefixes),
     which moves the old `NewServer` premises.
   - Across one member's runs: still a trusted assumption of `Next`'s model
     (`nonissues/etcd-request-id-restart-reuse.md`).
6. **Premises kept on client-facing server specs:**
   - `Range`/`RangeStream`: `key ≠ [] ∧ validSort`, the gRPC check's.
   - `Txn`: `txnChecked`, plus the depth premise for writes.
   - `Compact`: `rev ≠ 0`, W0's scope restriction (`issues/etcd-restore-scheduled-compact-zero.md`),
     here because this is the only proposer of compactions.

## Open questions

- **The read registry has to know the read's answer.** A read update's commit names the answer, and
  `Step`'s range answers are not unique (sort ties). The registry fires every answer `srvStep`
  allows at each point (finitely many). Or, if 3b exposes the implementation's answer as a function
  of the state, it fires once with that answer. 2d's `answered` (commit-time answers of writes)
  needs the same function from 3a/3b.
- **2d's `Names` vs 2e's `Cluster`.** `isServer s γ` is over W0's `Cluster`; `srvApplied`/`histAt`
  are over `Names`. They need one map between them (item 1 of my `req/` section).
- **One-shot proposals need at-most-once firing.** The raft cluster must be allocated `dup = false`,
  or 2d's invariant must fire only an entry's first committed occurrence.
- **2b's `srvCtxPrin` and my `reqPrin` are the same fact.** 2a's `mdPrin` asks for a law to
  `reqPrin`.

## `req/` sections written (`## from 2c`)

- `go_etcd_io_etcd_server_v3_etcdserver.md`: 2d/2e; 9 items:
  - the cluster name;
  - `isServer`'s contents;
  - `readEnv` at `start`;
  - the proposal update;
  - the read registry;
  - the applied-state reads;
  - `LinearizableReadNotify`;
  - the internal requesters;
  - `srvWatchable`.
- `go_etcd_io_etcd_server_v3_etcdserver_api_v3rpc.md`: 2a:
  - `togRPCError`/`srvErrOf`;
  - `reqPrin` vs `srvCtxPrin`;
  - the validations;
  - persistence;
  - `rsSink`'s laws;
  - outcome 2 at the client.
- `go_etcd_io_etcd_api_v3.md`: W0: the keep-alive denial, `Authenticate`'s persistence, the race.
- `go_etcd_io_etcd_server_v3_etcdserver_apply.md` (new): 3a: `applyResult`, the answers,
  `CheckTxnAuth`.
- `go_etcd_io_etcd_server_v3_etcdserver_txn.md` (new): 3b: `txn.Range`, `txn.Txn`, `Count` at the
  applied point.
- `go_etcd_io_etcd_server_v3_auth.md`: 3d:
  - `reqPrin`'s realization;
  - `WithRoot`;
  - `CheckPassword`, `GenTokenPrefix`, `tokenUser`;
  - the revision;
  - `bcrypt`.
- `go_etcd_io_etcd_server_v3_lease.md` (new): 3c: `Lookup`, `Leases`, `Renew`, `leasehttp`.
- `go_etcd_io_etcd_api_v3_etcdserverpb.md`: 3h: `irrOwn`, `alarmReqOwn`, `Marshal` at depth.
- `go_etcd_io_raft_v3.md`: R1's read API used as stated; `dup = false` for one-shot proposals.
- `go_etcd_io_etcd_pkg_v3_traceutil.md` (new): 4b: `traceAt`.

## Answers to 2a's `## from 2a` (`req/go_etcd_io_etcd_server_v3_etcdserver.md`)

2a's section appeared at the end of my run; I re-read it. 2a's `v3rpc/Api.lean` already uses
`isServer`, `srvErrOf`, `SrvCallTriple`, `txnChecked` and `rsSink`.

1. **`srvStep` vs `Step`.** This is the user's decision (decisions 1 and 3 above); 2a cannot close it.
2. **`reqPrin_of_md`.** The law belongs in 2a's module (or 3d's). It mentions 2a's `Grpc.rpcCtx` and
   `V3rpc.mdPrin`, and `v3rpc/Api.lean` imports `ApiReq.lean`, so stating it in `ApiReq` would make
   an import cycle. I asked 3d for `AuthInfoFromCtx`'s realization of `reqPrin`.
3. **Context errors.** Done: `srvErrOf` never names a context's own `Canceled` or
   `DeadlineExceeded` (header corrected). Such errors are `srvIndef` vacuously, which is what
   `readErr_indef` needs. The condition on unmapped errors' messages is 2a's `togRPCError`
   boundary: it is stated over 2a's `Grpc.errMsg`.
4. **`MaxTxnOps ≤ 4999` in `isServer`.** That is 2e's handle.
5. **`Alarm`'s `ACTIVATE` takes no update.** Done:
   - `IrrBody.fires` is now true only for `.req`;
   - an alarm or a publication commits by the `envUpd` that the cluster's invariant holds;
   - `Alarm.spec`, `raftRequest.spec` and `processInternalRaftRequestOnce.spec` require and give
     back the update only for `.req`;
   - my `req/` item 8 asks 2d/2e for the `envUpd` in the invariant.
6. **`rsSink`'s chunks.** `rsSink`'s `ms` is the list of chunks sent, which matches 2a's `rsChunk g
   j m`. The sink is 2a's provisional slot, so its send laws (each chunk appended; the last with `Q`
   and `streamMatches`) are 2a's to state in `rsSink_intro`/`rsSink_out`; they should move the
   predicate into their module.
7. That item is 2e's.

New package namespaces: `Read`, `Wait`, `IdUtil`, `Notify` (as in the README's table).

## Round 1 repairs (2026-11-09)

Reviews: `reviews/2c-provability-1.md`, `reviews/2c-completeness-1.md`; coordinator's decisions.
Everything builds (`etc/specs-build.sh --dir` of `etcdserver`, `etcdserver/{errors,read}`,
`pkg/v3/{wait,idutil,notify}`); the snippets pass `go vet`. **Decisions 1-3 above are superseded**:

- **`srvStep` (decisions 1, 3; prov. F7, compl. F9).** The `doSerialize` race and keep-alive disjuncts
  are gone: W0's round-4 `Step` checks a read's permission at an auth table since the call's `lo`
  (every server spec takes `authLb γ lo`) and has `leaseKeepAlive`'s `permErr`. What remains:
  `srvStep p tls rq σ σ' res lo := Step p rq … lo ∨ (write ∧ Step tls rq …) ∨ emptyRangeStep`.
  - **The principal is what the code reads** (F7): `reqPrin ctx p tls`, `p` with auth enabled (the
    token's user, else the certificate's name), `tls` the certificate's name used with auth disabled.
    A write proposed with auth off and applied after `AuthEnable` runs as `tls`: filed as
    `nonissues/etcd-write-tls-principal-auth-enable.md`; asked W0 for the `ctxPrin` side.
  - `emptyRangeStep` (compl. F5): `Range` of the empty key (the health checks), which the server
    reads as the key `""` (an empty answer); the `key ≠ []` premise is dropped.
- **`Authenticate` (decision 2; prov. F1, compl. F4)**: a one-shot update. W0's answer carries no token
  (`tokenUser` comes with the reply). The token entry `.authToken name pw rev` fires the update at its
  commit iff the auth revision is still the checked one (else it is given back, `IrrBody.backOk`, and
  the loop retries); the apply's `ErrAuthNotEnabled`/`ErrAuthFailed` are fired there. Open, asked of
  W0: `CheckPassword`'s own errors (returned before proposing) need W0's `authenticate` step to admit
  them from an auth table since `lo`.
- **`RangeStream` (prov. F2, compl. F10)**:
  - `Q` comes with the `nil` return (`streamMatches` of all the chunks), not with the last chunk.
  - New outcome: `ErrAuthOldRevision` after every chunk was sent.
  - New outcome: `ErrCompacted` with no chunk.
  - New premise: `rangeStreamOk` (default order, no revision filters).
  - `rsSink` lost `Q` and `fin`.
  - Filed: `issues/etcd-rangestream-auth-revoked-midstream.md` (the probable bug: keys read after
    a revocation are delivered, then the error; no test written) and
    `nonissues/etcd-rangestream-count-compacted.md`.
- **`readEnv` (prov. F3)**: the method triples are now Iris triples (persistent) inside `readEnv`, not
  a pure `Prop`. The pure part is `appliedPredOk`.
- **`leaseTimeToLive` (prov. F4)**: the answer holds at a reached `σ₁` with `Reach σ₀ σ₁`, and at every
  state after it. It assumes the peers are members. The partial-key-set mismatch is asked of W0.
- **Validation premises (prov. F5)**:
  - `Put`: `pr.invalid = none`; `DeleteRange`: `d.key ≠ []`.
  - `IrrBody.wf` replaces `depthOk`, with the validation and `rev ≠ 0`.
  - `Compact`'s `rev ≠ 0` names its sources (compl. F6): the compactors, W0's client contract, and
    2a's contract (requested).
- **Message ownership (prov. F6)**: `irrOwn p dq ir` (inner messages at `dq`) is given back by
  `raftRequest` and `processInternalRaftRequestOnce`, so the writers return their request message.
  3h is asked for the wrap and unwrap laws.
- **Errors (prov. F8, compl. F1/F2)**: new module `errors/Api.lean`.
  - `srvErrOf`, the sentinels `srvErrVal e` and `srvErrMapped`, `srvErrLeaf` (errors.Is is equality),
    `srvErrNotMapped`, `raftStoppedErr`.
  - `srvErrShape` = 2a's `togRPCError` precondition. Every returned error carries it.
  - Laws: `srvErrOf_val`, `_inj`, `_notCtx`, `srvErrVal_leaf`, `srvErrVal_shape`,
    `raftStoppedErr_*`.
  - `readErr` is now a transparent persistent predicate over those values; `readErr_shape` added.
  - The packages' initialization laws (globals hold `srvErrVal e`) are requested of their owners.
- **Snippets (prov. F8, compl. F11)**:
  - `txnChecked_small` introduces the snippets' transactions.
  - Notify: `notifyCount γ k` (the client's count), moved by `Notify`'s atomic update; laws
    `notifyCount_lb`, `notifyLb_count`. `ReqNotifyAfterReceive` is provable.
  - New: `ReqHealthRange`, `ReqIsRegistered`.
  - Citations of missing snippets fixed. `ReqReadAfterWrite` is marked as depending on 2e's
    `EtcdServer.LinearizableReadNotify` (compl. F12).
- **`reqPrin` introduction (compl. F3)**:
  - Stated in `ApiReq.lean`: `ctxNoIncoming` (with background/child/value laws),
    `reqPrin_noIncoming`, `reqPrin_child`, `reqPrin_value`.
  - Requested: `WithRoot` (3d, mode-dependent), `reqPrin_of_md` (2a's module: import order).
- **`IsRegistered` (compl. F7)**: it takes `waitWasReg ∨ waitNever` and returns `false ⇒ waitDone`.
  - `Trigger` accepts `waitDone`.
  - New: `waitWasReg` (from `Register`), `waitGone`, `waitNever`, `waitToks_never`, `waitRecv_never`.
- **2b (compl. F8)**:
  - `srvWatchable_persistent`, `srvWatchable_mvcc` (to 3f's `Mvcc.watchableAt`).
  - Asked of 2e: `isServer ⊢ watchMemberAt`.
  - The `srvCtxPrin`↔`reqPrin` bridge is asked of 2a.
- **Lesser**:
  - `dup = false` stated (the "first occurrence" alternative withdrawn: prov. 2nd tier 2).
  - `γ.raft.ns ⊆ etcdN` asked of 2d.
  - `idSpaceAuth` and `idSpaceAuth_add`: prefixes for joining members.
  - `Generator.Next` marked as an assumed contract across runs, with the true condition (256 ids
    per ms).
  - `AuthInfoFromCtx`'s nil case docstring corrected (compl. F15).
  - The wait answer predicate covers `*confChangeResponse` (compl. F13).
  - The `publishV3`/`servesAt` question is asked of 2e (compl. F14).
  - `Compact`'s "returns after the compaction" moved to the Margin.
  - The `LeaseRevoke` user's principal is noted as mode-dependent.

**API changes that break callers** (sent in `req/`, "from 2c (round 1)"):
- `reqPrin` (2→3 arguments); `SrvCallTriple` (`p tls`, and `lo` via `authLb`); `srvStep`'s
  arguments;
- `irrOwn` (adds `dq`); `IrrBody.depthOk` → `wf`; `.authToken name pw rev`; `rsSink`;
- `readErr` (now an IProp);
- the error vocabulary moved to `errors/Api.lean` (same namespace).

2e's member files already follow. 2a's handlers and 3h's moved copy of `IrrBody` must follow; 3h's
`IrrBody` and 2c's are to become one at integration.

New nonissues: `etcd-rangestream-auth-revoked-midstream`, `etcd-rangestream-count-compacted`,
`etcd-write-tls-principal-auth-enable` (`nonissues/INDEX.md` regenerated).

**Still open for the user / W0:**
- `Authenticate`'s `CheckPassword` errors (W0's step since `lo`).
- The `tls ≠ p` write quirk on the client side (`ctxPrin`).
- `leaseTimeToLive`'s half-attached key sets.

## Round 2 follow-ups (2026-11-09): W0's rounds 5-6 and the requests after round 1

- **W0's round 5-6 tables**:
  - `respTy` covers `Req.alarmActivate`; this was the build break at `ApiReq.lean`.
  - A client's `Alarm(ACTIVATE)` is now `.req (.alarmActivate al)`, with the client's update. The
    quota's own activation stays `IrrBody.alarmActivate`, with no update.
  - `ErrNoSpace` is indefinite. `IrrBody.backOk` now excludes indefinite errors, so a `.noSpace`
    result is outcome 1 or 3, never given back.
  - Compact's `lo`/`authLb` was already in `SrvCallTriple` (round 1).
  - `Range`'s sketch now cites `permittedSince`. `authStep`'s `lo` covers `Authenticate`'s
    `CheckPassword` errors (my round-1 open item, closed by W0).
  - `endOf` needs no change here: the request predicates are W0's.
- **4b (traces)**:
  - `traceAt` is now exclusive: an alias of `TraceUtil.traceOpt`, kept only so 3a's apply specs build
    (they should cite `traceOpt`). The persistent version was false of `traceutil`.
  - `applyResult` hands the result's trace over owned.
  - Every spec taking a request context takes `reqCtxOk ctx` (`ctxTraceIs ctx none` and
    `ctxSpanOk ctx`).
  - `doSerialize` and its closures thread `ctxTrace ctx`, the trace `EnsureTrace` installed, owned.
- **3a (round 1)**:
  - `IsRegistered`'s `waitWasReg ∨ waitNever` and `waitDone` are as 3a uses them.
  - The activation reply: `irrReply` of `.req (.alarmActivate _)` is an `*AlarmResponse` (`respTy`).
- **Not stated in my files** (realization-side; my sketches use them unchanged):
  - **3b**: `Txn.errIs`. Txn's errors are the sentinels' globals, so `srvErrOf` follows through
    `togRPCError`'s map. This matches `srvErrVal`; the law tying them is 2a/3b's.
  - **3c**: reader tokens. The lessor's reads take `lessorReaders γl 1`. My lease specs take a
    `threadTok`, and the realization lends a reader from the pool the server's invariant keeps (2e's
    `NewLessor`).
  - **3d**: the store-index to cluster-index link is 2d's. `Range`'s sketch cites it.
- **Builds**: `etc/specs-build.sh --dir SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver` OK (150 modules);
  `--dir .../etcdserver/apply` OK (74 modules). No other batch's file failed after the `traceAt`
  alias.
