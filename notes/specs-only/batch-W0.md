# Batch W0 (the anchor): report

Author's report: the files, the exported vocabulary, the changes from the old specs, what was left
out, the decisions the user should see, the open questions, the `req/` sections. Everything below
builds (`etc/specs-build.sh --dir SpecPlan/Spec/go_etcd_io/etcd/api/v3 SpecPlan/Spec/context
SpecPlan/Spec/go_etcd_io/etcd/client/v3 SpecPlan/Spec/go_uber_org/zap SpecPlan/Spec/go_uber_org/zap/zapcore`: 173 modules);
the snippets vet (`cd examples && go vet ./specreq/clientv3kv/`).

## Files

| path | what |
|---|---|
| `SpecPlan/Spec/go_etcd_io/etcd/api/v3/Model.lean` (`EtcdModel`) | the pure model: `State`, `Req`, `Resp`, `Step`, `EnvCfg`, `EnvStep`, `Reach`, `EtcdErr` |
| `SpecPlan/Spec/go_etcd_io/etcd/api/v3/State.lean` (`EtcdModel`) | the resources: `Cluster`, `etcdState`, `etcdLb`, `etcdN`, `envUpd`, `servesAt`, `errVal`, `indefErr` |
| `SpecPlan/Spec/go_etcd_io/etcd/api/v3/Wire.lean` (`EtcdWire`) | the KV messages as heap predicates over models, with unfold laws |
| `SpecPlan/Spec/context/Api.lean` (`Context`, new namespace) | any Go context: `ctxOk`, `ctxDone`, `ctxWithValues`, `Err`'s specs |
| `SpecPlan/Spec/go_etcd_io/etcd/client/v3/Api.lean` (`ClientV3`) | the client's vocabulary, the KV contract (`KV.*Triple`), the wire contract (`RemoteKV.*Triple`), the `Txn` contract, slots |
| `SpecPlan/Spec/go_etcd_io/etcd/client/v3/*.lean` | 142 specs (below) |
| `SpecPlan/Spec/go_uber_org/zap/Api.lean` (`Zap`), `SpecPlan/Spec/go_uber_org/zap/*.lean`, `zapcore/CheckedEntry__Write.lean` | the logger's trust boundary: `isLogger`, `entryOk`, 25 specs |
| `examples/specreq/clientv3kv/{put_get,txn,ops,errors,history,stream}.go` | 18 requirement snippets |
| `notes/specs-only/top.md` | the top-level story and the cluster contract (K1–K8) |
| `notes/specs-only/req/*.md` | six `## from W0` sections (below) |

The client specs: `kv.{Put,Get,Delete,Compact,Do,Txn,GetStream}`, `Client.{Put,Get,Delete,Compact,Do,
Txn,GetStream}` (the promoted methods), `txn.{If,Then,Else,Commit}`, `NewKV`, `NewKVFromKVClient`,
`OpResponse.{Put,Get,Del,Txn}`, `{Put,Get,Delete,Txn}Response.OpResponse`, `GetStreamToGetResponse`,
`RangeStreamResponse.Err`; `op.go`: the 24 getters (`Op.IsGet`, ..., `Op.isWrite`,
`Op.IsSortOptionValid`), `Op.{KeyBytes,ValueBytes,RangeBytes,Txn}`, `Op.{WithKeyBytes,WithRangeBytes,
WithValueBytes}`, `Op.{toRangeRequest,toRequestOp,toTxnRequest,applyOpts}`, `NewOp`, `OpGet`,
`OpPut`, `OpDelete`, `OpTxn`, `OpWatch`, `IsOptsWithPrefix`, `IsOptsWithFromKey`, the 23 option
constructors, `WithFirstCreate`...`WithLastRev`, `withTop`, `GetPrefixRangeEnd`, `getPrefix`,
`LeaseOp.applyOpts`, `WithAttachedKeys`, `toLeaseTimeToLiveRequest`; `compare.go`: `Compare`,
`Value`, `Version`, `CreateRevision`, `ModRevision`, `LeaseValue`, `FromCompare`, `cloneCompare`,
`Cmp.{Clone,ensureCompare,GetCompare,KeyBytes,WithRange,WithPrefix}`, `mustInt64`,
`mustInt64orLeaseID`; `compact_op.go`: `OpCompact`, `CompactOp.{applyCompactOpts,toRequest}`,
`WithCompactPhysical`; `ctx.go`: `WithRequireLeader`, `withVersion`; `utils.go`: `jitterUp`;
`retry.go` (KV): `RetryKVClient`, `retryKVClient.{Range,RangeStream,Put,DeleteRange,Txn,Compact}`,
`retryPolicy.String`, `isSafeRetryMutableRPC`, `isSafeRetryImmutableRPC`; `client.go`:
`ContextError`.

## Exported vocabulary

**Model (`EtcdModel`, transparent).** `State` (`kv : KVHist` the whole history and `compacted`;
`leases`, `granted`; `auth : AuthState`; `members`; `alarms`), `State.init`; `Req` (every v3 RPC's
request, protobuf-shaped), `Resp`/`RespBody`/`OpResp`; `Step who rq σ σ' res` (a relation: the
deterministic success and errors per RPC, a refusal of any request, the server's choices, a
serializable read at a member's view `KVHist.IsView`); `RangeReq.answers` (etcd's range semantics,
quirks included), `TxnRun` (a transaction's run: comparisons and checks at the pre-state, reads
after earlier writes, one revision); `State.permits`, `AuthState.admin`; `EnvCfg`, `EnvStep cfg`
(lease expiry, auto-compaction if configured, alarms, publications); `Reach` (closure over every
principal's steps and every environment step); `EtcdErr` (rpctypes' errors), `.indefinite`,
`.refusal`; `Req.isRead`.

**State (`EtcdModel`).** `etcdState γ σ` (exclusive, timeless): the cluster's state.
`etcdLb γ σ` (persistent): the cluster has been in `σ`. Laws: `etcdState_timeless`, `etcdState_excl`,
`etcdLb_persistent`, `etcdLb_timeless`, `etcdState_lb` (snapshot), `etcdLb_reach` (current state
reachable), `etcdLb_ord` (one history), `etcdState_revFits` (revision fits `int64`). `etcdN`.
`envUpd γ cfg` (def): the environment's permission. `servesAt γ ep` (persistent): a member serves
the cluster at `ep`; `servesAt_persistent`. `errVal e`: rpctypes' error value; `errVal_inj`,
`errVal_ty`. `indefErr err` (def): not a definite etcd error.

**Wire (`EtcdWire`).** Models `HeaderM`, `KeyValueM`, `RangeRespM` (optional header),
`PutRespM`, `DeleteRespM`, `ResponseOpM`, `TxnRespM`, `CompactRespM`, relations `RangeRespM.ofAns`,
`ResponseOpM.ofResp`, `TxnRespM.ofResps`. Predicates (opaque, `(p : Loc) (dq : DFrac) model`):
`respHeaderOwn`, `keyValueOwn`, `rangeRespOwn`, `putRespOwn`, `deleteRespOwn`, `responseOpOwn`,
`txnRespOwn`, `compactRespOwn`, `rangeReqOwn`, `putReqOwn`, `deleteReqOwn`, `compareOwn`,
`requestOpOwn`, `txnReqOwn`, `compactReqOwn`, `protoRest`; defs `msgsOwn`, `optOwn`, `responseOneof`,
`requestOneof`, `cmpOneof`. Laws: one `*_unfold` each, `protoRest_zero`, `replyPersist`,
`msgOwn_ne_null`.

**Context (`Context`).** `ctxOk ctx` (persistent: any context), `ctxDone ctx`, `ctxWithValues ctx
ctx'`; laws `ctxOk_persistent`, `ctxDone_persistent`, `ctxOk_ne_nil`, `ctxWithValues_persistent`,
`ctxWithValues_done`, `ctxOk_of_isContext`, `ctxOk_background`; specs `Err`, `ErrDone`, `TODO`,
`Background`.

**Client (`ClientV3`).** Pure: `OpM` (the `Op`, field by field), `OpM.zero`, the option models
`with*M`, `withTopM`, `applyOptsM`, `opGetM`/`opPutM`/`opDeleteM`/`opWatchM`/`opTxnM`, panic
conditions `prefixAndFromKey`, `putPanics`, `deletePanics`, `watchPanics`, the requests
`rangeReq`/`putReq`/`deleteReq`/`toReqOp`/`toReq`, `isWrite`, `prefixEnd`, `CmpArg`, `compareM`,
`cmpOfTarget`, `TxnSt`, `CompactOpM`, `CallErr`, `streamMatches`. Resources: `connOk`, `callOptsOk`,
`clientConnOk` (slots, 1c); `watcherAt` (1b), `leaseAt`, `authAt`, `clusterAt`, `maintAt` (1c slots);
`kvAt` (the KV bundle), `kvHandle`, `remoteKVAt` (the wire bundle), `retryKVHandle`, `isClient`,
`clientMut`, `clientMutRest`, `txnAt`, `opAt`, `cmpAt`, `optAt`, `compactOptAt`, `leaseOptAt`,
`callErr` (slot, 2a), `streamAt`, `wireStreamAt` (slot, 2a), `ctxRequireLeader` (slot); defs
`indefCall`, `opsAt`, `cmpsAt`, `optsAt`, `compactOptsAt`, `leaseOptsAt`, the replies
`getReply`/`putReply`/`deleteReply`/`txnReply`/`compactReply`/`doReply`/`wireReply`/`wireIndef`.
The contracts, once each: `KV.{Put,Get,Delete,Compact,Do,GetStream,Txn}Triple`,
`Txn.{If,Then,Else,Commit}Triple`, `RemoteKV.{Range,RangeStream,Put,DeleteRange,Txn,Compact}Triple`.
Laws: `opAt_unfold`, `cmpAt_unfold`, `optAt_call`, `optAt_type`, `compactOptAt_call`,
`leaseOptAt_call`, `handles_persistent`, `isClient_conn`, `isClient_KV`, `isClient_fields`,
`clientMut_KV`, `clientMut_conn`, `clientMut_freeze`, `kvAt_methods`, `kvHandle_kvAt`,
`txnAt_methods`, `remoteKVAt_methods`, `retryKVHandle_remoteKVAt`, `streamAt_recv`,
`wireStreamAt_recv`, `indefCall_pure`, `callErr_ctxErr`, `callErr_errVal`, `init.spec`.

**Zap (`Zap`).** `isLogger l` (persistent), `entryOk ce` (exclusive); `isLogger_persistent`,
`isLogger_ne_null`.

## Main changes from the old specs

* **One client-owned state for everything a client sees** (`etcdState`, over the model's `State`),
  replacing the server's `etcdKV`, the KV log certificates (`kvRevLb`, `kmLog`), the client's
  members (`isKv api γ dup`, `SrvAt`) and the per-feature models. Leases, auth, membership, alarms,
  compaction and the whole KV history are in the state; a mode is part of the state (auth on/off,
  leases), never a second spec.
* **Relaxed premises**: leases on puts (was lease `0`), auth on (the handle's principal `who`; was
  off), compaction (was a revision-reached certificate on `Compact`; now `ErrFutureRev` is a
  linearized answer), nested transactions in `Then`/`Else` and `Do`, keys-only and sorted reads
  (the model has etcd's quirks), no payload bound (`opSizeOk`), no `dup` flag, no `kvRoom`.
* **Errors**: a definite error is a linearized answer (`Q` given with it); only an indefinite
  error (`indefCall`) gives nothing. Old: `kvErr` (any error, no information).
* **Reads** take a persistent update; serializable reads and read-only serializable transactions
  are the same specs, answered at a member's view.
* **`GetStream`** (new: Kubernetes now lists with it), over Perennial's SPSC channel idiom.
* **The context** is any context (`Context.ctxOk`), not Perennial's `isContext` (which excludes
  `Background()`).

## Left out

`Cmp.WithKeyBytes`, `Cmp.ValueBytes`, `Cmp.WithValueBytes` (no old spec; only the `namespace`
package uses them; `Cmp.WithValueBytes` panics unless the comparison is a value one); the
non-KV parts of `retry.go` (`RetryLeaseClient`, `RetryClusterClient`, `RetryMaintenanceClient`,
`RetryAuthClient` and their methods: 1c's, as the batch row says); `client.go` other than
`ContextError` (1c). `sort.go` has only types.

## Decisions the user should see

1. **The environment's permission** (`envUpd γ cfg`, `State.lean`): lease expiry, auto-compaction,
   alarms and member publications change `etcdState` through a persistent atomic update the
   program hands to the cluster when it starts it. Alternative: a client invariant every client
   spec names; rejected, it puts the environment into every client spec. A program that grants no
   lease and runs no auto-compactor (`cfg.autoCompact = false`) sees only alarms and publications.
2. **Time is not modelled**: a lease may expire (be revoked by the environment) at any time, and a
   keep-alive or `TimeToLive` guarantees nothing about liveness (a deposed leader answers them).
   So `concurrency.Mutex`'s mutual exclusion is about revisions (fencing), not time (`top.md` §2).
3. **A write's update is exclusive, a read's persistent** (`Req.isRead`). The exclusive one needs
   the cluster to apply each call at most once (`req/`: one proposal, no resend by grpc, the
   interceptor resending only never-sent attempts or token refusals that fired nothing).
4. **The step is a relation with refusals** (`EtcdErr.refusal`: any request may be refused with
   no change). Linearization of failures is thus exact (a definite error is a step), at the price
   that the specs never promise success (as no distributed system's can).
5. **Kept the whole KV history** in the state (compaction only sets the floor), so that a stale
   member's answer, a read at a past revision and a watch's events need no second notion of past.
6. **The messages' predicates are the anchor's** (`Wire.lean`), shared by client and server; 3h
   realizes them (its `req/`).
7. **The revision bound is a law** (`etcdState_revFits`), owned by the cluster's invariant.

## Open questions for the user

1. **`Compact(0)`**: kept as a client premise (`rev ≠ 0`, `issues/etcd-restore-scheduled-compact-zero.md`);
   with it the model's compaction is "`compacted < r ≤ rev`". Alternative: model a first
   `Compact(0)` as a successful no-op and accept the crash-restart divergence as a model violation
   (no premise, a false spec in that corner). The premise is a scope restriction on the client API.
2. **The model's lease, auth and membership steps** are W0's reading of the server's code (they
   are what 1c's specs will state); 3c, 3d, 2e should check them and report mismatches. In
   particular: who may call `UserGet`/`RoleGet` for themselves, `MemberAdd`'s learner limit
   (`tooManyLearners` modelled as a refusal-like answer), and whether `Compact` needs an
   administrator (the code: no).
3. **Streamed ranges** (`GetStream`): the model says only what a stream at the default ordering
   returns (its pages are the range's answer); a sorted or filtered stream's contents and every
   stream's counts are left open (`issues/etcd-rangestream-sort-none.md`). Enough for Kubernetes
   (it streams in key order); say if a stronger stream model is wanted.
4. **The size of requests**: no client premise; the gRPC boundary must fail (not panic) on an
   oversized message (`req/google_golang_org_grpc.md` item 3). If 2a cannot state its boundary so,
   the client's specs would regain a payload premise: a decision for the user then.

## `req/` sections written (`## from W0`)

`google_golang_org_grpc.md` (the boundary under `remoteKVAt`: one run per attempt, no resend,
error kinds, any size, contexts, streams, metadata);
`go_etcd_io_etcd_server_v3_etcdserver_api_v3rpc.md` (the handlers: every answer a `Step`, the
firing discipline, configuration scope, streamed ranges);
`go_etcd_io_etcd_api_v3_v3rpc_rpctypes.md` (the error variables hold `errVal`, `Error` over
`callErr`); `go_etcd_io_etcd_api_v3_etcdserverpb.md` (realize `Wire.lean`, the getters, the enum
maps, the stub, `proto.Clone`/`Merge`); `go_etcd_io_etcd_client_v3.md` (1b, 1c: `New`, the slots,
the interceptor's discipline, `callOptsOk`); `go_etcd_io_etcd_server_v3_etcdserver.md` (2c, 2d,
2e: the cluster contract K1–K8).

## Round 1 repairs (2026-11-09)

Reviews: `reviews/W0-provability-1.md` (P), `reviews/W0-completeness-1.md` (C). Every first-tier
finding is fixed; second-tier ones done where cheap (listed).

**Renamed or changed names (wave-1 batches: follow these).**

| name | change |
|---|---|
| `EtcdModel.OpResp.range` | **arity**: `range (rev : Nat) (a : RangeAns)` (was `range (a)`): a nested range's header revision (C-F3) |
| `EtcdWire.ResponseOpM.ofResp.range` | takes the revision; requires `m.hdr.map (·.revision) = some (W64 rev)` |
| `EtcdModel.EnvCfg` | new field `leaseExpiry : Bool` (C-F6); `EnvCfg.all` sets both; `EnvStep.leaseExpire` needs it |
| `EtcdModel.EtcdErr` | new constructors `canceled`, `deadlineExceeded`, `notSupportedForLearner`, `invalidClientAPIVersion`, `watchCanceled`, `permissionNotGiven` (P-S1) |
| `EtcdErr.refusal` | adds `authFailed` (P-F1, C-F5), `notSupportedForLearner`, `invalidClientAPIVersion` |
| `EtcdErr.indefinite` | adds `canceled`, `deadlineExceeded`, `watchCanceled` |
| `EtcdModel.State.permits` | same signature; a principal is needed only where a pair or an attached key is checked (P-F3.1) |
| `EtcdModel.RangeReq.txnRevErr` | **new**: `checkRange` inside a txn (P-F3.3); `TxnRun.rangeErr`/`range` use it |
| `EtcdModel.AuthState.mayCall` | **new**: admin, or self `UserGet`/own-role `RoleGet` (P-F3.7) |
| `EtcdModel.etcdState_sizeFits` (State.lean) | **new law** (P-F4) |
| every `KV.*Triple`, `RemoteKV.*Triple` | **new premise** `ctxPrin ctx who` beside `Context.ctxOk ctx` (C-F4) |
| `ClientV3.ctxPrin` | **new** (persistent), laws `ctxPrin_persistent`, `ctxPrin_of_isContext`, `ctxPrin_background`, `ctxPrin_todo`, `ctxPrin_child`; `WithRequireLeader.spec`/`withVersion.spec` posts keep it |
| `Txn.{If,Then,Else}Triple` | post `txnAt r ...` for the returned `r` (was `⌜r = iv⌝ ∗ txnAt iv ...`) (C-F7) |
| `ClientV3.streamMatches` | stronger: non-last chunks have no header, `More` false, `Count` 0, key-values; last `Count = W64 a.count` (C-F2) |
| `streamAt_recv`, `wireStreamAt_recv` | new terminal disjunct: `ErrCompacted` after a chunk, no `Q` (P-F2, C-F1) |
| `ClientV3.callErr_agree`, `errorsIs_errVal` | **new laws** (P-S7, P-S6) |
| `Context.ctxChild`, `cancelOk`, `WithCancel.spec`, `WithTimeout.spec`, `WithValue.spec`, `ctxDoneChan`, `Done.spec`, `doneRecv.spec` | **new** (P-F5; R1's `req/context.md`) |

Nothing was removed.

**Model fixes (P-F3).** Empty permission checks need no principal; serializable read-only txns
checked at a stale auth state; negative revisions in a txn (`txnRevErr`); an empty `RequestOp` is
`ErrKeyNotFound` (txn refusal); `AuthEnable` keeps the auth revision; role, permission, member and
alarm lists answered as permutations; self `UserGet`/own-role `RoleGet`; `RoleGet "root"` any
permissions; `RoleGrantPermission`'s `invalidAuthMgmt`/`permissionNotGiven`; a password-less user
stays password-less; `TimeToLive`'s remaining TTL unbounded by the granted one; permission errors on
`Leases` and `TimeToLive(keys)`; `Leases` without duplicates; `MemberAdd`'s `memberBadURLs`,
`memberExist`, `memberNotFound`; member and alarm admin checks at a stale local state (refusal at
any state, success not conditioned on `σ`'s administrators).

**Snippets.** `ReqListPrefix` (now provable with `etcdState_sizeFits`; also `More` ⇒ non-empty page,
C-S3 P5), `ReqCtxErrors` (`Context.WithCancel.spec`), new `ReqTxnNestedRangeHeaders` (C-F3),
`ReqGetStream` (first non-nil header, final `Count`, C-F2), new `ReqGetStreamCompacted` (C-F1),
new `ReqAuthRefusal` (C-F4). The package comment states the `ctxPrin` assumption.

**Second tier done.** P-S1 (the gRPC-only rpctypes errors, `.other` reworded), P-S2/the learner
resend (Api header, 1c's req item 2), P-S3 (reads answer with the firing at the state read: Api
header, `top.md`, v3rpc req item 3), P-S5 (K8 names the long-name crash as liveness), P-S6,
P-S7, P-S8 (the step budget in K7 and `State.lean`), C-S1 (leasing removed from `kvAt`'s
realizers; `req/go_etcd_io_etcd_client_v3_leasing.md`), C-S2 (the GetStream margin), C-S4 (`WithValue`,
`ctxOk_todo` fixed; `Client.Ctx()` in 1c's req). Not done: C-S3's other snippets (P14, P23, two
clients), C-S5 (more zap: `Named`, `Sugar`, `Time`, `Float64`, `Binary`), C-S6, C-S7, C-S8.

**Go findings recorded.** `nonissues/etcd-client-getstream-abandoned-leak.md` (blocks-proof: no),
`nonissues/etcd-doserialize-auth-enable-race.md` (blocks-proof: yes; K8 open question).

**New open questions for the user.**
5. **`doSerialize`'s race with `AuthEnable`** (`nonissues/etcd-doserialize-auth-enable-race.md`):
   a fix on the fork, or a scope premise "no `AuthEnable` while reads are in flight".
6. **Lease reads per member** (C-F6): `examples/etcd/{leasegrant,leaseexpiry,leasecatchup}` need
   `Leases` to answer the live leases of a state the cluster has been in, with a lower bound for a
   client of one member. The model keeps no lease history and no per-member views, so `Leases`
   only says "granted ids, no duplicates". Options: per-member views with a monotone lower bound a
   client carries (a model change: `State` gains the leases' history, `Step` takes the answering
   member), or a single-member mode. Your decision; `EnvCfg.leaseExpiry` (added) covers the
   "no lease expires during the run" premise.
7. **Contexts a caller builds with its own metadata** (`ctxPrin`): Kubernetes' request contexts
   (`WithValue` chains) need `ctxPrin` from their batch: `Context.WithValue.spec` gives no
   `ctxChild` because a value may be grpc's outgoing metadata.

## Round 2 repairs (2026-11-09)

Review: `reviews/W0-round2.md` (F1–F7, S1–S8), the coordinator's cross-batch requests (`req/
go_etcd_io_etcd_api_v3.md`: 1b, 1d, 1f, 1g) and 1f's review (duplicate keys). Every first-tier
finding is fixed.

**Changed or new names (wave 1: follow these).**

| name | change |
|---|---|
| `streamAt_recv`, `wireStreamAt_recv` | the `ErrCompacted` disjunct no longer requires `ms ≠ []` (F1: before any chunk too) |
| `KV.GetStreamTriple`, `RemoteKV.RangeStreamTriple` | an open error is `indefCall err` **or a refusal** (`∃ e, e.refusal ∧ err = errVal e`, resp. `callErr err (.etcd e)`) (F2); **new premise** `0 ≤ revision` (F7) |
| `Context.ctxChild_done` | **removed** (false: F3) |
| `Context.WithValue.spec` | **new premise**: the key non-nil (its binder is now `ki : GoInterfaceOk`) and of a comparable type (F4); post adds `ctxValueAt parent ctx key` |
| `Context.ctxValueAt`, `Context.ctxNoMeta` (transparent: `Value(mdOutgoingKey{})` is nil, dischargeable by a root context's owner), `ctxNoMeta_background`, `ctxNoMeta_child`, `ctxNoMeta_value` | **new** (F6) |
| `ClientV3.ctxPrin_of_isContext` | **removed** (false: F5) |
| `ClientV3.ctxPrin_of_noMeta`, `ctxPrin_value` | **new** (F6): Kubernetes' contexts get `ctxPrin` from `ctxNoMeta` at their root and `WithValue` at non-metadata keys |
| `ClientV3.callErr_errorsNew` | **new law** (1d's request): of the `*errors.errorString` errors, a call returns only `context.Canceled`'s, so a package's own `errors.New` sentinel is never a call's error |
| `EtcdModel.etcdState_revFits` | **strengthened**: `σ.kv.rev + 1 < 2 ^ 63` (1f) |
| `EtcdModel.etcdLb_revFits` | **new law** (1b): the same for any state an `etcdLb` names |
| `EtcdModel.etcdLb_init` | **new law** (1d, 1f): `etcdLb γ σ ⊢ ⌜∃ ms, Reach (State.init ms) σ⌝` |
| `EtcdModel.etcdPerm γ T`, `EtcdModel.etcdPeek γ` | **new** (State.lean; 1d, 1f, 1g): 1d's `etcdPerm` body (a persistent update performing any `T`, committing `etcdLb` of both states), and `etcdPeek γ := etcdPerm γ (σ' = σ)`; 1d's `Concurrency.etcdPerm`, 1f's `etcdPeek`/`dbPerm`, 1g's `Cache.etcdPeek` can be replaced by them |
| `EtcdModel.putOnce` | **new**, and a conjunct of `kvStep .txn`'s success (1f): the gRPC layer's duplicate-key check refuses a transaction that puts a key twice on a path; the events may still delete a key put earlier (sibling put-then-delete, `issues/etcd-txn-check-intervals-sibling.md`). Cite it as "`kvStep`'s `putOnce evs`" (it is the model's restriction, not a law) |
| `AuthState.mayCall` | `.userGet n` also `who = none ∧ n = []` (S1) |
| `EtcdModel.RequestOp.valid`, `RequestOp.validL`, `TxnReq.valid` | **new** (1e's review): the gRPC layer's validation of every comparison and operation of a transaction (both branches, nested); `kvStep .txn`'s applied branch now requires `t.valid` (an invalid one is only refused: `ErrEmptyKey`, `ErrValueProvided`, `ErrLeaseProvided`, `ErrInvalidSortOption`, `ErrKeyNotFound`). Cite as "`kvStep`'s `t.valid`" |
| `EtcdModel.etcdLb_keyNonEmpty` | **new law** (1g): no event or stored key of any state an `etcdLb` names is the empty key (true of `Step`: puts are validated, deletes and revocations remove stored keys) |
| `ClientV3.clientRest` | **new** (persistent; 1d, 1e): everything of a client but its `KV` field; laws `clientMut_split`, `clientRest_persistent`, `isClient_rest`, `clientRest_conn`, `clientRest_fields`; the proxy that overwrites `client.KV` with a leasing KV keeps the field and `clientRest` (`req/go_etcd_io_etcd_client_v3.md`, "from W0 (round 2)") |

**Other fixes.** `ReqAuthRefusal`'s Assumes (not root, `pfx < end`, a half-open range, `outside`
outside it); `ReqGetStream` assumes `rev ≥ 0`; `ReqGetStreamCompacted`'s comment (S6). The
`doSerialize` nonissue's fix (re-check the permission after the read; the auth revision does not
move at `AuthEnable`) (S4); the leak nonissue's window (three chunks) and the `streamAt_recv`
docstring (S5); new `nonissues/etcd-rangestream-negative-revision-unpinned.md` (F7);
`streamMatches`' wording (S7); the lease reads' permission errors documented (S8); K2 says
`EnvCfg.leaseExpiry = false` is a trusted deployment premise (S3); the stream interceptor's open
error in 1c's req item 2; `ctxNoMeta` in the grpc req.

**Not done.** S2 (`ctxOk`'s intended realization should list `Deadline`, the `&cancelCtxKey` value
and `AfterFunc`: a realization note, no statement changes); 1b's `EnvCfg` compaction retention
(a model question for the user: the compactor's retention is time- or revision-based); moving 1b's
watch messages into `Wire.lean` (1b's files would only change their import: left to the
coordinator to schedule).

## Round 3 repairs (2026-11-09)

The coordinator's two changes: per-member lease reads (open question 6, now in scope: the lease
examples were verified at `037bf21c75`) and the principal per call.

| name | change |
|---|---|
| `EtcdModel.State` | **new field** `leaseHist : List (Int → Option LeaseRec)` (the lease tables before the current one; `State.init` empty; every grant and revocation, client's or the environment's, appends the old table) |
| `EtcdModel.State.leaseTables`, `State.leaseAnsAt σ i rq res` | **new**: every lease table, the current last; a lease read answered from table `i` |
| `leaseStep .leaseLeases` | now `∃ i ids, σ.leaseAnsAt i .leaseLeases res ∧ ...` (was: any granted ids) |
| `leaseStep .leaseTimeToLive` | the answer (found, or `ErrLeaseNotFound`) is `leaseAnsAt` of some table `i`; the permission error unchanged |
| `EtcdModel.leaseViewLb γ ep i` (State.lean) | **new** (persistent): the member serving `ep` has reached lease table `i` and answers its lease reads from tables `≥ i`; laws `leaseViewLb_persistent`, `leaseViewLb_le`. 1c's lease specs produce and consume it (a grant through `ep` gives the table after it; a read through `ep` holding `leaseViewLb γ ep i` answers at a table `≥ i` and gives its own) |
| `EtcdModel.tokenUser γ tok u` (State.lean) | **new** (persistent): the cluster issued `tok` to `u` (`Authenticate`'s answer: 1c, 3d) |
| `ClientV3.ctxPrin` | **arity**: `ctxPrin dflt ctx p` (was `ctxPrin ctx who`): a request sent with `ctx` by a client whose credentials name `dflt` is authenticated as `p` |
| every `KV.*Triple`, `RemoteKV.*Triple` | **new binder** `(p : Principal)` per call; premise `ctxPrin who ctx p` (`who` is now the client's default principal); the update's step is `Step p ...` (was `Step who`) |
| `KV.TxnTriple`, `KV.GetStreamTriple`, `RemoteKV.RangeStreamTriple` | their results are `txnAt iv γ p ctx _`, `streamAt ch γ p ...`, `wireStreamAt sc γ p ...` (the call's principal) |
| `isClient c γ who`, `clientMut`, `kvAt v γ who`, `clientConnOk`, `connOk`, ... | **same arity**; `who` now means the client's default principal (its credentials), not the principal of every call |
| `ClientV3.ctxTokenMd ctx tok` | **new** (slot 2a): `ctx` carries outgoing metadata `token: tok` |
| `ctxPrin_token`, `ctxPrin_tokenSame` | **new laws**: a forwarded token's user for a client without credentials (the proxy, `v3client`); a token of the client's own user |
| `ctxPrin_of_noMeta`, `ctxPrin_background`, `ctxPrin_todo` | now give `ctxPrin dflt ctx dflt` (the client's own principal) |
| `ctxPrin_child`, `ctxPrin_value`, `WithRequireLeader.spec`, `withVersion.spec` | carry `ctxPrin dflt ctx p` for every `dflt`, `p` |

What the lease examples need, from these: `leasegrant` (one member: the grant through `ep` gives
`leaseViewLb` of the table after it; `Leases` through `ep` answers at a later table, which still has
the lease: no revocation, `EnvCfg.leaseExpiry = false`); `leaseexpiry` (`TimeToLive` answers
`ErrLeaseNotFound` at table `i`, so `leaseViewLb γ ep i`; `Leases` answers at `j ≥ i`; once revoked
a lease is not live in any later table unless its id is granted again, which the example's
workload excludes); `leasecatchup` (member 3's listing of the last filler is at a table after the
filler's grant, which is after the lease's grant through member 3, and nothing revokes). 1c states
the per-endpoint guarantees in its lease specs.

**Round 3, second part** (1c's provability review F7, F8, S3):

| name | change |
|---|---|
| `leaseStep .leaseGrant` | the granted id is an int64 (positive when the server chooses it), the granted TTL `0 < ttl' ≤ maxLeaseTTL` |
| `leaseStep .leaseKeepAlive`, `.leaseTimeToLive` | the reported TTLs are int64s; a known lease's granted TTL is positive (`v3_server.go`, `LeaseTimeToLive`) |
| `clusterStep .memberAdd` | the new member's id is a uint64 (`< 2 ^ 64`) |
| `EnvStep.alarm` | **new premise**: the alarm's member id `< 2 ^ 64` |
| `notes/specs-only/top.md` §1, K4 | a KV write is fired at most once; the repeatable lease and alarm writes (`LeaseGrant`, `LeaseRevoke`, `Alarm`) may apply more than once and take persistent updates (1c) |

The initial members' ids (`State.init ms`) are uint64s by the cluster contract (K1: they come from
the configuration).

## Round 4 repairs (2026-11-09)

The coordinator's decision (the `doSerialize`/`AuthEnable` race in the model, no premise) and 2a/2c's
reviews (keep-alive and `Compact` permission errors; 2c's F1, F7).

| name | change |
|---|---|
| `EtcdModel.State` | **new field** `authHist : List AuthState` (earlier auth states; every auth change, `AuthEnable` included, appends the old one); `State.init` empty |
| `EtcdModel.State.authTables` | **new**: every auth state, the current last |
| `EtcdModel.State.authOffSince σ lo`, `State.deniedSince σ lo who ps` | **new**: some auth state from index `lo` on had auth off; denied the pairs |
| `EtcdModel.Step`, `kvStep` | **new optional last argument** `(lo : Nat := 0)`, the auth state's index at the call's start; existing uses `Step who rq σ σ' res` keep meaning "any `lo`" (`0`, the weakest). A linearizable `Range` or read-only `Txn` succeeds if permitted at `σ` **or** `σ.authOffSince lo` (the race: its check saw auth off), and may be denied when `σ.deniedSince lo` (the check's state). Exactly etcd's outcomes: with auth on at the check the auth revision is re-checked after the read (`ErrAuthOldRevision`, a refusal), so success then needs the permission at the answer's auth state |
| `EtcdModel.authLb γ lo` (State.lean, def) | **new**: `lo = 0`, or an `etcdLb` of a state whose auth history has an index `lo` |
| `KV.GetTriple`, `KV.DoTriple`, `KV.GetStreamTriple`, `Txn.CommitTriple`, `RemoteKV.{Range,RangeStream,Txn}Triple` | **new binder** `(lo : Nat)`, **new premise** `authLb γ lo`; the update's step is `Step p rq σ σ' res lo` |
| `kvStep .compact` | may be refused for a non-administrator at any auth state the cluster has had (`kvServer.Compact`'s local check); success not conditioned on `σ`'s administrators |
| `leaseStep .leaseKeepAlive` | may answer `permErr who` (`checkLeaseRenew`) |
| `EtcdModel.RespBody.authenticate` | **arity**: no argument (was `authenticate (token)`); the token is given by `tokenUser γ tok u` (2c's F1). `ErrAuthNotEnabled`, `ErrAuthFailed` were already definite answers of `authStep .authenticate` |
| `ClientV3.ctxPrin` (doc) | `p` is the principal the server uses with auth on (token, else certificate CN); with auth off no step depends on the principal, so the certificate's name `AuthInfoFromTLS` gives then is covered (2c's F7); no statement change |
| `nonissues/etcd-doserialize-auth-enable-race.md` | `blocks-proof: no`: the model covers it |

## Round 5 repairs (2026-11-09)

The coordinator's decision (`ErrNoSpace` indefinite), the requests after round 4 in
`req/go_etcd_io_etcd_api_v3.md` and `req/context.md` (2c, 2e, 3a, 3b, 3c, 3d, 2d), and 3b's review F1.

| name | change |
|---|---|
| `EtcdErr.indefinite` | `.noSpace` is indefinite (still a refusal too): an over-quota member applies a write and answers `ErrNoSpace` (`nonissues/etcd-apply-quota-nospace-after-write.md`); `callErr`'s classification follows (`CallErr.indefinite (.etcd .noSpace)`) |
| `EtcdModel.pwHash`, `EtcdModel.pwMatch` | **new** (opaque, trusted; 3a, 3d): `UserRec.password` is the stored credential; `userAdd`/`userChangePassword` store some `cred` with `pwHash pw cred`; `authenticate` succeeds iff the stored credential `pwMatch`es (not "is the password"); law `pwHash_match.spec` (State.lean) |
| `authStep` | **new optional last argument** `(lo : Nat := 0)` (`Step` passes its `lo`): `Authenticate`'s `CheckPassword` answers (`ErrAuthNotEnabled`, `ErrAuthFailed`) at an auth state since `lo` (2c's item 2) |
| `authStep .roleGet` | `"root"` answers `ErrRoleNotFound` when no root role is stored; a stored one any permissions (3d's item 6) |
| `authStep .roleGrantPermission` | success only for a valid range (`KeyRange.validPerm`, new) (3d's item 3) |
| `KeyRange.validPerm`, `KeyRange.inverted`, `State.invertedDeny` | **new**: a range, read, delete or transaction naming an inverted range may be denied with auth on for a non-root principal (3d's item 4) |
| `kvStep .compact` | success only for an administrator at an auth state since `lo` (2a); `KV.CompactTriple`, `RemoteKV.CompactTriple` gain the binder `(lo : Nat)` and the premise `authLb γ lo` |
| `leaseStep .leaseTimeToLive` | the keys are attached at revision `r` or `r + 1` (a lessor's set half updated by an entry or half restored: 3c's items, 2c's item 4); no longer "exactly those of `r`" |
| `EtcdModel.AlarmKind.other`, `Req.alarmActivate` | **new**: a client's `Alarm(ACTIVATE)` (any type, unknown ones as `other n`), admin-refusable at a local auth state (2e's item 5) |
| `EtcdModel.EnvCfg` | **new field** `compactLag : Nat`; `EnvStep.compact` requires `r + cfg.compactLag ≤ σ.kv.rev` (2e's F6); `EnvCfg.all` has `0` |
| `EtcdModel.tokenUser_agree`, `etcdLb_noEmptyUser` | **new laws** (3d, 3a); `tokenUser`'s meaning includes a member's own root tokens and JWTs |
| `Context.TODO.spec` | post adds `□ (ctxDone ctx -∗ False)`; **new law** `ctxDone_background` (3b) |
| `EtcdWire.endOf es bs` | **new**: a range end as mvcc reads the slice (`nil`: one key; non-`nil` empty: from the key on, `"\x00"`; else itself). `rangeReqOwn_unfold`, `deleteReqOwn_unfold`, `compareOwn_unfold` now say `r.rangeEnd = endOf es ebs` (3b's review F1: `WithRange("")` through the in-process adapter) |
| `ClientV3.OpM.endReq` | **new**: the request end of an `Op` (`some []` is `"\x00"`); `OpM.rangeReq`, `OpM.deleteReq` use it; `opAt_unfold`'s `some e` adds `op.end' ≠ slice.nil`; `Cmp.WithRange.spec` gives `"\x00"` for an empty end |
| `ClientV3.ctxPrin` (doc) | the token-and-certificate case: covered when the client's certificate, if any, names its own principal (a scope premise of `connOk`, 1c: one identity per client); otherwise `nonissues/etcd-write-tls-principal-auth-enable.md` (2c's item 3, 3d's item 5) |
| `top.md` K6 | crash restarts under the adequacy's crash rule and `crashScope` (2e) |

**Declined, with the reason.**
- **3b's "an empty range end is `nil`" in the request predicates**: superseded by 3b's review F1
  (`endOf`): a non-`nil` empty end is a real input (in-process adapter), so the predicates say how
  mvcc reads it rather than excluding it.
- **2d's `Cluster` as a structure carrying the raft names and the configuration**: `Cluster` is the
  client API's ghost name; making it hold raft's names would put raft's vocabulary into every
  client spec (PRINCIPLES: the spec of an API, not of an implementation; coupling). The bridge
  `isServer_names` (2c/2d/2e) stays where the server needs it.
- **3c's per-member granted TTLs**: no change: `leaseTimeToLive` already allows any positive granted
  TTL; no client needs a member's own.
- **3a's item 4 (members' TTLs alike)**: the same; a user decision if wanted (`batch-3a.md`).
- **2e's adequacy resources** (`dataDirFresh`, `addrFree`, `backendEnvOk`) and the join by peer-URL
  rights: 2e's vocabulary, stated in its specs; K1/K2 in `top.md` refer to 2e for them.

## Round 6 repairs (2026-11-09)

3d's review F4: an auth change bumps the auth revision before its batch is published to readers,
so `doSerialize`'s post-read check passes and a read is checked against the old auth state.

| name | change |
|---|---|
| `EtcdModel.State.permittedSince σ lo who ps` | **new**: the read is permitted at some auth state from index `lo` on (subsumes `authOffSince`) |
| `kvStep .range`, `.txn` (read-only) | a linearizable read succeeds if permitted at `σ`, or `σ.permittedSince lo` (was `σ.authOffSince lo`); denials unchanged (`deniedSince`) |
| `EtcdModel.State.authOffSince` | kept (no longer used by `kvStep`); it implies `permittedSince` |

What it admits: a read whose check saw an auth state since its start (auth off there, or the user
permitted there before a change not yet visible to readers) and whose data is the linearization
state's. Margin: it also admits a read permitted only at a state whose change was already visible
to the reader (etcd then answers `ErrAuthOldRevision`, a refusal); the model does not record which
auth changes a member's readers saw.
