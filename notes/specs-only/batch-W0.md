# Batch W0 (the anchor): report

Author's report: the files, the exported vocabulary, the changes from the old specs, what was left
out, the decisions the user should see, the open questions, the `req/` sections. Everything below
builds (`etc/specs-build.sh --dir Spec/go_etcd_io/etcd/api/v3 Spec/context
Spec/go_etcd_io/etcd/client/v3 Spec/go_uber_org/zap Spec/go_uber_org/zap/zapcore`: 173 modules);
the snippets vet (`cd examples && go vet ./specreq/clientv3kv/`).

## Files

| path | what |
|---|---|
| `Spec/go_etcd_io/etcd/api/v3/Model.lean` (`EtcdModel`) | the pure model: `State`, `Req`, `Resp`, `Step`, `EnvCfg`, `EnvStep`, `Reach`, `EtcdErr` |
| `Spec/go_etcd_io/etcd/api/v3/State.lean` (`EtcdModel`) | the resources: `Cluster`, `etcdState`, `etcdLb`, `etcdN`, `envUpd`, `servesAt`, `errVal`, `indefErr` |
| `Spec/go_etcd_io/etcd/api/v3/Wire.lean` (`EtcdWire`) | the KV messages as heap predicates over models, with unfold laws |
| `Spec/context/Api.lean` (`Context`, new namespace) | any Go context: `ctxOk`, `ctxDone`, `ctxWithValues`, `Err`'s specs |
| `Spec/go_etcd_io/etcd/client/v3/Api.lean` (`ClientV3`) | the client's vocabulary, the KV contract (`KV.*Triple`), the wire contract (`RemoteKV.*Triple`), the `Txn` contract, slots |
| `Spec/go_etcd_io/etcd/client/v3/*.lean` | 142 specs (below) |
| `Spec/go_uber_org/zap/Api.lean` (`Zap`), `Spec/go_uber_org/zap/*.lean`, `zapcore/CheckedEntry__Write.lean` | the logger's trust boundary: `isLogger`, `entryOk`, 25 specs |
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
