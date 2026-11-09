# Batch 2a: etcd's gRPC handlers, rpctypes, and the grpc / protobuf boundary (draft, before review)

All files build (`etc/specs-build.sh`, 153 modules, 2026-11-09). The generators I used are in
`.lake/g2a/` (not committed).

## Files

- **protobuf's `proto`**, `Spec/google_golang_org/protobuf/proto/` (namespace `Proto`, assumed):
  `Api.lean`, `Size`, `Marshal`, `Unmarshal`, `Clone`, `Equal`, `Merge`.
- **grpc**, `Spec/google_golang_org/grpc/` (namespace `Grpc`, assumed):
  - `Api.lean`;
  - the client: `NewClient`, `ClientConn__Invoke`, `ClientConn__NewStream`, `ClientConn__Close`;
  - the dial options: `WithUnaryInterceptor`, `WithStreamInterceptor`, `WithResolvers`,
    `WithPerRPCCredentials`, `WithTransportCredentials`;
  - the call options: `WaitForReady`, `MaxCallSendMsgSize`, `MaxCallRecvMsgSize`;
  - the server: `NewServer`, `Server__RegisterService`, `Server__Serve`, `Server__Stop`,
    `Server__GracefulStop`;
  - the server options: `ChainUnaryInterceptor`, `ChainStreamInterceptor`, `CustomCodec`, `Creds`,
    `MaxRecvMsgSize`, `MaxSendMsgSize`, `MaxConcurrentStreams`, `StatsHandler`;
  - `status/`: `FromError`, `Status__Code`, `Status__Message`, `Error`, `Errorf`;
  - `metadata/`: `FromIncomingContext`, `FromOutgoingContext`, `NewOutgoingContext`,
    `AppendToOutgoingContext`, `Pairs`, `MD__Get`, `MD__Copy`, `MD__Set`;
  - `peer/FromContext`;
  - `health/`: `NewServer`, `Server__SetServingStatus`.
  - The streams' `SendMsg`/`RecvMsg`/`CloseSend`/`Context` are laws of `Api.lean` (interface
    methods: `cliSend_send`, `cliSend_closeSend`, `cliRecv_recv`, `srvRecv_recv`, `srvSend_send`,
    `srvStream_context`), as are the invoker's and streamer's triples (`attemptOk_call`,
    `streamerOk_call`).
- **rpctypes**, `Spec/go_etcd_io/etcd/api/v3/v3rpc/rpctypes/` (namespace `Rpctypes`): `Api.lean`,
  `Error`, `ErrorDesc`, `EtcdError__Code`, `EtcdError__Error`.
- **v3rpc**, `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/` (namespace `V3rpc`; 2b's watch
  files share the directory): `Api.lean` and 99 specs.
  - The KV handlers: `kvServer__{Range,Put,DeleteRange,Txn,Compact,RangeStream}`,
    `quotaKVServer__{Put,Txn,Range,DeleteRange,Compact}`.
  - The lease handlers: `LeaseServer__{LeaseGrant,LeaseRevoke,LeaseTimeToLive,LeaseLeases,LeaseKeepAlive,
    leaseKeepAlive}`, `quotaLeaseServer__{LeaseGrant,LeaseRevoke,LeaseTimeToLive,LeaseLeases}`.
  - The other services: `AuthServer__*` (17), `ClusterServer__*` (5),
    `maintenanceServer__*` (8) and `authMaintenanceServer__*` (10).
  - The checks: `checkRangeRequest`, `checkRangeStreamRequest`, `checkPutRequest`,
    `checkDeleteRequest`, `checkTxnRequest`, `checkRequestOp`, `checkIntervals`.
  - The errors: `togRPCError`, `isClientCtxErr`, `isRPCSupportedForLearner`.
  - The header: `newHeader`, `header__fill`, `header__fillWithoutRevision`,
    `headerFillingRangeStream__Send`.
  - The guards: `AuthAdmin__{isPermitted,requireAuthInfo}`, `quotaAlarmer__check`,
    `newBackendQuota`.
  - The constructors: `NewKVServer`, `NewQuotaKVServer`, `NewLeaseServer`,
    `NewQuotaLeaseServer`, `NewAuthServer`, `NewClusterServer`, `NewMaintenanceServer`,
    `newHealthNotifier`, `healthNotifier__startServe`, `Server`.
  - The interceptors: `newUnaryInterceptor`, `newLogUnaryInterceptor`, `logUnaryRequestStats`,
    `newStreamInterceptor`, `monitorLeader`, `newCancellableContext`, `cancellableContext__{Cancel,Err}`,
    `getServerMetrics`.
- **Snippets**: `examples/specreq/v3rpc/` (`kv.go`: validation answers, put-then-range,
  compact-admin, lease-ttl-unknown, range-stream; `serve.go`) and `examples/specreq/grpc/grpc.go`
  (at-most-once, status classification, outgoing metadata). Both pass `go vet`.

## Vocabulary

### Proto

- `Content` (opaque type): a message's content, every field and the unknown ones, up to
  `proto.Equal`. It is a value: not keyed by address, not a model a caller builds.
- `msgAt t p dq c`: the `*t` message at `p` holds `c`. Laws: timeless, persistent at `discard`,
  `ne_null`, `agree`, `persist`.
- `encSize`, `depth`, `marshalOk`, `encodes` (with `encodes_fun`), `merge`.
- `depthMax` (`10000`), `marshalMax` (`2 ^ 48`), `Content.fits`.

### Grpc

- The codes. `MD`, with `MD.get`, `MD.set`, `MD.ofPairs`, `lowerKey`, `mdSeen`.
- `Outcome` (a reply's content, or a status). `UnarySpec`, the urpc-style contract of a method.
  `StreamSpec`: `up`, `dn` and `fin`, indexed by message, over the stream's name `StreamName`.
- `grpcMsg`: grpc's own messages. `msgsFit` (opaque `Prop`): the workload premise.
- Errors (persistent): `statusErr`, `sentStatus`, `ownErr`, `errMsg`, `statusAt`, `errView`.
- The client side (persistent): `outMD`, `connAt cc A ui si R`, `dialOptAt`, `callOptOk`,
  `attemptOk`, `streamerOk`, `resolverAt`, `perRPCAt`.
- Address binding:
  - `addrFree ep` is exclusive, one per address, and comes from adequacy.
  - `addrAt ep C` (persistent, agreeing) binds `ep` to the contracts `C : AddrContract`.
  - `serves` and `servesStream` are defined from `addrAt`.
  - `listenerAt` and `serveTok`.
- The server side:
  - `srvBuild gs B` (`SrvCfg`), `srvOptAt`, `serviceDescAt`, `codecOk`, `icChain`, `icHandler`,
    `healthAt`.
  - `rpcCtx ctx md`, the context of a run.
  - `decOk`, the request decoder of a run.
  - `unaryOut`, `unaryOk`, `streamOut`, `streamRun`, `streamOk`: a handler meets its contract.
  - `regsOk B C`: the registrations meet `C`.
- The stream halves (exclusive): `cliSend`, `cliRecv`, `srvRecv`, `srvSend`. `streamKey g`
  (exclusive) is what a protocol uses to allocate its ghost state keyed by `g`.
- `mdAt` (a `metadata.MD` map), `peerOk`.
- Laws:
  - `grpc_persistent`;
  - `ownErr_grpcMsg`, `statusErr_sent`, `ctxErr_sent`, `statusErr_agree`, `errMsg_call`,
    `errMsg_sent`;
  - `rpcCtx_ctxOk`;
  - `decOk_call`, `attemptOk_call`, `streamerOk_call`;
  - the stream laws above;
  - `outMD_noMeta`, `outMD_ctxOk`, `outMD_agree`, `outMD_child`, `outMD_value`, `mdAt_persist`,
    `mdAt_discard_persistent`;
  - `addrFree_bind`, `addrAt_persistent`, `addrAt_agree`;
  - `start` (a ghost step: registrations meeting `C`, a listener and `msgsFit` give `serveTok`);
  - `icChain_call`, `icHandler_call`.

### Rpctypes

- `desc`, `code`: the table of the 63 `ErrGRPC*`. `mapped`: the description is a key of
  `errStringToError`.
- `grpcVar`, `clientVar`.
- Laws:
  - `init.spec`: the variables;
  - `errVal_fields`: `errVal e` is `EtcdError{code e, desc e}`;
  - `desc_inj`;
  - `desc_not_grpcMsg`: the boundary's assumption;
  - `errVal_errMsg`, `errVal_not_status`, `ctxErr_errMsg`;
  - **W0's `callErr`, realized**: `callErr_view`, with the introductions `callErr_status`,
    `callErr_unmapped`, `callErr_ownErr`.

### V3rpc

- `maxTxnOpsMax` (`4999`), `indefMsg`, `ansOutcome` (`LeaseTimeToLive`'s not-found reply
  included).
- The validation model: `rangeCheck`, `deleteCheck`, `opCheck`, `opsCheck`, `txnCheck`,
  `intervalsOk` (opaque). Law `txnCheck_checked`: the checks give 2c's `txnChecked` and
  `IrrBody.depthOk`.
- **The contracts**:
  - `etcdUnary γ m`: three ways to finish, joined by `∧`.
    1. Answered: fired, `Q` mapped to the outcome.
    2. Refused unfired: a token or learner refusal, the update given back.
    3. Unsettled: an `indefMsg` status.
  - `etcdLocal`: the member-local maintenance RPCs.
  - `rangeStreamSpec γ`, with its ghost state `rsReq` and `rsChunk`, and the laws `rsReq_alloc`,
    `rsReq_agree`, `rsChunk_ids`.
  - `kaSpec γ`, `snapSpec`, and `watchSpec γ` (a slot of 2b's).
  - `etcdContract γ`: the method table.
- **`servesAt_addr`**: W0's `servesAt γ ep ⊣⊢ addrAt ep (etcdContract γ)`.
- `HandlerTriple`, the shape of every unary handler's spec.
- `icEtcdOk` and `sicEtcdOk`: interceptors that preserve etcd's contracts.
- `rsSink_intro`, `rsSink_out`: 2c's `rsSink`, realized.
- Handles (persistent): `kvServerAt`, `quotaKVAt`, `leaseServerAt`, `quotaLeaseAt`,
  `authServerAt`, `clusterServerAt`, `maintAt`, `authMaintAt`, `headerAt`, `authAdminAt`,
  `quotaAlarmerAt`, `notifierAt`, `hfAt`, `streamsMapAt`, `cctxAt`, `metricsOk` (grpc-prometheus,
  assumed: `metricsOk_unary`, `metricsOk_stream`), and `quotaOk` (a slot of 2e's).
- Slots of other batches, named here: `reqModels`, `replyModels` and `chunkModels` (3h's);
  `mdPrin` (2c/3d's).
- Used from 2c: `EtcdServer.isServer`, `reqPrin`, `srvErrOf`, `SrvCallTriple`, `txnChecked`,
  `IrrBody`, `rsSink`.

## Main changes from the old specs

- **No caller-built message model, nor a pool chosen by the caller.**
  - Messages are `Proto.msgAt` over a content value. The old `PbType`/`ProtoMsg`/`StreamMsg`
    records, and `pbEnc` keyed by address, are gone.
  - A handler run is a thread of the model. It gets its `threadTok` from the trusted dispatch
    model's `Fork`. The old `grpc.serve`'s `S`/`n` pool is gone.
- **One contract per method, no modes.**
  - Auth on and off, leases, compaction, serializable reads and restarts are all in `Step`.
  - The handlers' validation errors are model answers that the handler fires itself. Before, each
    was a separate `putCheck`/`kvOut` case over the caller's `KVAns`.
  - `backendUnderQuota` is gone: a quota refusal is `.noSpace`.
  - `maxTxnOps`'s depth fact is a law (`txnCheck_checked`).
- **Sizes**: the per-call `opSizeOk`/`watchSizeOk` premises are replaced by one workload premise,
  `msgsFit`, taken by `NewClient` and `start`.
- **Addresses** are bound to contracts for good (`addrAt`). This keeps a restart at the same
  address sound: two servers at one address can never serve different contracts.
- **New**:
  - the cluster service (5 handlers), the inner maintenance methods, `RangeStream`, the promoted
    wrapper methods;
  - metadata;
  - rpctypes' exact `Error` (it returned "some client error").

## Left out

- `membersToProtoMembers` and `ClusterServer.header`: internal, inlined in the handlers'
  sketches.
- `healthNotifier.{stopServe,defragStarted,defragFinished}`: only Defragment calls them, and it
  is `etcdLocal`.
- `codec.{Marshal,Unmarshal,String}`: their content is `codecOk`.
- `grpc_health_v1.RegisterHealthServer`, the enum stringers, the remaining no-op dial options
  (keepalive, block, dialers, stats handlers): each would be a neutral `dialOptAt v id`.
- `grpc/resolver/manual`'s specs: 1c's request item 5, needed to realize `resolverAt`.

## Decisions for the user

1. **Oversized messages (W0's item 3) are false of grpc-go.**
   - An encoding over `2 ^ 48` bytes panics in grpc's codec. This happens on the client sending a
     request that holds one submessage many times, and on the server sending such a reply.
   - Proposed: the opaque workload premise `Grpc.msgsFit`, taken where connections and servers are
     made. The closed theorems are then conditional on it.
   - The alternatives are per-call size premises, which W0 refused, or a grpc fork.
   - It may also subsume K8's `--max-request-bytes` premise (the keys-only reply amplification).
2. **`addrFree ep`** is a per-address resource that the adequacy theorem gives the program (like
   the thread fuel). It is needed so that an address is bound to one set of contracts for good.
3. **The handler runs' thread tokens** come from a trusted Goose model of `Serve`'s dispatch loop
   (a modelled `Fork` per run), not from a bare axiom. The boundary is then a trusted model plus
   specs, not only axioms.
4. **2c's `srvStep` (the `doSerialize` auth race) blocks every read handler.** The handler's
   update is over `Step`, and 2c fires over `srvStep`. The fix or the scope premise is your
   decision (2c's report). No 2a spec changes either way.
5. **The model (W0)**, filed in `req/go_etcd_io_etcd_api_v3.md`:
   - **Compact needs an admin refusal.** `kvServer.Compact` checks `isPermitted` first.
   - **Six errors are not mapped by rpctypes**, so the client sees statuses for them:
     `permissionNotGiven` and `invalidClientAPIVersion` are not `errVal` at the client, and
     `ErrGRPCCanceled` is `.other`.
   - **`notSent` never occurs** with grpc v1.84.

## Open questions

- `intervalsOk` is opaque. Its realization mirrors `checkIntervals`. Whether its meaning is what
  3b's `TxnRun` needs is the law `txnCheck_checked`'s `txnChecked` part, which 2a must prove from
  3b's definition at integration.
- `kaSpec`'s responses carry nothing. 1c's item 4 asks that a response's `ID` is its request's;
  `kaRecvAt_recv` does not use it today.
- `sicEtcdOk` is opaque, unlike `icEtcdOk`, which is spelled out. The stream interceptor's
  contract should be spelled out once 2b's `watchSpec` is fixed.
- `icChain` is reused for the stream chain, whose call shape differs. It needs a stream variant of
  `icChain_call`.

## `req/` sections written (`## from 2a`)

- `req/go_etcd_io_etcd_server_v3_etcdserver.md` (2c, 2e):
  - `srvStep = Step`;
  - `reqPrin` from metadata;
  - unmapped errors' messages; context errors outside `srvErrOf`;
  - `isServer`'s `MaxTxnOps` bound;
  - `Alarm(ACTIVATE)` from `envUpd`;
  - the `rsSink` laws;
  - 2e's membership calls and getters;
  - the start sequence.
- `req/go_etcd_io_etcd_api_v3_etcdserverpb.md` (3h):
  - the relation laws, including the realization of `reqModels`, `replyModels` and `chunkModels`;
  - the fits and depth facts;
  - the generated handlers, registrations and stream wrappers;
  - the stubs;
  - `proto.Merge`.
- `req/go_etcd_io_etcd_api_v3.md` (W0):
  - the compact admin refusal;
  - the unmapped errors;
  - `notSent`;
  - oversized messages;
  - `servesAt` realized;
  - at-most-once confirmed.
- `req/go_etcd_io_etcd_client_v3.md` (1c, W0):
  - `connOk`, `dialOptsOk` and `AttemptTriple` from grpc's specs;
  - the keep-alive halves;
  - the error classification;
  - `io.EOF`;
  - `tlsCfgOk`.
