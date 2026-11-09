# Requirements on `go.etcd.io/etcd/api/v3/etcdserverpb` and `mvccpb` (the messages, batch 3h)

## from W0

W0 defined the KV messages' heap predicates the client and the server share
(`Spec/go_etcd_io/etcd/api/v3/Wire.lean`, namespace `EtcdWire`): `rangeReqOwn`, `putReqOwn`,
`deleteReqOwn`, `compareOwn`, `requestOpOwn`, `txnReqOwn`, `compactReqOwn` (requests, over
`Model.lean`'s `RangeReq`, ...) and `respHeaderOwn`, `keyValueOwn`, `rangeRespOwn`, `putRespOwn`,
`deleteRespOwn`, `responseOpOwn`, `txnRespOwn`, `compactRespOwn` (replies, over Go-level models),
with `protoRest` for the protobuf bookkeeping, each with an unfold law (field by field). They are
opaque: 3h realizes them from its own message vocabulary and proves the laws.

1. **Realize the predicates and prove their laws**: `*_unfold`, `protoRest_zero`, `replyPersist`,
   `msgOwn_ne_null`. If 3h's vocabulary makes a different shape necessary (the oneof wrappers,
   `protoRest`'s fields), say so in a `req/` to W0 rather than working around it.

2. **The generated getters** over these predicates (pointer receivers, nil-safe as protobuf's):
   `ResponseOp.GetResponseRange`, `GetResponsePut`, `GetResponseDeleteRange`, `GetResponseTxn`
   (the wrapped reply's pointer for the matching `responseOneof` case, `nil` otherwise),
   `RequestOp.GetRequestRange` (used by the server's `IsTxnReadonly`), `Compare.GetKey` (nil-safe:
   `nil` for a nil message), `RangeResponse.GetKvs`, `GetHeader`, `ResponseHeader.GetRevision`.
   ```go
   rr := resp.Responses[0].GetResponseRange()      // nil unless the else-branch ran a get
   if rr != nil && len(rr.Kvs) == 1 { ... }
   ```
   Used by: the snippets `clientv3kv/txn.go`; `Cmp.KeyBytes.spec` (`Compare.GetKey`).

3. **The enum name maps** (`RangeRequest_SortOrder_name`, `RangeRequest_SortTarget_name`): their
   init law (the maps hold exactly `0..2`, `0..4`).
   Used by: `Op.IsSortOptionValid.spec`.

4. **`NewKVClient(conn)`** (the generated stub): for `connOk conn γ who` (1c) it returns a value with
   `remoteKVAt v γ who` (`client/v3/Api.lean`), its methods `cc.Invoke`/`cc.NewStream` with the
   method names, a fresh reply message (`new(RangeResponse)`, ...) unmarshalled by grpc
   (`req/google_golang_org_grpc.md`), and the stream's `Recv` (`wireStreamAt_recv`).
   Used by: `RetryKVClient.spec`.

5. **`proto.Clone` of a `*pb.Compare`** (protobuf's boundary, 2a's proto): a fresh deep copy,
   owned (`compareOwn p' (own 1) m` from `compareOwn p dq m`). **`proto.Merge`** of
   `RangeResponse`s (repeated `Kvs` appended, `Header`/`More`/`Count` taken when set).
   Used by: `cloneCompare.spec`, `GetStreamToGetResponse.spec`.

## from 1b

1. **`pb.NewWatchClient(conn)`** for `connOk conn γ who` (W0's slot) gives `remoteWatchAt` of the
   stub (with grpc's stream, `req/google_golang_org_grpc.md` from 1b). Used by: `NewWatcher.spec`.
2. **Realize the watch messages' predicates** (`ApiWatch.lean`, possibly moved to `Wire.lean`):
   `watchReqOwn` (a `WatchRequest` whose oneof is a `WatchCreateRequest` with the watch's key,
   range end, start revision, filters `NOPUT`/`NODELETE`, `PrevKv`, `ProgressNotify`, `Fragment`;
   a `WatchCancelRequest`; a `WatchProgressRequest`), `wireWatchRespOwn` (`WatchResponse`),
   `eventOwn` (`mvccpb.Event`, `eventOwn_unfold`).
3. **Getters**: `ResponseHeader.GetRevision` on an optional header (`0` for `nil`), used by
   `WatchResponse.IsProgressNotify.spec`; `mvccpb.Event.IsCreate`/`IsModify` (Kubernetes' watcher
   reads them) over `eventOwn`.

## from 1c

1. **Realize `replyOwn p b` and `reqOwn p dq rq`** (`client/v3/ApiClient.lean`) for the non-KV
   messages, with unfold laws for the fields clients read: `AuthenticateResponse.Token`
   (`replyOwn_authenticate`, stated); `MemberAddResponse.Member`, `MemberListResponse.Members` (each
   `Member`'s `ID`, `Name`, `ClientURLs`, `IsLearner`: **translate `Member`, `MemberAddResponse`,
   `MemberListResponse`, `StatusResponse` as structs**, today names only); `AlarmResponse.Alarms`;
   the lease replies' fields the lessor copies (`LeaseGrantResponse`, `LeaseTimeToLiveResponse`,
   `LeaseLeasesResponse`); `statusRespOwn` (`Version`, `DbSize`); `userAddOptsAt` (`UserAddOptions`).
   Used by: `lessor.{Grant,TimeToLive,Leases}.spec`, `Client.Sync.spec`, snippets
   `clientv3client/{cluster,maint}.go`.
2. **The stubs** `NewLeaseClient`, `NewAuthClient`, `NewClusterClient`, `NewMaintenanceClient`
   over a `connOk` connection meet `RemoteCallTriple` for their requests (with 2a), and
   `LeaseClient.LeaseKeepAlive` opens a stream with `kaSendAt`/`kaRecvAt`. Used by: the
   `Retry*Client.spec`s and `retry*Client.*.spec`s.
4. (1b, round 1) **A create's key in `watchReqOwn`**: `toPB` sends the watch's own key, which is
   `""` when `w.range.key` is `"\x00"` (the member normalizes it): realize `watchReqOwn p dq
   (.create w s)` as a message whose key is `w.range.key`, or `""` when that is `"\x00"`.

## from 2b

Batch 2b (the gRPC watch handler) reads and builds watch messages through 1b's slots
`watchReqOwn p dq r` (a `pb.WatchRequest` modelled by `WireWatchReq`) and `wireWatchRespOwn p dq m`
(a `pb.WatchResponse`), and 1b's `eventOwn`. Their realizer (3h, with W0's `Wire.lean`) owes the
laws 2b states in `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/ApiWatch.lean`:

1. **`watchReqOwn_unfold`**: the oneof a non-`nil` wrapper of a non-`nil` inner request; a create's
   fields (`Key`/`RangeEnd` raw, `createRange k e = w.range`; `StartRevision`; the flags; the filter
   types containing `NOPUT` (`0`) iff `filterPut`, `NODELETE` (`1`) iff `filterDelete`; `WatchId =
   0`); a cancel's `WatchId`. So a wire request is what etcd's Go client sends (`toPB`); the server
   writes the create's `Key` and `RangeEnd` (owned in full from `Recv`).
2. **`wireWatchRespOwn_unfold`**: the response's fields (header `optOwn respHeaderOwn`, events
   `msgsOwn eventOwn`, the flags, `WatchId`), so that the handler builds one from a fresh struct.
3. **`wireWatchRespOwn_persist`**: own `1` to `DFrac.discard` (the handler shares a header and the
   events among a response's fragments).

Used by: `serverWatchStream.recvLoop.spec`, `sendLoop.spec`, `sendFragments.spec`.

## from 2c

Provisional predicates in `Spec/go_etcd_io/etcd/server/v3/etcdserver/ApiReq.lean` that 3h should
own: **`irrOwn p ir`** (an `InternalRaftRequest` with exactly `ir`'s field set: `Put`, `DeleteRange`,
`Txn`, `Compaction`, `LeaseGrant`, `LeaseRevoke`, `Alarm`, the auth requests, `Authenticate`'s
internal one, `LeaseCheckpoint`, `ClusterVersionSet`, `ClusterMemberAttrSet`, `DowngradeInfoSet`;
`Header` and `ID` unset), built from the client-level request messages (`putReqOwn`, ...,
`ClientV3.reqOwn`), and **`alarmReqOwn p dq ir`** (an `AlarmRequest`: `GET`, `DEACTIVATE`,
`ACTIVATE`). And `proto.Marshal` of an `irrOwn` message whose transaction is at most `9999` deep:
bytes every member's apply decodes back to `ir` with the header set (`irr-depth.md`).

## from 2a

The gRPC boundary (`Spec/google_golang_org/grpc/Api.lean`) and protobuf's
(`Spec/google_golang_org/protobuf/proto/Api.lean`) transport message **contents**
(`Proto.Content`, `Proto.msgAt t p dq c`); what a content means is the message type's owner's. What
2a's specs need of 3h:

1. **Relation laws**, one per message predicate (W0's `Wire.lean`, 1c's `reqOwn`/`replyOwn`, 1b's
   watch messages, R1's raftpb predicates): `xOwn p dq m ⊣⊢ ∃ c, Proto.msgAt X.ty p dq c ∗
   ⌜xModels c m⌝`, with `xModels` pure and a function of the content (`xModels c m → xModels c m' →
   m = m'`). In particular **realize 2a's slots** `V3rpc.reqModels m c rq` (the request content of
   method `m` models `rq`: for `/etcdserverpb.KV/Put` the `PutRequest` whose `putReqOwn` model is
   `p` iff `rq = .put p`, ...), `V3rpc.replyModels m b c` (the reply content carries the success body
   `b`, as W0's `getReply`/`putReply`/.../1c's `ansReply` say: the header's revision, the body's
   fields; the header's ids free), `V3rpc.chunkModels c m` (a `RangeStreamResponse`'s chunk). Used
   by: every handler spec's contract (`etcdUnary`), `rangeStreamSpec`.
2. **Fits and depth**: a message of a non-recursive type whose byte slices are distinct allocations
   fits (`Proto.Content.fits`); a request accepted by `checkTxnRequest` at a budget of at most `4999`
   nests below `Proto.depthMax`, and so does its reply (`Grpc.unaryOut` asks the reply's depth: the
   logging interceptor's `proto.Size`); `marshalOk` of every message a client builds from `bytes`
   fields (raft's, the KV requests), and of a message with `string` fields when they are valid UTF-8.
3. **The generated server code**: `_<Svc>_<M>_Handler(srv, ctx, dec, interceptor)` calls `dec(new
   req)` (`Grpc.decOk_call`) then, with no interceptor, `srv.(<Svc>Server).<M>(ctx, in)`, else
   `interceptor(ctx, in, info, handler)` with a fresh `UnaryServerInfo` (`FullMethod` the full name)
   and `handler` the method's call: `Grpc.icHandler` at the end of the chain; streams'
   `_<Svc>_<M>_Handler(srv, stream)` (`RecvMsg` once for a server stream, then the method with
   `&grpc.GenericServerStream{stream}` / the typed wrapper); the typed wrappers' `Send`/`Recv` are the
   stream's `SendMsg`/`RecvMsg` (`Grpc.srvSend_send`, `srvRecv_recv` at the wrapper value);
   `Register<Svc>Server(s, srv)` is `s.RegisterService(&<Svc>_ServiceDesc, srv)` with the descriptor's
   init fact `Grpc.serviceDescAt` (its methods' names and handlers). Used by: `V3rpc.Server.spec`
   (`regsOk`).
4. **The generated client stubs**: `NewKVClient(cc)`'s methods call `cc.Invoke(ctx, "/etcdserverpb.KV/
   <M>", in, out, opts...)` with `out := new(<M>Response)` (`Grpc.ClientConn.Invoke.spec`), the
   streaming ones `cc.NewStream(ctx, &<Svc>_ServiceDesc.Streams[i], name, opts...)` then (server
   streams) `SendMsg(in)`, `CloseSend()`. Used by: W0's `remoteKVAt` realization (1c, W0), 1b, 1c.
5. **`proto.Merge` of `RangeResponse`s** (W0's request): `Proto.merge c c'`'s model: `Kvs` appended,
   `Header`, `More`, `Count` taken when set (a law over `rangeRespOwn`'s relation).
