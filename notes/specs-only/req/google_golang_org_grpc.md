# Requirements on `google.golang.org/grpc` (the gRPC boundary, batch 2a)

## from W0

Batch W0 (the anchor: `Spec/go_etcd_io/etcd/api/v3/{Model,State,Wire}.lean`,
`Spec/go_etcd_io/etcd/client/v3/Api.lean` and the client's KV specs) states the client's KV path
over **one wire-level contract**, `remoteKVAt v γ who` (`client/v3/Api.lean`, `RemoteKV.*Triple`):
a `pb.KVClient` value whose `Range`, `Put`, `DeleteRange`, `Txn`, `Compact`, `RangeStream` take the
request message (`api/v3/Wire.lean`'s `rangeReqOwn`, ...) and the caller's atomic update, and
return the reply message or a classified error (`callErr`). What W0's sketches assume of gRPC, in
plain terms; the stub (`pb.NewKVClient`, batch 3h) and the server's handlers (2a's v3rpc, over 2c)
complete it (`req/go_etcd_io_etcd_server_v3_etcdserver_api_v3rpc.md`,
`req/go_etcd_io_etcd_api_v3_etcdserverpb.md`).

1. **A unary call on the client's connection** (`ClientConn.Invoke` through the client's
   interceptors, 1c), for a method registered by a member of the cluster (`servesAt γ ep`,
   `api/v3/State.lean`), carries the request to **one run** of the handler per attempt and returns
   the last attempt's reply or error. The caller's resource travels with the call (the old
   `GrpcSpec` shape: `□ ▷ Spec m Φ`, a persistent spec of the method, the caller's `Φ`), so that the
   handler can fire the caller's update. Needed: an attempt that **was not sent** fails with a
   status `Unavailable` whose message is "there is no address available" or "there is no connection
   available" (`CallErr.notSent`), and no other error has those messages; grpc never resends an
   attempt by itself once sent (no transparent retry after the request left the client: grpc-go's
   transparent retry applies only to streams that never reached the server, which is `notSent`).
   ```go
   resp, err := rkv.kc.Put(ctx, in, opts...)   // retryKVClient.Put -> stub -> cc.Invoke
   ```
   Used by: `retryKVClient.Put/DeleteRange/Txn/Compact.spec` (the exclusive update: at most one
   attempt applies), `retryKVClient.Range.spec` (any number of attempts: the update is persistent).

2. **Errors are classified** (`callErr err k`, a slot of `client/v3/Api.lean` that 2a realizes):
   every error a call returns is `.etcd e` (a status whose message is etcd's error `e`, what the
   server's `togRPCError` sent), `.notSent` (item 1), or `.other` (any other status or error: a
   context's, a transport's). Laws W0 states and 2a proves: `callErr_errVal` (`errVal e` is
   `.etcd e`), `callErr_ctxErr` (a context's error is `.other`). The specs W0's sketches call on
   them: `status.FromError` (ok and the code for a status; `Unavailable` with the two messages
   exactly for `.notSent`), `status.Status.Code`, `errors.Is(err, target)` for `target` an `errVal`
   (true only for `.etcd e` with `errVal e = target`; a status's `Is` is false against an
   `EtcdError`), `errors.Is(err, io.EOF)` (false for every `callErr`).
   Used by: `ContextError.spec`, `isSafeRetryMutableRPC.spec`, `isSafeRetryImmutableRPC.spec`,
   `kv.GetStream.spec`; the snippets `clientv3kv/errors.go`.

3. **A message of any size**: sending a request larger than the client's `MaxCallSendMsgSize`
   (etcd's client sets 2 MiB) fails with an error (`ResourceExhausted`, an `.other`), never a
   panic; the old boundary's premise `wireLen < grpcMsgMax` (`opSizeOk` on every client call) is
   not acceptable at the client's API: if the boundary's proof needs a bound, keep it inside the
   boundary's own statement (PRINCIPLES, "Keep a tool's temporary limitation as local as possible")
   and say so; W0's specs take no size premise.
   Used by: every `kv.*.spec` (no `opSizeOk`).

4. **Request messages are read, not kept**: the call reads the request (`rangeReqOwn req dq r` at
   any fraction `dq`, given back at return), marshaling's `sizeCache` writes are inside
   `protoRest`'s realization (atomic); the reply is a fresh message the caller owns in full
   (`rangeRespOwn resp (own 1) m`, ...).
   Used by: `kv.Do.spec` (the request built from the `Op`'s read-only slices), `txn.Commit.spec`.

5. **Contexts**: the call takes any `Context.ctxOk ctx` (`Spec/context/Api.lean`: Background,
   TODO, WithValue chains, Perennial's contexts, a caller's own); a call whose context is done
   returns a status `Canceled`/`DeadlineExceeded` (an `.other`) or its reply.
   Used by: every client call (`Context.ctxOk` in every `KV.*Triple`).

6. **Server streams** (`RangeStream`): `ClientConn.NewStream` + `SendMsg` + `CloseSend` open a
   stream (an open error is `.other`/`.notSent`), `RecvMsg` delivers the server's messages in order,
   then `io.EOF` once the handler returned `nil`, or the handler's error (`.etcd e`) or a
   transport error. `wireStreamAt_recv` (`client/v3/Api.lean`) is what the stub's `Recv` must meet
   (with 3h's stub and 2a's `RangeStream` handler).
   Used by: `retryKVClient.RangeStream.spec`, `kv.GetStream.spec`.

7. **Metadata** (`google.golang.org/grpc/metadata`): `FromOutgoingContext`, `Pairs`, `MD.Copy`,
   `MD.Set`, `NewOutgoingContext`: no panic for any `ctxOk` context; `NewOutgoingContext(ctx, md)`
   returns a context `ctx'` with `Context.ctxOk ctx'` and `Context.ctxWithValues ctx ctx'`.
   ```go
   md, ok := metadata.FromOutgoingContext(ctx)
   copied := md.Copy(); copied.Set(rpctypes.MetadataRequireLeaderKey, rpctypes.MetadataHasLeader)
   return metadata.NewOutgoingContext(ctx, copied)
   ```
   Used by: `WithRequireLeader.spec`, `withVersion.spec`.
