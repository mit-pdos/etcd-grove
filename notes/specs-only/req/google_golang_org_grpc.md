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

2. **Errors are classified** (`callErr err k`, a slot of `client/v3/Api.lean` that 2a realizes;
   one error has one kind: `callErr_agree`; `ErrGRPCCanceled`/`ErrGRPCDeadlineExceeded` are
   `.etcd` of the indefinite kinds `.canceled`/`.deadlineExceeded`; `errors.Is` against an `errVal`
   is `errorsIs_errVal`, a law 2a proves):
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
   Used by: `WithRequireLeader.spec`, `withVersion.spec` (they keep `ctxPrin`: the keys they set are
   not `token`/`authorization`). `metadata.AppendToOutgoingContext` and `NewOutgoingContext` with a
   caller's `token` (`examples/etcd/auth/authkv.go`) need an introduction of `ctxPrin` (a token of
   the client's own user, or a malformed one: refused) from 2a; metadata without a `token` or
   `authorization` key (Kubernetes' tracing `traceparent`) keeps it. A root context with no gRPC
   metadata is `Context.ctxNoMeta` (a transparent definition its owner discharges: net/http's
   request context, Kubernetes' `wait.ContextForChannel`), which gives `ctxPrin`.

## from 1b

Batch 1b (the client's watch, `Spec/go_etcd_io/etcd/client/v3/ApiWatch.lean`) states the gRPC watch
stream as three slots with their laws (obligations of 2a's boundary, with 3h's stub and 2b's
handler, `req/go_etcd_io_etcd_server_v3_etcdserver_api_v3rpc.md`): `remoteWatchAt v γ who` (a
`pb.WatchClient`), the stream's halves `wireWatchSend wc γ who g ss` / `wireWatchRecv wc γ who g st`
and `wireWatchSentLb g ss`. What 1b's sketches (`watchGRPCStream.openWatchClient`, `run`,
`serveWatchClient`) assume of grpc, in plain terms:

1. **Opening a bidirectional stream** (`remoteWatchAt_watch.spec`: `v.Watch(ctx, opts...)`, i.e.
   `ClientConn.NewStream` through the client's stream interceptors, 1c): for any `Context.ctxOk`
   context (the watcher's is `WithCancel(&valCtx{inctx})`, never done until canceled) and call
   options `callOptsOk`, a non-nil stream with both halves and nothing sent or received, or an error
   with a `callErr` kind (a context's, a transport's, `Unavailable`), never a panic; a `nil` stream
   with a `nil` error is not returned (the client guards anyway).
   ```go
   if ws, err = w.remote.Watch(w.ctx, w.callOpts...); ws != nil && err == nil { break }
   ```
   Used by: `watchGRPCStream.openWatchClient.spec`.
2. **Send** (`wireWatchSend_send.spec`): the request message is read (given back at any fraction)
   and delivered once, in order, to the member's handler (no resend: a message is never
   duplicated or reordered; after an error every later send fails too); an error ends nothing else.
   Only `run` sends; grpc's `SendMsg` is not called concurrently on one stream.
   Used by: `run`'s creates, cancels and progress requests.
3. **Receive** (`wireWatchRecv_recv.spec`): the member's responses in the order it sent them, each a
   fresh message the receiver owns in full (`wireWatchRespOwn p (own 1) m`), with the facts the
   handler gave it (`wireStep`, 2b); or an error ending the stream, classified (`callErr`: a
   context's error `.other`, the handler's returned status `.etcd e` for etcd's errors such as
   `ErrGRPCNoLeader`, `io.EOF` `.other`). The facts travel with the message: the old `GrpcSpec`
   shape for a stream's server-to-client messages. Only `serveWatchClient` receives.
   Used by: `watchGRPCStream.serveWatchClient.spec`, through it every `watchChAt_recv` fact.
4. **No size premise**: a create request whose key and range end exceed the send limit fails the
   stream (an error, then the client reconnects or halts), never a panic (W0's item 3, here for
   streams: the old `watchSizeOk` is dropped from `Watch`).
5. **Metadata and errors**: `metadata.FromOutgoingContext` (any `ctxOk` context; the stream key's
   `fmt.Sprintf("%+v", md)` is Perennial's `fmt`), `status.Error(codes.FailedPrecondition, reason)`
   (an error, for `WatchResponse.Err`), `errors.Is(err, context.Canceled)` (any error), and
   `status.FromError` / `Code` for 1c's `isHaltErr`/`isUnavailableErr` on every `callErr`.
   Used by: `streamKeyFromCtx.spec`, `WatchResponse.Err.spec`, `watcher.Close.spec`.

## from 1e

1. **`status.Error(codes.Unimplemented, msg)`** for a message that is not one of etcd's: a non-nil
   error with `ClientV3.callErr err .other` (so `indefCall err`). `leasingKV.GetStream` returns it:
   `leasingKV.GetStream.spec` meets W0's `KV.GetStreamTriple` through it.
2. **`status.FromError(err)`** on any error a client call returned (or a context's error): no panic,
   a status value whose `Code()` may be read. `leasingKV.acquire` retries on `Unavailable`
   (`leasingKV.acquire.spec`).

## from 1c

Batch 1c (`Spec/go_etcd_io/etcd/client/v3/ApiClient.lean`, `ApiLease.lean`) realizes W0's `connOk`
from grpc's connection and the client's interceptors. What its sketches assume of grpc (slots named
in `ApiClient.lean`, to be stated as 2a's specs or laws):

1. **One attempt** (`AttemptTriple`, `ApiClient.lean`): grpc's `UnaryInvoker` for a connection
   whose resolver's endpoints all serve `γ` (`dialTargetOk`) and whose per-RPC credentials attach
   only tokens of `who` (`Credentials.rpcCredsAt`), called with the request (`unaryArgs`: method,
   request message, reply holder), a context (`ctxOk`, `ctxPrin _ who`), gRPC options
   (`grpcCallOptsOk`) and the caller's update (`callAU`, persistent or exclusive), returns one of:
   success with the update fired and the reply filled; a definite etcd error (not a token or learner
   refusal) with the update fired; **a not-sent error, a token refusal (`ErrInvalidAuthToken`,
   `ErrAuthOldRevision`, `ErrUserEmpty`) or the learner's refusal, with the update given back
   unfired** (the server's handlers: `req/..._api_v3rpc.md`, from 1c); an indefinite error.
   ```go
   lastErr = invoker(ctx, method, req, reply, cc, grpcOpts...)   // retry_interceptor.go
   ```
   Used by: `Client.unaryClientInterceptor.spec` (`uiOk_call`), hence W0's `RemoteKV.*Triple`
   and 1c's `RemoteCallTriple`.
2. **The dial** (`grpc.NewClient(target, opts...)`): with `clientDialOpts` (the client's
   `WithUnaryInterceptor(ui)` with `uiOk`, `WithStreamInterceptor(si)` with `siOk`, transport
   credentials `transportCredsOk`, keepalive), `WithPerRPCCredentials` of `rpcCredsAt`, and the
   caller's `cfg.DialOptions` (`dialOptsOk`), a connection whose `Invoke` runs the client's
   interceptor first, then the caller's chained ones, then one `AttemptTriple` invoker per call of
   the chain's invoker; `NewStream` runs `si`; or an error. Introductions of `dialOptsOk` for
   Kubernetes' options: `WithChainUnaryInterceptor`/`WithChainStreamInterceptor` of interceptors
   that call the invoker once with their arguments (grpc-prometheus's), `WithStatsHandler`
   (otelgrpc's), `WithContextDialer`, `WithKeepaliveParams`, `WithBlock`; `dialOptsOk_nil` is 1c's.
   Used by: `Client.dial.spec`, `New.spec`.
3. **Status classification** (beyond W0's item 2): no definite etcd error's status has code
   `Canceled` or `DeadlineExceeded` (`isContextError.spec`); `status.Error` of `Canceled`,
   `DeadlineExceeded`, `Unknown` and `status.Errorf(Unimplemented, ...)` are indefinite
   (`contextErrToGRPCErr.spec`, `siOk_call`); `errors.Is(err, rpctypes.ErrGRPCNotSupportedForLearner)`
   true exactly for `callErr err (.etcd .notSupportedForLearner)` (`isSafeRetry.spec`).
4. **The lease keep-alive stream** (`ApiLease.lean`'s slots `kaSendAt`, `kaRecvAt`, laws
   `kaSendAt_send`, `kaSendAt_closeSend`, `kaSendAt_context`, `kaRecvAt_recv`): one sender and one
   receiver at a time; `Recv` returns a fresh message or a classified error; `Context()` a context
   (`ctxOk`). Used by: `lessor.keepAliveOnce.spec`, `lessor.resetRecv.spec`,
   `lessor.sendKeepAliveLoop.spec`, `lessor.recvKeepAliveLoop.spec`.
5. **Credentials and resolvers**: `credentials.NewTLS(cfg)` of a `tlsCfgOk` configuration
   (`transportCredsOk`); `insecure.NewCredentials()`; `manual.NewBuilderWithScheme`,
   `Resolver.UpdateState`, `Resolver.CC` (its panic before `Build` is recovered by etcd's
   `getCC`), `Resolver.Close`; `metadata.FromOutgoingContext` for `closeRequireLeader`.
   Used by: `credentials.*.spec`, `resolver.*.spec`, `lessor.closeRequireLeader.spec`.
6. **A stream's open may fail with the token fetch's error** (`streamClientInterceptor` calls
   `getToken` first): a definite refusal (`ErrAuthFailed`, ...) can be returned when opening a
   stream (`siOk_call`'s error disjunct). W0's `RemoteKV.RangeStreamTriple` (open error:
   `indefCall`) and 1b's watch open must admit it (`req/go_etcd_io_etcd_client_v3.md`, from 1c).

## from 2b

Batch 2b (the member's watch handler, `v3rpc/watch.go`) states the **server end of a watch stream**
as slots in `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/ApiWatch.lean`, with their laws as
obligations of 2a's boundary (with 3h's messages), mirroring 1b's client end (the same
`WatchStreamNames` `g` name the stream at both ends):

1. **Registration** (`grpc.go:81`, `pb.RegisterWatchServer(grpcServer, NewWatchServer(s))`): 2a's
   `Server` registers the `pb.WatchServer` value with its contract `watchServiceAt v γ`
   (`watchServiceAt_methods`: `WatchServer.WatchTriple`), which `NewWatchServer.spec` and
   `watchServerAt_service` give. For each stream a client of `γ` opens as `who` (`remoteWatchAt_watch`,
   1b), grpc calls the handler (`_Watch_Watch_Handler`) with a server end `st` and
   `srvWatchStreamAt st γ who g ∗ srvWatchRecv st g [] ∗ srvWatchSend st γ who g WireSt.init`, `g`
   the names of the client's halves (`wireWatchSend wc γ who g []`, `wireWatchRecv wc γ who g
   WireSt.init`). The handler needs **no thread token** (its goroutines get theirs from `Fork`).
   ```go
   pb.RegisterWatchServer(gs, v3rpc.NewWatchServer(s))
   ```
2. **`Recv`** (`srvWatchRecv_recv`): the client's requests in the order sent, each a fresh message
   owned in full, modelled by 1b's `WireWatchReq` through 1b's `watchReqOwn` (the same predicate as
   the client's `Send` takes: one wire model); an error (`io.EOF` after `CloseSend`, a context's or
   transport's) leaves the half; later receives fail. `srvWatchRecv_lb`, `srvWatchRecvdLb_sent`
   (what was received was sent: `srvWatchRecvdLb g rs ⊢ wireWatchSentLb g rs`). Only `recvLoop`
   receives.
3. **`Send`** (`srvWatchSend_send`): a response message at any fraction (read, given back: the
   handler shares a header and events among fragments, read-only) with its facts (`etcdLb γ σ`,
   `etcdLb γ σa`, `srvWatchRecvdLb g rs`, `srvWireStep who σ σa rs sst m sst'`), delivered in order;
   the client's `wireWatchRecv_recv` gives them back with the message (after 1b adopts the
   correction of `req/go_etcd_io_etcd_client_v3.md`, `## from 2b`, `srvWireStep` is `wireStep`).
   On an error the half is gone (the handler stops sending). Only `sendLoop` sends.
4. **`Context()`** (`srvWatchStreamAt_context`): a `Context.ctxOk` context with `srvCtxPrin ctx who`
   (its incoming metadata names `who`: the client's outgoing metadata, `ctxPrin`, through 1c's
   interceptors and 2a's stream interceptor); `Done()`/`Err()` as W0's context specs. If 2a states a
   server-context principal for the unary handlers (W0's item 6), 2b uses it instead of
   `srvCtxPrin`.
5. **Errors and helpers** the handler calls on stream errors: `errors.Is(err, io.EOF)`,
   `errors.Is(err, context.Canceled)` (any error, no panic); `isClientCtxErr(ctxErr, err)`
   (`v3rpc/util.go`, names only: a trusted spec, any arguments, no panic); `rpctypes.ErrGRPCWatchCanceled`,
   `ErrGRPCInvalidAuthToken`, `ErrGRPCAuthOldRevision`, `ErrGRPCUserEmpty`,
   `ErrGRPCPermissionDenied`, `ErrCompacted` initialized (rpctypes' `isPkgInit`) with `Error()` a
   **non-empty** string (a refused create's `CancelReason`, `wireStep`'s `cancelReason ≠ []`).
6. **`proto.Size(wr)`** (`sendFragments`): an `int` for a `pb.WatchResponse` owned at any
   fraction, no panic (the protobuf boundary).

Used by: `watchServer.Watch.spec`, `serverWatchStream.{recvLoop,sendLoop,isWatchPermitted}.spec`,
`sendFragments.spec`; the snippets `examples/specreq/v3rpcwatch/`.

### from 2b, round 1

* **Client-certificate principals**: see `req/go_etcd_io_etcd_server_v3_auth.md`, "from 2b, round
  1": with `ClientCertAuthEnabled`, a token-less request's principal is its TLS peer's CN; 2a's
  `mdPrin`/`rpcCtx` (and 2b's `srvCtxPrin`) must say so, or 2e takes `ClientCertAuthEnabled = false`.
* **2a's `watchSpec γ` slot and 2b's stream slots**: 2b states the handler over its own server-end
  slots (`srvWatchStreamAt`, `srvWatchRecv`, `srvWatchSend`, `srvCtxPrin`, the `wireStep` facts on
  `Send`); 2a's framework names the same stream by `srvRecv`/`srvSend` at `watchSpec γ`. At
  integration, `watchSpec γ`'s `up` is the request's wire model (`watchReqOwn`'s `WireWatchReq`,
  recorded in a ghost list keyed by the `StreamName`), `dn` the `wireStep` facts against that list
  and the client's `WireSt` (ghost, keyed likewise), `fin` nothing; `mdPrin γ md who` with `rpcCtx
  ctx md` gives `srvCtxPrin ctx who`; and 2b's slots are realized from them (or replaced by them).
* **`Send` ownership** (`srvWatchSend_send`): the handler sends read-only messages
  (`DFrac.discard`) and keeps nothing it writes; 2a's `srvSend_send` giving back the fraction sent
  is stronger than needed (grpc-go may read a message after `SendMsg` returns, grpc-go#5857).
* **The in-process pipe** (`proxy/grpcproxy/adapter`, used by `v3client`, hence v3lock/v3election)
  is not grpc and meets none of these laws as stated (it passes the message pointers): out of 2b's
  scope, an open question (`batch-2b.md`).

## from 1c (round 1)

1. **`grpcConnAt cc`** (slot, `ApiClient.lean`): the `*grpc.ClientConn` grpc's `Invoke` passes to the
   interceptor and the invoker; `cc.Target()` (read in the interceptor's log calls) is safe. Part of
   `AttemptTriple`'s and `uiOk_call`'s preconditions.
2. **`AttemptTriple`'s indefinite case excludes `.notSent`**: a not-sent attempt always gives the
   update back (case 3); item 1 of the section above should read so.
3. **`dialOptsOk` admits the gRPC proxy's interceptors** (`server/etcdmain/grpc_proxy.go:344-349`:
   `grpc.WithUnaryInterceptor(grpcproxy.AuthUnaryClientInterceptor)`, `WithStreamInterceptor(...)`):
   an introduction for `WithUnaryInterceptor(ui)`/`WithStreamInterceptor(si)` whose interceptor calls
   its invoker or streamer at most once with a context carrying the call's principal (the proxy's
   forwards the incoming token: `ctxPrin none ctx' (some u)` from W0's `ctxPrin_token`). With such an
   option grpc keeps it and drops the client's: the unary call then makes one attempt, whose
   unsettled refusals the call's ghost update fires (`uiOk_call`'s post holds of any interceptor
   that invokes once).
4. **The peer holder** (provability review S2): `grpc.Peer(&p)` writes `p` after the attempt;
   `AttemptTriple` should take and give back `p ↦ _` (or `grpcCallOptsOk`'s realization keep it).

## from 3h

Batch 3h's generated stubs (`kVClient.Put.spec`, ..., WP form: `unaryStubWP`, `streamStubWP` in
`Spec/go_etcd_io/etcd/api/v3/etcdserverpb/Api.lean`) and handlers (`_KV_Range_Handler.spec`, ...,
`handlerBodyWP`) are stated over this boundary's vocabulary. What they need of it:

1. **`grpc.StaticMethod()`**: returns a call option with `callOptOk` (no panic; it only marks the
   method name as static for metrics).
   ```go
   cOpts := append([]grpc.CallOption{grpc.StaticMethod()}, opts...) // every generated stub
   ```
   Used by: every `*Client.*.spec` of etcdserverpb.
2. **Interface dispatch of `ClientConnInterface.Invoke`/`NewStream`** to `*grpc.ClientConn`'s (the
   stubs hold the connection as the interface `grpc.ClientConnInterface`; `ClientConn.Invoke.spec`
   is at the concrete type): nothing to add if Goose's interface-call rule suffices; noted for the
   `New*Client.spec` sketches.
3. **`HandlerTriple`'s home**: 2a's `V3rpc.HandlerTriple` is written in grpc's vocabulary only; if it
   moves to `Grpc` (`Spec/google_golang_org/grpc/Api.lean`), 3h's handler specs can state their
   `unaryOk` corollary directly (today they are WP forms 2a composes with `icChain_call`).

## from 2f

Batch 2f (the net/http boundary, `Spec/net/http/Api.lean`) and 2a's grpc boundary should state
the handler runs' thread tokens the same way. The coordinator's decision (2f round 1, provability
F1), from the repository's earlier fix (`specs-ref/notes/STATUS.md`, "Soundness bugs:
grpc.serve's handler pool", the user's decision via etcd-grove-82): **`Serve` takes from its caller
a pool of the caller's thread tokens** (`Http.handlerPool p n`, made from `threadToks n` by
`Http.handlerPool_alloc`); **each handler run draws one for its life and returns it at its end**;
no token comes from nothing. The assumed physical fact is that the server runs at most `n`
handlers at once, a bound the adequacy theorem fixes. A statement realized only by a "trusted model
whose goroutines are forks" is not acceptable until that model exists, and grpc-go and net/http are
names-only (2a's `Api.lean:14-19` still claims the fork realization). Please restate `Server.Serve`
over such a pool. If both boundaries share one pool predicate, 2f will use 2a's name; until then
`Http.handlerPool` is 2f's.

## from 3d

The auth store reads a request context's incoming metadata and TLS peer (`AuthInfoFromCtx`,
`AuthInfoFromTLS`, `WithRoot`). Its specs are stated over two provisional slots in
`Spec/go_etcd_io/etcd/server/v3/auth/Api.lean`, to be realized by this boundary:

1. **`Auth.ctxInMD ctx o`** (persistent): `metadata.FromIncomingContext(ctx)`'s answer for *any*
   context, not only a run's (`Grpc.rpcCtx`): `some md` (every key with at least one value: the
   store indexes `ts[0]`, `nonissues/etcd-auth-token-md-empty.md`) or `none` (a context with no
   incoming metadata: `Background()`-derived, the server's `s.ctx`). Needed laws: `rpcCtx ctx md ⊢
   Auth.ctxInMD ctx (some md)`; `Context.ctxNoMeta`-like intro for contexts without incoming metadata
   (`Background`, `WithCancel`/`WithValue` children: `ctxInMD ctx none`); a spec of
   `metadata.New(map)` and `metadata.NewIncomingContext(ctx, md)` (`WithRoot`: the result `ctxOk`,
   `ctxInMD ctx' (some md)`, the peer kept). `Auth.mdToken` reads it (`token`, then `authorization`,
   `Bearer ` trimmed). Used by: `authStore.AuthInfoFromCtx.spec`, `WithRoot.spec`.
   ```go
   md, ok := metadata.FromIncomingContext(ctx)   // auth/store.go:1052
   ts, ok := md[rpctypes.TokenFieldNameGRPC]
   token := strings.TrimPrefix(ts[0], "Bearer ")
   ```
2. **`Auth.ctxCertUser ctx c`** (persistent): what `AuthInfoFromTLS` reads: `peer.FromContext`, its
   `AuthInfo` a `credentials.TLSInfo` whose first non-empty verified chain's leaf has common name
   `cn`, incoming metadata present and without `grpcgateway-accept`: `some cn`; else `none`. A run's
   context should give it from the connection's TLS state. Used by: `authStore.AuthInfoFromTLS.spec`
   (assumed), and through it 2b's round-1 finding (the principal of a token-less request with a client
   certificate is its common name).
3. **`mdPrin γ md who`'s realization** (2a's slot): `who = none` iff `Auth.mdToken md = none` (and no
   certificate user, with client-certificate auth), else `who = some u` with `tokenUser γ tok u` for
   the token `tok`: what `AuthInfoFromCtx.spec` and W0's `tokenUser_agree` turn into the store's
   answer. `togRPCError`'s table for the auth errors is `Auth.AuthErr.etcd` over `Auth.errOf`.
