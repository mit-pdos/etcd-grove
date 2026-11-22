# Phase 7: etcd's gRPC, net and net/http axioms as theorems over the models (plan, Draft)

2026-11-21, claim #24. Phase 7 of `notes/dsverify-net-port-plan.md`, planned on its own as that section
says. Coordination: #10's `grpc3` (grpc's resolver, `resolver/manual`, `attributes`, `serviceconfig`,
etcd's `client/v3/internal/resolver`) and `http3` (`Proof/net/http/{Axioms,Boundary}.lean`,
`Proof/net/textproto/Header.lean`, rafthttp's `Codec`, `snapshotHandler.ServeHTTP`) land what they
have and then release the area to #24 (coordinator, #10, 2026-11-21). Nothing below edits those files
before that.

## What there is (inventory, `lean` at `ed897615f5`)

102 of `etc/tcb-baseline.txt`'s axioms mention grpc, net or http: 15 package-init axioms
(`initFuncsOk`/`opaqueInitsOk` of grpc's packages, net, net/http, net/url, `toGRPCErrorMap_init`), and 87
others. `etcd-all.txt` (`etcd_safe`) holds 99 of the 102. By kind:

- **Vocabulary**, axiomatized predicates with no definition: grpc's `grpcSrvNew`, `grpcAddrIsRaw`,
  `grpcSrvCfgRaw`, `grpcSrvLink`, `grpcConnsLink`, `grpcReplyTo`, `grpcConn`, `grpcResolverAt`,
  `grpcWrotePeer`, `grpcDialOptIs`, `grpcSrvOpt`, `grpcProtoCodec`, `grpcStatsHandlerOk`,
  `grpcHealthSrv` (`Proof/google_golang_org/grpc/Inv{Grpc,GrpcServer,GrpcRun,Dial}.lean`); net's
  `netAddrFree`, `netListenerAt`, `httpProtoFree` (`Proof/net/InvNet.lean`); and net/http's `opaque`s
  in `Proof/net/http/Boundary.lean` (`httpProtoAtRaw`, `respReader`, `bodyReader`, `respWriter`, ...: not
  axioms, so not in the TCB lists, but as uninterpreted).
- **Transport and connection**, over that vocabulary: `grpc.NewServer`, `Server.RegisterService`,
  `grpc.start`, the stage-B names `grpc.model.{acceptRun,acceptRunConns,respond,finishStream}` (with
  the trusted `Server.Serve` body), `NewClient`, `ClientConn.Invoke`, `ClientConn.NewStream`,
  `etcdResolver_grpc`; `net.Listen`; net/http's `reserve`, `register`, `Serve_ok`, the response
  writer, the body readers, the client (`RespClose*`, `ReadAll_resp_ok`, `ReadFull_resp_ok`,
  `CloseIdleConnections_ok`, `transport.NewTimeoutTransport`), the mux.
- **Leaves**, Go code the models keep verbatim: grpc's option constructors (`With*`, `MaxRecvMsgSize`,
  `ChainUnaryInterceptor`, ...), `CustomCodec`, `StatsHandler`, health, the prometheus interceptors,
  `ClientConn.Target`; net/http's `NewRequest`, `WithContext`, `URLString*`, `ReadAll`. Their *posts*
  are in the vocabulary's terms, so they become provable once the vocabulary is defined.

The protocol facts the vocabulary gives clients, which the model proofs must re-establish: a
connection reaches only the server listening at the dialed address; a handler runs at most once per
attempt (`grpcInvokerOk` consumes the call's spec once; `respond` consumes the exclusive
`grpcReplyTo`); a success returns the handler's reply; errors are in `clientErrTys`; a stream's two
directions are queues (`InvGrpcStream.lean`: in order, no loss or duplication, `io.EOF` only after the
peer's close and everything received); net/http's closed world (a request a server gets came from a
program's `RoundTrip`), at most once for `onceOnly` requests, statuses the handler's or Go's own, reads
a prefix of what the handler wrote.

## The two couplings that decide the order

1. **grpc's translation is independent of the network.** The model (`models/grpc`) has grpc-go
   v1.84.0's API and keeps its option, server-construction, interceptor and stream-wrapper code
   verbatim. Project `etcd` can take grpc's source from the model instead of the module cache (a
   `replace` in the translation's module file, as `models/grpc/gomodel.py` does for Go builds), under
   the same `Code/google_golang_org/grpc*.toml` (names-only but for what is proved). Then the leaves
   and server construction are provable over the model's bodies without any network semantics.
   Checked 2026-11-21: goose translates all 51 of the model's packages (71k Lean lines) with only two
   refusals: a labeled `continue` (`mem.ReadAll`, `health/client.go`) and `unsafe.StringData` in four
   generated `.pb.go` descriptors (protobuf plumbing, names-only as in etcd today). Whether the output
   compiles depends on the standard-library and protobuf names it calls; not built yet.
2. **`net` is coupled to the deployment statement.** The transport-level axioms (`Invoke`, `Serve`,
   `grpc.start`, `net.Listen`, all of net/http's server and client) can only become theorems over the
   net extension's `Conn`/`Listener`. The main tree's `net` is names-only today, over the axiomatized
   `netAddrFree`/`netListenerAt`, and every etcd closed theorem runs in **one process with no net
   extension** (`etcdFsExts := ⟨[idIssueExt, Fs.fsExt]⟩`,
   `examples/lib/etcdstart/FsExts.lean:46`; `etcd_safe` is eleven examples on separate clusters in one
   process). Making `net` the part's means adding the net extension to every etcd program's
   extensions, and getting the addresses' ownership from a deployment plan instead of the
   axiomatized premise `addrsUnclaimed` (`Proof/runtime/Start.lean`). That is a statement change for
   `etcd_safe` and every collection above it: the user's decision (below).

## Slices

Each lands on its own through the queue, with `etc/tcb-report.py --check --update` and the
collections' baselines saying what it removes.

- **S0, prerequisites.** (a) Project `etcd`'s grpc from the model: the `replace`, `etc/goose.py`'s
  handling of a module model (it has `std_models` for standard-library models; this is the module
  case), `etc/goose.py --check` with it, and `Code/google_golang_org/grpc*.lean` regenerated: no
  axiom removed, every proof still building (the model's `dialOptions`/`serverOptions` differ from
  v1.84's by a few fields: `models/diff.py grpc`). (b) The two goose refusals worked around in the
  model (`mem.ReadAll`'s labeled `continue` rewritten; the `.pb.go` descriptors names-only).
  Waits for `grpc3`'s release.
- **S1, server construction and options** (about 18 axioms). Define `grpcSrvOpt`, `grpcDialOptIs` and
  `grpcSrvNew` over the option closures' effect on `dialOptions`/`serverOptions` and the `Server`
  struct's fields; prove the option constructors, `NewServer`, `Server.RegisterService` over the
  model's bodies; then health (`RegisterHealthServer`, `grpcHealthSrv`) and `grpcProtoCodec` (as
  `models_lab.pbcodec`'s `PbCodec`, phase 5 item 1). `StatsHandler`/`otelgrpc.NewServerHandler`: the
  model removed stats handlers (a `NotModelled` panic), but etcd installs one
  (`v3rpc` `Link.lean`), so either the model keeps the stats-handler calls (decided in S1; the
  handler's methods are then the program's code) or the theorem would be vacuous there. No network.
  **S0 landed** (`715d5e6753`, 2026-11-21). **S1, server side (branch `phase7-s1`, 2026-11-21).**
  `grpcSrvOpt v k` is a definition (`Proof/google_golang_org/grpc/InvGrpcServer.lean`): `v` is a
  `*funcServerOption`, read-only, whose closure's persistent WP over a `p ↦ so` does `k`
  (`srvOptFnOk`): `.neutral` keeps the chains and the stats handlers; `.chainUnary`/`.chainStream`
  own the chain they append to; the new kind `.stats h` owns `statsHandlers`. A kind owns what its
  closure reads, so `StatsHandler`'s restated axiom stays true: stated as `.neutral` it would assert a
  WP of an `append` reading a slice the closure does not own, false for an arbitrary `so`. Proved
  over the model's bodies (`etc/goose.py`'s grpc translate list): `MaxRecvMsgSize`, `MaxSendMsgSize`,
  `MaxConcurrentStreams`, `KeepaliveEnforcementPolicy`, `ChainUnaryInterceptor`,
  `ChainStreamInterceptor` (one recipe: `wp_fupd`, `ipersist` of the captured cells,
  `wp_func_lits`, step into `newFuncServerOption`, then the closure; the chains through
  `wp_slice_append`). Still axioms, restated: `NewServer` (`[∗ list]` premise), `CustomCodec`,
  `StatsHandler` (`.stats h`). For `serverOptions` to be a translated struct, grpc's imports gained
  `time`, `io` (the `Compressor`/`Decompressor` interfaces of its `cp`/`dc` fields), `credentials`,
  `keepalive` and `stats`, and the model's `serverOptions` lost three fields whose types are other
  packages': `binaryLogger` and `inTapHandle` (their options panic when `NewServer` applies them,
  where the model's `NewServer` panicked on them before) and `bufferPool` (the server reads
  `mem.DefaultBufferPool()`, grpc-go's default; the option setting another pool panics), so that
  `tap`, `internal/binarylog` and `mem` stay untranslated, with no init axiom of theirs (a first
  attempt translating `mem` types-only added its two init axioms, which the land queue's tcb gate
  rightly refused; S2 translates `mem` with its pools). Trust base: −7 (the six, `grpcSrvOpt`).
  Users adjusted: v3rpc's `Server` spec (`[∗ list] v ∈ gvs, grpcSrvOpt v .neutral`) and proof, the
  `etcdstart`/`cluster3` callers. **Server stats handlers in the model (2026-11-22, branch `phase7-stats`).** The model's server
  calls a stats handler as grpc-go does, which kaashoek's `etcd_dist_safe` server needs with tracing on:
  per connection `TagConn`/`ConnBegin`/`ConnEnd`, and per call `TagRPC`, `InHeader`, `Begin`,
  `InPayload`, `OutHeader`, `OutPayload`, `OutTrailer` and `End`, in grpc-go's order, with grpc-go's
  fields except `InHeader.WireLength`. That one is an HPACK size, given by a new choice point,
  `modelChooseLength`. `internal/grpcdifftest/stats_test.go` checks the sequences of a unary call, a
  failed call and the stream kinds against grpc-go's. One visible difference: a connection per stream
  means one `ConnBegin`/`ConnEnd` pair per call. The trusted claim is narrowed in `models/README.md` to
  programs whose behavior does not depend on how many connections carry their calls; otelgrpc's
  `TagConn`/`HandleConn` do nothing. Client stats handlers still panic `NotModelled`. **The dial side (2026-11-22,
  branch `phase7-dial`).** `grpcDialOptIs o d` is a definition (`InvDial.lean`): a read-only
  `*funcDialOption` whose closure's persistent WP over `p ↦ dopt` sets what `d` sets
  (`dialOptSets`) and keeps the other descriptor fields (`dialOptsKeep`); `.resolvers` and
  `.perRPCCreds` own the slice they append to. `dialOptsAt`'s fact is a `[∗list]`. Proved over the
  model's bodies: `WithTransportCredentials`, `WithPerRPCCredentials`, `WithUnaryInterceptor`,
  `WithStreamInterceptor`, `WithResolvers`. `WithKeepaliveParams` stays an axiom (it calls grpc's
  logger), restated. For `dialOptions`/`connectOptions` to be translated structs: grpc imports `net`
  and `resolver` too (their instances moved before grpc's in the cache's `Base.lean`), and the model's
  dial structs name no type of `internal/backoff`, `internal/binarylog`, `channelz` or `mem`
  (`withBinaryLogger`, `WithChannelzParentID`, `withBufferPool` panic `NotModelled`; the reconnect
  backoff is `DefaultExponential`, a timing). Trust base −6 (the five, `grpcDialOptIs`). client/v3's
  `Client__dial*` proofs adjusted. Landed `bbc60799b2`. S1 ends here: `NewServer` and
  `RegisterService` move to S2 (2026-11-22). Proving them means defining `grpcSrvNew` over the model's
  `Server` (its services map, the chained interceptor), the predicate the stage-B `Serve` axioms
  (`acceptRun`, ...) read, so its definition is S2's server invariant; the `Server` struct is also
  opaque until grpc imports `internal/grpcsync` and the model's `traceEventLog` is dropped.
- **S2, the unary pair** (`NewServer`, `RegisterService`, `grpc.model.*`, the trusted `Serve` body,
  `grpcReplyTo`, `Invoke`'s attempt, `grpc.start`). **A resource for the callees (2026-11-22, proving
  session 2's request on #24):** the contracts S2 restates, the client interceptor chain and the attempt
  (`grpcInvokerOk`, as `ClientConn.Invoke`/`NewStream` use it), per-RPC credentials'
  `GetRequestMetadata` and the server interceptor chain (`grpcSrvChain`/`srvChainWP`), take a resource
  parameter the caller passes in and gets back (as `isTransporter tr Rd`), so that etcd's
  `Client.Endpoints`, `perRPCCredential.GetRequestMetadata` and `api.IsCapabilityEnabled` can trade it
  for an `RWMutex` reader slot (`/shared/tmp/ps2/rdslot/design.md`, rafthttp's `8f442de83b`); draft
  signatures go to #24 before the proofs. over `model_transport.go`/`model_wire.go` and the net extension's `Conn`,
  from dsverify's unary proofs (Q2). Needs S4's deployment, or an interim single-machine statement
  over `goose_dist_adequacy` with one machine, which keeps `etcd_safe`'s single process but adds the
  net extension.
- **S3, streams** (`NewStream`, the stream ends, `InvGrpcStream.lean`'s two queues as a fact about the
  connection's two byte streams through the model's framing).
- **S4, the deployment statement.** Each member a machine (one node per member), the client drivers
  machines or co-located; addresses from the plan (`DistDeploy`-like); `netAddrFree`, `netListenerAt`,
  `httpProtoFree`, `addrsUnclaimed` gone; restart examples over the crash adequacy.
- **S5, net/http.** The server first (`Serve_ok`, the response writer, `Flush`, the body reader, the
  mux) over the model's real server (the largest proof); `reserve`/`register` as a per-address
  protocol registry; then the client, which needs the `Transport.RoundTrip` model (it panics today,
  `models/net/http/transport.go:614`) and chunked request bodies (the snapshot;
  `models/net/http/transfer.go:575`). Waits for `http3`'s release. Before S5, the main tree's
  names-only `Code/net/http.lean` and the part's `Net/Code/net/http.lean` declare the same namespace,
  so one replaces the other (with S4).

## For the user

1. **The deployment statement (S2/S4).** Decided 2026-11-22 (the user's answer, relayed by kaashoek on
   #24): one machine per member, over the net extension. The `net` half of the names-only swap goes to
   kaashoek's sessions once `phase7-dial` landed (it has, `bbc60799b2`); `net/http` stays here (S5).
2. **Stats handlers in the grpc model (S1):** kept (landed, `phase7-stats`). Open: the user's approval
   of the narrowed trusted claim (a handler sees a connection begin/end per stream; #24).

## Risks

- Goose and Perennial on the model's code: `mem.BufferSlice` and its pools, `sync.Cond`
  (`GracefulStop`), `time.AfterFunc`/`time.NewTimer`, `url.Parse` (targets), `fmt` verbs in
  `status.Errorf`, map iteration in header writing (specs must not fix header order), channels and
  `select` in the transport.
- The models' over-approximations may add error descriptions today's axioms exclude (REFUSED_STREAM,
  any non-OK code on a cut, idleness at any time, the spurious clean end of a server stream after a
  transparent retry, `nonissues/grpc-transparent-retry-spurious-eof.md`): proofs using `noRefusalAt`
  or `refusalDescs` must be rechecked.
- Addresses: `netAddrLit` is loopback-only (the `HTTP_PROXY` reason); the net extension's `addrOk`
  allows any unicast address. A distributed etcd over non-loopback addresses reopens rafthttp's
  `ProxyFromEnvironment` unless the deployment premise excludes a proxy environment.
- Size: option B's estimate, 60-110k Lean lines for all of it; dsverify's HTTP server proof alone is
  1.4k lines for a much simpler server.
