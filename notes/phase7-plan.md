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
  calls a stats handler as grpc-go does, which kaashoek's `etcd_safe` server needs with tracing on:
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
  signatures go to #24 before the proofs (written: "S2 draft signatures (2026-11-23)" below). over `model_transport.go`/`model_wire.go` and the net extension's `Conn`,
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

## S2 draft signatures (2026-11-23)

These are the names S2's proofs will be stated against, written before any proof, for #24
(kaashoek's putget-dist, proving session 2). Branch `phase7-s2-design`, off `lean`. The groundwork
`a12d44ed4f` on `phase7-s2` (grpc's `Server` as a translated struct) is not merged here. Nothing
below is built. The Lean text is the intended statement, and `...` marks a body sketched in prose.
Library names are neutral: `Net.*`, `GooseLang/Ext/Net` and grpc's
`Proof/google_golang_org/grpc/`. etcd's names live in etcd's files.

### 0. Where the answer on #24 had to change

Most of the answer's shape holds:
- `grpcSvcAt` does not depend on any heap, and `isGrpcRpc`/`isGrpcRpcMd` are redefined as it.
- The deposit travels in the connection's protocol.
- The start fixes the address, and the member publishes `E` once.
- A success implies that `E` was published.

Four details of it do not work as stated:

1. **There is no saved predicate of the service.** Perennial's saved predicates store
   `A → IProp GF` for a countable `A` (`Perennial/Ghost/SavedProp.lean`: `savedPredOwn` stores
   `Φ ∘ decode`). A method's spec takes the caller's `Φ` and `Ψe`
   (`GrpcSpecMd := GrpcMd → Req.M → (Rep.M → IProp) → (GoString → IProp) → IProp`). That puts
   `IProp` in a negative position, so the spec cannot be saved.

   It does not need to be. The net library keeps an address's protocols as *parameters of its
   invariant* (`addrInvP a γa P Q`, set once by `addr_set_proto`). `listen_au` needs
   `addrProto a P Q`, so the protocol is fixed before the member listens, which is before `E`
   exists anyway. So **the service is a Lean term `Svc`, fixed when the address's protocol is
   set**. The deployment's start sets it: the top-level proof, before the machines run.
   - `Svc` may mention ghost names that the start allocates (`γE`), but never `E`.
   - What the member sets at run time is the publication of `E` at `γE`, which is a fact on
     etcd's side. `Serve` publishes nothing about the service.
   - So "the per-address service right" is the net library's own `addrUnset a`, spent by the start
     (§1.2's `grpc_addr_set`). The member receives `grpcAddrAt a Svc` already set.
2. **`envAt γE E` cannot agree on `E : apply.AEnv GF` itself.** `AEnv` holds:
   - `IProp`-valued fields (`Nx`, `Pk`, `RD`, `FS`, `RO`, `RW`, `Cp`, `BkTie`, `Wt`);
   - one field with `IProp` in a negative position (`ciC : IProp GF → w64 → Prop`);
   - values on the member's heap (`kv : GoInterface`, `f : GoFunc`).

   No camera of `GF` can hold a value whose type mentions `IProp GF`. So the agreement is over a
   countable **view** `ν : EnvView` (ghost names, ids, modes), with `E = etcdEnvOf ν`. It is
   `dghostVar γE .discard (some ν)` (§1.3). The specs that clients see must factor through the
   view (open question O1). `etcdstart`'s `env₀` and `envAgree` suggest they do: `envAgree` reads
   only `γs`, `γrev`, `Nx` and `cmp`.
3. **The spec in the table must not depend on a heap, and neither may the message models it is
   typed over.** The table is one Lean term that both machines hold. A spec built with a `HeapGS`
   means a different proposition on each machine. One example is a points-to at a server `Loc`:
   `kvOpAuOn s E …` takes the server's `s`.
   - The rule: an entry's spec takes no `HeapGS` (O2).
   - Its types are the **wire part** `ProtoWire` of the message models (`ty`, `M`, `tree`), which
     involves no heap.
   - `tree` is only in `ProtoMsgT` today. `ProtoMsg` gains it, so that `isGrpcRpcMd`, which is
     typed over `ProtoMsg`, can name it (O3).
4. **`Invoke`'s post gains nothing at the grpc level.** `envAt γE E` reaches the client through
   the spec that etcd puts in the table (`etcdPubSpec`, §1.3), not through a conjunct of grpc's
   spec. The caller's obligation is for *every* view published at `γE`, and its `Φ` names the
   view.
   - So "a success means `E` was published" follows from the spec's shape, with no ordering
     between machines.
   - A dial before the listener exists is the semantics' refused `Dial`. That is an
     `Unavailable` error in the error arm. Its description is not in `handlerDescs`, so it carries
     no `Ψe`.

There is also one scope cut: **streams stay on the old pair in S2** (§2.6). The stream
registration (`isGrpcStreamAt`, a WP of the handler) still depends on the server's heap, so it is
used only within one machine until S3.

### 0a. Amendment (2026-11-23, S2 core, branch `phase7-s2-core`): three corrections

This supersedes the parts of §1.1, §1.2 (`headReady`, `grpcAttemptSlot`, `grpcCliP`, the
"How a unary call travels" steps 2-3, "At most once" (a)) and §4 (O1, O2) that it names.

1. **The unary deposit travels with the message, to the server's `dec`, not with the head.**
   - grpc-go v1.84 runs the unary handler as soon as the stream's headers arrive (`server.go:1446-1450`),
     and its `dec` is `stream.RecvMsg`. The client queues HEADERS in `newClientStream`
     (`call.go:70`, `http2_client.go:915`) and only then marshals the request, in
     `SendMsg`/`prepareMsg` (`stream.go:1072`), which can fail.
   - The model does the same (checked): `invoke` (`models/grpc/call.go`) runs `newClientStream`,
     whose `newClientTransportStream` (`model_transport.go`) writes the head frame in one write,
     before `SendMsg` runs `prepareMsg` and `csAttempt.sendMsg` writes the data frame and the close
     frame together (`Write(hdr, payld, Last: true)`, one write). On the server, `HandleStreams`
     reads the head, `operateHeaders` refuses (`REFUSED_STREAM`, `drainReads` after it) or
     dispatches, and `handle(s)` starts the handler before any data frame is read; the unary
     handler is `wrapUnaryHandler`'s, whose `df` is `stream.RecvMsg`.
   - So the deposit cannot be in the head's protocol fact: a marshal failure would leave it there
     after a head the server dispatched. The client **registers the slot just before it writes
     the data frame** (the marshal has succeeded, the bytes `bs` are known), and the data frame's
     protocol fact is the slot. The server **claims when its `dec` has read a whole data frame**:
     the handler gets the caller's `spec md m Φ Ψe` only from a `dec` that returned nil (the shape
     of dsverify's quepaxa kit: `dec` returning nil gives `∃ m Φ, spec … ∗ Got Φ ∗ <decoded>`;
     the handler is proved for any receipt `Got`). `headReady fs` becomes
     `msgReady fs bs W := clientPrefaceBytes ++ headFrame fs ++ dataFrame bs <+: W`.
   - **Refusal is per connection, not per slot.** The model refuses after the head, before reading
     any data, possibly before the client registered its slot (the client writes its data without
     waiting). So the server cannot give a deposit back from a slot it may not see. Instead it
     spends its `connFresh cn true` into the slot map's invariant (`conn_refuse`, giving the
     persistent `connRefused cn`), and the `REFUSED_STREAM` reset carries `connRefused cn`. A
     claim needs that same `connFresh cn true`, so a refused connection's slot is never claimed,
     and the client takes its deposit back with `connRefused cn` and its token
     (`depSlot_takeRefused`), before the transparent retry's buffered `sendMsg` re-deposits it on
     the new attempt's connection. `SlotOut.refused` goes: the slot's outcome type is the user's
     (grpc: `.ok bs`, `.err d`).
   - **Withdraw** stays as the draft has it (the dialer's `sendTok` frozen at a `W` with
     `¬ ready W`), and the claimed states keep the claim's `sentLb cn false W'` with `ready W'`,
     which is what refutes a withdraw after a claim. The model never needs it (a head write that
     fails registered no slot; a data write that fails allows no retry: `shouldRetry` retries only
     an unprocessed stream), but the library has it for other users.
   - `depSlotInv` loses its `P` parameter (the frozen `sendTok` is at an existential protocol), so
     `grpcCliP` and the slot are not mutually defined.
2. **O1, decided** (kaashoek's answer on #24): `envAt γE ν` over a countable view `ν` = (`γs`,
   `γrev`, `authOn`, the read names, `cid`); `etcdEnvOf ν` sets
   `Nx := srvApi.kvNx (viewRd ν) false` and `Cp := kvCpOk (viewRd ν).kv`.
3. **O2, decided**: the service table's specs are re-sectioned over
   `[GooseGlobalGS]`/`[GoLocalContext]` (no heap). That restatement (about 30 defs modules) and the
   etcd-side users are proving session 2's part, on its own branch; S2's core builds on its
   interface when it lands (#24), and touches none of those modules.

**Built so far** (`phase7-s2-core`): `GooseLang/Ext/Net/Slot.lean` (the slot library, §1.1 as
amended; laws proved) and `Proof/google_golang_org/grpc/InvGrpcWire.lean` (the model's bytes, the
two protocols, `grpcAddrAt`, `grpcSvcAt`, `grpc_addr_set`, and the parse laws that make the protocols
usable: `cli_read_slot`, `srv_data_answered`, `srv_trailer_answered`). Changes to §1.2 made there:
- `ProtoWire` has the message's bytes `enc : M → List w8`, not a tree (`pbEncodeTree` does not
  exist; O7 decides how `enc` relates to the store, and O3 becomes `ProtoMsg` gaining `enc`).
- The deposit is at every metadata the server may make of the head (`grpcFieldsMd fs md`, stated on
  the keys grpc does not set, as `grpcAttemptMd` is; a `-bin` key through the base64 encoder
  `b64Raw`), not at a function `mdOfFields`.
- The trailer's fact is over its `grpc-message` field percent-decoded (`grpcMsgDecode`, Go's
  `decodeGrpcMessage`), not over a `statusOf`.
- `grpcSlotCont`'s error arm is `⌜d ∈ handlerDescs⌝ -∗ Ψe d` (the server can answer any error).
- Data and trailer frames say nothing when the connection's head is a well-formed head of no unary
  method of `Svc` (`streamConn`: streams, unknown methods), which a unary attempt's client refutes
  from its own head (`streamConn_unary`).

**F1 (finding, the grpc model): a header block of 4 GiB or more is misframed.** `appendHeaderBlock`
(`models/grpc/model_wire.go`) writes the block's length and each field's length as `uint32`s,
truncating them. A head whose fields total 4 GiB (a context's outgoing metadata, which nothing
bounds) is then read by the server as other fields, possibly another method's head, while grpc-go's
HTTP/2 server rejects any header list over its 16 MiB default (`MaxHeaderListSize`; the model's own
reader, `readHeaderBlock`, refuses a block over `maxHeaderBlock`, but only after the truncation). The
protocol requires every head well formed (`headOk` in `grpcCliP`), so the client attempt's proof
needs either the model to refuse such a head before writing it (proposed: `newClientTransportStream`
fails the attempt when `len(b) > maxHeaderBlock + 5`, without a transparent retry, as grpc-go's
server would answer it with a connection error), or a premise bounding the metadata. The same holds
for the server's header and trailer blocks (a handler's `SetHeader`/`SetTrailer` metadata).

**F1, fixed in the model (2026-11-23, `phase7-s2-core`; a trusted-model change for the user's review).**
Measured against grpc-go v1.84.0 (`models/internal/grpcdifftest/headerlimit_test.go`): grpc-go's
server does **not** advertise `SETTINGS_MAX_HEADER_LIST_SIZE` unless `grpc.MaxHeaderListSize` is set
(`http2_server.go:205`), so its client's `checkForHeaderListSize` passes and the *receiver's* framer
refuses a list over 16 MiB (x/net's count, name + value + 32 per field). The outcomes: client
metadata just over the limit, Internal "stream terminated by RST_STREAM with error code:
FRAME_SIZE_ERROR"; a value over it, Unavailable "error reading from server: EOF" (connection
error); a server header or trailer over it, Unavailable "error reading from server: connection error:
COMPRESSION_ERROR" after the handler ran; the handler of a refused head never runs, and a stream
with such metadata is created (`NewStream` succeeds, `Recv` fails). The model (`MODEL:` notes on
`headerListTooLarge`, `model_wire.go`) now checks the list before writing: the client's
`newClientTransportStream` ends the stream unsent with one of the first two outcomes (`modelChoose`,
no transparent retry); the server's `writeHeaderBlock` writes the marker `appendOversizedBlock` (a
block length over the limit, no fields), which the client's reader refuses with one of grpc-go's three
outcomes (`headerListTooLarge`, `modelChooseN(3)`). In Lean: `headerListOk`, `headOk_of_listOk`,
`SrvFrame.oversized` (`srvFrameOk` says nothing). Left as before (a gap of the claim, now stated in
`models/README.md`): the `MaxHeaderListSize` options are ignored, so a program that sets a limit is
outside the claim.

**Built in the session's second part** (`phase7-s2-core`): `Code/google_golang_org/grpc.toml` translates
the frame writers with bodies (`headerListTooLarge`, `appendHeaderBlock`, `appendOversizedBlock`,
`appendData`, `appendReset`, the frame-kind constants, `maxHeaderBlock`, `clientPreface`) and imports
`encoding/binary` (its package fact imported in `cache/v3/Base`); `errHeaderListTooLarge` is
skipped. Proved, no axiom: `binary.bigEndian.AppendUint32` (`Spec/encoding/binary/`, from Perennial's
translated body; a candidate for Perennial) and `grpc.headerListTooLarge` (`false` iff
`headerListOk (hfPairs hs)`; the model's sum now adds one length at a time, so it cannot overflow in
GooseLang, where only `len` bounds a string below `2 ^ 63`). Not linked yet (no grpc Link holds them).
Next, in order: `appendData` and `appendHeaderBlock` (bytes `dataFrame`, `headerBlock kind (hfPairs
hs)` under `headerListOk`); then `newClientTransportStream`'s callees, which need the skipped error
variables' initializers translated (`errMalformedFrame`, `transportFailureCodes`, `http2ErrConvTab`,
`errStreamDone`, `metadataFromOutgoingContextRaw`, `ErrClientConnClosing`; goose refuses a
reference to a skipped variable) and specs of `credentials`, `grpcutil`, `strings`, `strconv`,
`time.Until` for `createHeaderFields`.

**Built in the session's third part** (`phase7-s2-core`, 2026-11-23; no axiom, no `sorry`):
- **The frame writers, proved**: `appendData` (`b ++ frameData :: hdr ++ payload`, `appendData_dataFrame`
  makes it `dataFrame bs`), `appendHeaderBlock` (`b ++ headerBlock kind (hfPairs hs)` under `headerListOk
  (hfPairs hs)`: the length sum `hbLenPre` and the bytes `hbBytesPre` are its loops' invariants,
  `listOk_length`/`listOk_field` bound each `uint32`), `appendOversizedBlock` (`srvFrameBytes
  (.oversized kind)`), `appendReset` (`srvFrameBytes (.reset code)`); `u32Le_reverse`:
  `AppendUint32`'s bytes are `be32`. Specs `Spec/google_golang_org/grpc/append*.lean`; the pure laws in
  `InvGrpcWire`. Not linked yet (no grpc `Link`).
- **Six skipped variables translated with their initializers** (`grpc.toml`): `errMalformedFrame`,
  `errStreamDone`, `errHeaderListTooLarge` (`errors.New`), `ErrClientConnClosing` (`status.Error`),
  `transportFailureCodes`, `http2ErrConvTab` (slice literals of codes); grpc now imports `codes` and
  `status`. `etc/gen-init.py`'s grpc entry proves them (Perennial's `errors.wp_New_errorString`, the
  existing `status.Error.wp_proof`, `wp_slice_literal`): no new `opaqueInitsOk`; grpc's `Init` is now
  split (`InitLinked`, since `status.Error.wp_proof` is a proof module), and so are its importers'
  (`etcdserverpb`, `v3lockpb`, `v3electionpb`, `health`, `reflection`, the prometheus middleware). The
  translation's `clientTransportStream` is now a translated struct (two `axiomatized type` instances
  fewer). `cache/v3/Base`: the `codes`/`status` instances moved above grpc's. The fact `grpcInit` says
  nothing of the new variables yet (adding to it rebuilds about 7700 modules: do it once, with what the
  client attempt's proof needs: `errStreamDone` a non-nil error, `transportFailureCodes`' contents).
- **Left skipped**: `metadataFromOutgoingContextRaw`. Its initializer asserts the type of
  `internal.FromOutgoingContextRaw`, which `metadata`'s `init` sets; grpc's `internal` package is not
  translated at all. Needed: translate `google.golang.org/grpc/internal` (names-only, its variable
  `FromOutgoingContextRaw`), `metadata`'s `init` and `fromOutgoingContextRaw`, and a `metadata` fact
  (`internal.FromOutgoingContextRaw ↦□ the function value`) for the assertion and the call. A `SPECIAL`
  entry for `metadata` in `gen-init`.
- **`createHeaderFields`' callees**: `time.Until` proved (`Spec/time/Until.lean`, as Perennial's
  `Since`; a Perennial candidate). Still to do: `strings.LastIndex` (names-only in Perennial:
  `notes/perennial-changes.md`), `grpcutil.{RegisteredCompressors, ContentType,
  IsCompressorNameRegistered, EncodeDuration}`, `credentials.NewContextWithRequestInfo`,
  `istatus.IsRestrictedControlPlaneCode`, `imetadata.ValidatePair` (all in `models/grpc/internal/...` and
  `models/grpc/credentials`: translatable with their bodies), the model's `encodeMetadataHeader` and
  `isReservedHeader`, `strconv.Itoa` (Perennial's), `strings.{TrimSuffix, ToLower}` (Perennial's and the
  repository's).

**Built in the session's fourth part** (`phase7-s2-core`, 2026-11-23; no axiom added, no `sorry`):
- **`metadataFromOutgoingContextRaw`, translated and proved.** grpc's `internal` is translated names-only
  but `FromOutgoingContextRaw` (`Code/google_golang_org/grpc/internal.toml`: its other initialized
  variables `[[skip]]`s, literals; `translate_types`: two `axiomatized type` instances, `HealthChecker`,
  which names the untranslated `connectivity`); `metadata`'s `init` and `fromOutgoingContextRaw` with
  their bodies. The cell is another package's (allocated by `internal`, written by `metadata`'s `init`,
  read by grpc's initializer) and a package fact is persistent, so it lives in `internal`'s fact
  `internalInit` (`cache/v3/Base.lean`), an invariant with two states: *held* (the cell, a counter
  `γS` past `0` only with `fromOutRawAny` in it, the whole ghost variable `γI`) and *lent* (a package
  state `ownGoState σ`, exclusive, and half of `γI` at `σ`). A package initializer takes the cell out by
  lending its package state, does its plain (non-atomic) load or store, and puts it back
  (`Proof/google_golang_org/grpc/internal/FromOutRaw.lean`: `fromOutRaw_alloc`, `fromOutRaw_acc`,
  `wp_store_fromOutRaw`, `wp_load_fromOutRaw`). `metadata`'s fact `metadataInit` (until then `True`) is
  the invariant with the counter's lower bound `1`. `etc/gen-init.py`: `SPECIAL` entries for `internal`
  (the invariant's allocation), `metadata` (the translated `init`'s store) and grpc's
  `metadataFromOutgoingContextRaw` (the load, then the type assertion and the store into a `GoFunc`
  cell). The trust-boundary axiom `metadata.initFuncsOk` is gone (`etc/tcb-baseline.txt`,
  `tcb-collections/mvccfull.txt` edited by hand: no full build was run). grpc's `wp_initialize'_lb`
  reaches, as before, grpc's own `initFuncsOk`/`opaqueInitsOk`, `status.Error.wp_proof`,
  `codes.initFuncsOk`, `credentials.opaqueInitsOk`. `grpcInit` still says nothing of the new variables.
- **A grpc-model rewrite (trusted, for review):** `createHeaderFields`' audience takes the method's last
  `/` with a backwards byte loop (`MODEL:`) in place of `strings.LastIndex` (names-only in Perennial), as
  `net/rpc/server.go` does; `internal/grpcdifftest`'s `TestPerRPCCredsAudience` (new: with and without a
  `:443` suffix, against grpc-go and the model); `run.sh` green; `models/README.md`.
- **`createHeaderFields`' callees translated with their bodies:** `internal/grpcutil` (new;
  `RegisteredCompressorNames`, whose fact `grpcutilInit` is the nil slice for good, `IsCompressorNameRegistered`,
  `RegisteredCompressors`, `ContentType`, `EncodeDuration`, `div`), `internal/metadata` (new;
  `ValidatePair`, `ValidateKey`, `hasNotPrintable`), `internal/status.IsRestrictedControlPlaneCode`,
  `credentials.NewContextWithRequestInfo`, and the model's `isReservedHeader`, `encodeMetadataHeader`,
  `encodeBinHeader`; grpc imports `strings`, `strconv`, `encoding/base64` (so `cache/v3/Base` imports
  base64's fact), `grpcutil`, `internal/metadata`. Their vocabulary: `HeaderFields.lean` (`reservedHdr`,
  `contentTypeOf`, `keyOk`/`pairOk`, `restrictedCodes`).
- **Proved** (Lean's three axioms; not linked: no grpc `Link` yet): `grpc.isReservedHeader`,
  `grpcutil.ContentType`, `grpcutil.IsCompressorNameRegistered` (`false`), `grpcutil.RegisteredCompressors`
  (`""`, over Perennial's `strings.Join.spec`), `istatus.IsRestrictedControlPlaneCode` (over
  `status.Status.Code.spec`, the existing trust boundary).
- **Left, with what each needs:** `ValidatePair` (Perennial's `fmt.Errorf` spec covers its `%q`:
  `wp_Errorf_argsWf`); `EncodeDuration` (Perennial's `strconv.FormatInt`); `encodeMetadataHeader`
  (`base64.RawStdEncoding.EncodeToString`: base64's fact `base64Init` has `StdEncoding` and
  `RawURLEncoding` only, so it gains a `rawStdEncInit` part, proved in base64's generated `Init` as
  `rawUrlEncInit` is: a change to base64's fact); `NewContextWithRequestInfo` (`context.WithValue`'s
  spec, `Spec/context/WithValue.lean`, lists the key types it accepts; `requestInfoKey` is not one:
  extending it changes that trusted statement, left for review).
- **Found (for the head's spec, not a bug):** per-RPC credentials may return a pseudo-header key
  (`ValidateKey` skips keys starting with `:`), which `createHeaderFields` appends after the real
  `:path`. grpc-go's HTTP/2 server refuses a pseudo-header after a regular one (a stream error); the
  model's server takes the last `:path` (`pathOf`), an over-approximation the claim allows. The client
  attempt's spec therefore needs the credentials' keys not to be pseudo-headers (etcd's token
  credentials return `token` only): a premise from the credentials' contract (`connCredsOk`).

**Built in the session's fifth part** (`phase7-s2-core`, 2026-11-23; no axiom added, no `sorry`):
- **Proved** (Lean's three axioms; not linked): `imetadata.hasNotPrintable` (`decide (¬ ∀ b ∈ msg,
  printable b)`), `imetadata.ValidateKey` (`nil` iff `keyOk`, otherwise an error `fmtErrorOk`: the
  repository's `fmt.Errorf.spec`, a callee), `imetadata.ValidatePair` (`nil` iff `pairOk`, the values'
  slice back; over `ValidateKey`, `hasNotPrintable` and Perennial's `strings.HasSuffix.spec`),
  `grpcutil.div` (`durDiv`: `sdiv`, plus one on a positive `srem`), `grpcutil.EncodeDuration`
  (`encodeDurationOf`: the units in Go's order, over Perennial's `strconv.FormatInt.spec`), the model's
  `encodeBinHeader` (`b64Raw` of the bytes) and `encodeMetadataHeader` (`encMdHdr k v`). Pure laws in
  `HeaderFields`: `keyByteOk_iff`, `printable_iff`. No Perennial gap met (Perennial's `fmt.Errorf`,
  `strconv.FormatInt`, `strings.HasSuffix` specs sufficed).
- **base64's fact gains `rawStdEncInit`** (`RawStdEncoding`'s `EncodeToString` returns `rawStdEnc`, the
  standard alphabet without padding): `base64Init` is now four parts; `rawStdEncInit_intro`
  (`InitFacts`), proved in the generated `InitLinked` from `StdEncoding.WithPadding(NoPadding)`
  (`etc/gen-init.py`'s `SPECIAL['encoding.base64']`); `rawStdEncInit_access`. A change to base64's fact:
  its ~7700 importers rebuild (only the targets this work needs were built here; CI builds the rest).
  `InvGrpcWire`'s `b64Raw` is now an abbreviation of base64's `rawStdEnc` (its copy of the encoder,
  `b64Char`/`b64Alphabet`, removed), so the protocol and the code use one encoder.
- **`credentials.NewContextWithRequestInfo.spec`** (`Spec/google_golang_org/grpc/credentials/`), stated, no
  proof file: the new context's `Value(requestInfoKey{})` is `ri`, every other key the parent's (in
  `context.WithValue.spec`'s form), and a description of the parent describes the child with the key
  added (`credentials.withRequestInfo`). To be taken as a callee-spec hypothesis by
  `createHeaderFields`' proof until the user decides on `context.WithValue`
  (`Proof/context/WithValue.lean` untouched).

Next: `createHeaderFields`. Its spec is not yet written; what it needs: the head's fields as a function
of the call header, the connection's user agent, the deadline (`encodeDurationOf (time.Until dl)`), the
credentials' metadata (a premise from `connCredsOk`/`perRPCCredsOk`: `pairOk` keys, none `:`-prefixed,
above) and the outgoing metadata (`metadata.Outgoing`'s raw form, `encMdHdr`, reserved keys skipped:
`grpcHdr.reservedHdr`), stated so that `grpcFieldsMd`/`headOk` follow; the map ranges' order is
arbitrary, so the post is over a permutation within each map's block. Its error arms: the credentials'
errors (`status.FromError`, `IsRestrictedControlPlaneCode`, `status.Errorf`), `ValidatePair`'s
(`status.Error(Internal, err.Error())`), the deadline's. Then `newClientTransportStream`, the stream's
`Write`/`reader`; `grpcInit` gains, once, what the client proof needs (`metadataFromOutgoingContextRaw`
holding `fromOutgoingContextRaw`, `errStreamDone` non-nil, `transportFailureCodes`' contents).

**Built in the session's sixth part** (`phase7-s2-core`, 2026-11-23; no axiom added, no `sorry`):
- **`createHeaderFields` translated with its body and proved** (`Spec/google_golang_org/grpc/createHeaderFields.lean`,
  `Proof/google_golang_org/grpc/createHeaderFields.lean`, vocabulary `Proof/google_golang_org/grpc/InvHeader.lean`). The
  post: on `nil`, `hfPairs hs = callHdrFields ch acc ua ++ tfs ++ afs ++ ofs` with `timeoutFieldsOk tfs` (`grpc-timeout` at
  `encodeDurationOf d` for some positive `d`, or nothing), `credsFieldsOk cms afs` (the maps `cms` the per-RPC credentials
  returned, one per credential, each `□ Q cm`, merged with a later map's value winning, `credsLookup`, in some order of the
  keys, `enumKeys`) and `outFieldsOk o ofs` (none without a `rawMD`; else the map's keys in some order, each key's values
  unless reserved, then the `added` rows' pairs, `rowFields`); on an error, only `err ≠ nil` (the credentials' own error, a
  status error made of it, `ValidatePair`'s refusal as `Internal`, `DeadlineExceeded`). Premises: `ch.Creds' = nil` (the
  model sets call credentials only from a `PerRPCCredsCallOption`, which `grpcOptOk` excludes), the credentials' contract
  `hdrCredsOk pc Ok Q` (non-nil; `GetRequestMetadata` with the resource `R` returns a `status`-accepted error or a map with
  `credKeysOk`: lower-case keys, no `:` prefix, §0a's pseudo-header finding), `ctxDeadline ctx`, and `outRawIs ctx o` (the
  `rawMD` the context holds at `mdOutgoingKey{}`, read-only, rows' keys lower case). Taken as hypotheses: the callees' specs,
  `credentials.NewContextWithRequestInfo.spec` (unchanged, pending the `context.WithValue` decision) and
  `grpc.outRawFn.law` (`isPkgInit grpc ⊢ metadataFromOutgoingContextRaw ↦□ fromOutgoingContextRaw`, a defs-module law; it
  becomes provable when `grpcInit` gains that cell, the batched `grpcInit` change). The proof needs
  `[context.Assumptions]` (`deadlineExceededError.Error`'s unfolding).
- **`metadata.fromOutgoingContextRaw` proved** over a named `rawMD` (`ro : Option rawMD`: GooseLang's interface values do not say
  that a value of dynamic type `rawMD` is one, and struct values have no `IntoValInj`).
- **`istatus.IsRestrictedControlPlaneCode`'s spec restated** over a `Code()` WP (what `status.FromError`'s post gives) in place of
  `statusAt` (which it does not); its proof no longer needs `Status.Code.spec`.
- **Open, for the user (not a bug):** the head's metadata is stated over what the transport reads (`outRawIs`, the `rawMD`'s heap
  contents), not over `metadata.outMD ctx om`: `outMD`'s `builtRawMDRaw` is a trusted opaque with no law, so nothing relates the
  two; likewise `grpcAttemptMd`'s `credsYield` is opaque. The client attempt's proof needs a law (or a definition) for each:
  `builtRawMDRaw v f ⊢ ∃ r ms rsl, v = mkOk rawMD #r ∗ …` with `f` the merged view, and `credsYield` replaced by the maps the
  credentials returned (`hdrCredsOk`'s `Q`).

Next: `newClientTransportStream` (`headerListTooLarge`, `appendHeaderBlock` under `headerListOk`, the head's write), the stream's
`Write` and `reader`; then the batched `grpcInit` change (`metadataFromOutgoingContextRaw`, `errStreamDone`,
`transportFailureCodes`), which proves `grpc.outRawFn.law`.

**Built in the session's seventh part** (`phase7-s2-core`, 2026-11-23; no axiom added, no `sorry`):
- **The metadata gap, `outMD` side, closed by a definition.** `metadata.builtRawMDRaw v f` (`Proof/context/LibKeys.lean`),
  a trusted opaque with no law since errdesc stage 1, is now `∃ M rows, metadata.rawMDAt v M rows ∗ ⌜f = rawView M rows⌝`:
  the `rawMD`'s read-only contents (the map's values `M`, the `added` rows), map and row keys lower case, rows of even
  length (`rawOk`), and `f` `FromOutgoingContext`'s merge (`rawView`: a key's map values, then its rows' values in
  order). `metadata.outMD`'s text is unchanged. Proved: `outRawIs_of_outMD` (`InvHeader.lean`): a context with
  `outMD ctx md` has the raw contents `o` the transport reads (`outRawIs`, `createHeaderFields`' premise) with
  `md = outViewOf o`. Ledger 2026-11-23 (`builtRawMDRaw`): the producing axioms (`AppendToOutgoingContext`,
  `withVersion`, `WithRequireLeader`, `WithCancelValCtx`, the model's server contexts) now claim the contents; checked
  against grpc v1.84 and etcd; narrowed to lower-case map keys (the opaque allowed non-colliding upper-case keys of a
  literal `MD`, which no verified program builds). For the user's review.
- **Not retired:** the axioms `metadata.AppendToOutgoingContext`, `withVersion`, `WithRequireLeader`. Their bodies need
  `context.WithValue` at `mdOutgoingKey{}` returning a `*valueCtx` (the chain form `outMD` is in): this repository's
  `context.WithValue.spec` is a trust-boundary axiom (Perennial translates `context` without `WithValue`'s body) whose key
  list excludes grpc's key, and extending it changes a trusted statement (the same decision as `requestInfoKey`, fifth
  part). Proposed: Perennial translates `WithValue` with its body (a `valueCtx` allocation; `ctxValue_valueCtx` already
  exists), after which these three and `NewContextWithRequestInfo` are provable here.
- **`credsYield`, not done: the design.** `credsYield conn cm` (opaque) is the only link from a connection to what its
  credentials returned. Replacing it needs the credentials' predicate at the attempt: `grpcConn` (an axiomatized
  predicate) gains `CQ : GrpcMd → IProp GF` (NewClient's post: `credsQOf (credsOfDial ds) Q`, `[] ↦ ⌜cm = none⌝`,
  `[_] ↦ □ Q cm`, more ↦ `True`; `connCredsOk` goes), `grpcInvokerOk conn addrs Ok CQ inv` asks
  `▷ ∀ md cm, CQ cm -∗ ⌜grpcAttemptMd cm om md⌝ -∗ Spec md m Φ Ψe` with `grpcAttemptMd` pure over the merged
  credentials' metadata `cm` (`credsLookup` of `createHeaderFields`' `cms`, `credsMapIs` per map), and the etcd client's
  `isEtcdConnG`/`connTokOk` carry `CQ` (`connTokOk conn P` becomes `□ ∀ cm, CQ cm -∗ tokMdOk P cm`, no consumer today).
  36 uses of `grpcConn`, 67 of `grpcInvokerOk` (15 files, three trusted statements: `NewClient`, `ClientConn.Invoke`,
  `ClientConn.NewStream`): a spec change at the client boundary, to do with `ClientConn.Invoke`'s proof over the model
  (where `grpcConn` becomes a definition and `CQ` its dial's), not before it.

- **The user's rule (2026-11-23): no hand-written stand-ins for real library functions in the models.** Go's real
  function is translated and proved (in Perennial), or becomes a Go model under perennial#692's overlay; until then the
  call stays as Go writes it and proofs through it wait. The fourth part's `LastIndex` byte loop in
  `createHeaderFields` stays for now (a separate branch reverts it to `strings.LastIndex` once Perennial has it); no
  further proof here depends on the loop specifically (the client attempt's proof takes `createHeaderFields.spec`, whose
  statement names no audience). The user approves any change that adds no Lean axiom and no premise of a top-level
  theorem.

### 1. The vocabulary

#### 1.1 Deposit slots (net library, neutral: `GooseLang/Ext/Net/Slot.lean`)

This generalizes `remote`'s slot (`Net/Proof/.../examples/lib/remote/Defs.lean`: `slotOf`,
`slotInv`, `slot_register`, `slot_claim`, `slot_done`, `slot_take`) so that grpc and remote share
it. remote can move onto it later; that is not part of S2.

There is one slot per connection, keyed by what the dialer's bytes say. grpc's transparent retries
need two laws that remote does not use:
- the acceptor **refuses**: it gives the deposit back;
- the dialer **withdraws**: it takes the deposit back when the acceptor can never have read enough
  to claim it.

```lean
namespace Net

/-- What the acceptor of a slot answered: bytes the dialer decodes, an error description, or
that it refused the deposit (gave it back). -/
inductive SlotOut where
  | ok (bs : List w8)
  | err (d : GoString)
  | refused
deriving DecidableEq            -- with a `Pos.Countable` instance

/-- The slot map's ghost name (made once, by `depSlots_alloc`). -/
class NetSlotGS where
  slots : GName

/-- A slot's names: the outcome (a dfrac ghost variable `Option SlotOut`, the acceptor's half
while it runs) and the dialer's token. -/
structure SlotNames where
  o : GName
  t : GName

variable [NetProtoGS] [σ : NetSlotGS] {K : Type} [Pos.Countable K]

/-- The slot map's invariant: every registered connection, with its dialer's `connFresh cn false`
(so a connection has at most one slot). -/
def depSlotsCtx : IProp GF := inv slotsN (∃ M : GMap Nat (SlotNames × Pos),
  ghostMapAuth σ.slots 1 M ∗ [∗map] cn ↦ _v ∈ M, connFresh cn false)

/-- The connection `cn` has the slot `γ`, with the key `k` (persistent). -/
def depSlotOf (cn : Nat) (γ : SlotNames) (k : K) : IProp GF :=
  ghostMapElem σ.slots cn .discard (γ, Pos.Countable.encode k)

/-- **A dialer's prefixes after which an acceptor may claim** (closed under extension). -/
structure SlotReady (ready : List w8 → Prop) : Prop where
  mono : ∀ a b, ready a → a <+: b → ready b

/-- **The slot's invariant** (persistent): `ready` the dialer's written prefixes after which an
acceptor may claim, `D` the deposit, `Φ` what the dialer gets for an outcome. States: registered
(`D`); claimed (the acceptor's `connFresh cn true` in it, the acceptor holding the outcome's other
half, `slotRunTok`); answered `o` (`D` back if `o = .refused`, else `Φ o`, or the dialer's token
once taken); withdrawn (the dialer's `sendTok` on `cn` frozen at a `W` with `¬ ready W`, and its
token). -/
def depSlotInv (cn : Nat) (γ : SlotNames) (P : Proto GF) (ready : List w8 → Prop)
    (D : IProp GF) (Φ : SlotOut → IProp GF) : IProp GF :=
  inv (depSlotN cn) (
      (D ∗ dghostVar γ.o (.own 1) (none : Option SlotOut))
    ∨ (connFresh cn true ∗ (dghostVar γ.o (.own (1/2)) (none : Option SlotOut) ∨
        ∃ o, dghostVar γ.o .discard (some o) ∗ ((if o = .refused then D else Φ o) ∨ token γ.t)))
    ∨ (∃ W, ⌜¬ ready W⌝ ∗ sendTok cn false P W ∗ token γ.t ∗
        dghostVar γ.o (.own 1) (none : Option SlotOut)))

/-- The acceptor's share of a claimed slot (exclusive). -/
def slotRunTok (γ : SlotNames) : IProp GF := dghostVar γ.o (.own (1/2)) (none : Option SlotOut)

/-- The slot answered `o` (persistent). -/
def slotDone (γ : SlotNames) (o : SlotOut) : IProp GF := dghostVar γ.o .discard (some o)

-- The laws (each at a mask `E` that contains the slot's and the map's namespaces):
theorem depSlots_alloc (E : CoPset) : ⊢ |={E}=> ∃ σ : NetSlotGS, depSlotsCtx (σ := σ)
theorem depSlotOf_agree (cn : Nat) (γ γ' : SlotNames) (k k' : K) :
    depSlotOf cn γ k ∗ depSlotOf cn γ' k' ⊢ ⌜γ = γ' ∧ k = k'⌝
/-- Register (the dialer, once per connection, with the fresh token its `Dial` gave). -/
theorem depSlot_register (cn : Nat) (k : K) (P : Proto GF) (ready : List w8 → Prop)
    (D : IProp GF) (Φ : SlotOut → IProp GF) :
    depSlotsCtx -∗ connFresh cn false -∗ D ={E}=∗
      ∃ γ, depSlotOf cn γ k ∗ depSlotInv cn γ P ready D Φ ∗ token γ.t
/-- Claim (the acceptor, with its fresh token, once a `ready` prefix was written). -/
theorem depSlot_claim (hr : SlotReady ready) (W : List w8) (h : ready W) :
    depSlotInv cn γ P ready D Φ -∗ connFresh cn true -∗ sentLb cn false W -∗ £ 1 ={E}=∗
      D ∗ slotRunTok γ
/-- Answer (`o ≠ .refused`), or refuse (giving `D` back). -/
theorem depSlot_answer (o : SlotOut) (ho : o ≠ .refused) :
    depSlotInv cn γ P ready D Φ -∗ slotRunTok γ -∗ Φ o ={E}=∗ slotDone γ o
theorem depSlot_refuse :
    depSlotInv cn γ P ready D Φ -∗ slotRunTok γ -∗ D ={E}=∗ slotDone γ .refused
/-- Take the answer (the dialer, with its token): `D` back on a refusal, else `Φ o`. -/
theorem depSlot_take (o : SlotOut) :
    depSlotInv cn γ P ready D Φ -∗ slotDone γ o -∗ token γ.t -∗ £ 1 ={E}=∗
      if o = .refused then D else Φ o
/-- Withdraw (the dialer, giving up writing at a `W` at which no acceptor can claim). -/
theorem depSlot_withdraw (hr : SlotReady ready) (W : List w8) (h : ¬ ready W) :
    depSlotInv cn γ P ready D Φ -∗ token γ.t -∗ sendTok cn false P W -∗ £ 1 ={E}=∗ D
```

`depSlot_withdraw` is sound for these reasons:
- A claim needs `sentLb cn false W'` with `ready W'`.
- The frozen `sendTok`'s `wHalf` bounds every lower bound by `W` (`wHalf_wLb_prefix`), so
  `W' <+: W`.
- By `SlotReady.mono`, `ready W` would follow, contradicting `¬ ready W`.

#### 1.2 grpc's service table, protocols and registration (`Proof/google_golang_org/grpc/InvGrpcWire.lean`, `InvGrpc.lean`)

```lean
/-- **A message type's wire part** (no heap): its Go type, its model, and the tree its model
stores as (what grpc's codec marshals: the bytes are `pbEncodeTree (tree m)`). -/
structure ProtoWire [GooseExts] where
  ty : go.GoType
  M : Type
  tree : M → VTree

/-- `ProtoMsg` gains `tree` (moved from `ProtoMsgT`, which becomes `abbrev ProtoMsgT := ProtoMsg`;
O3), and this projection: -/
def ProtoMsg.wire (T : ProtoMsg GF) : ProtoWire := ⟨T.ty, T.M, T.tree⟩

/-- The bytes of a gRPC message holding `m` (grpc's codec over protobuf-go; the payload of a data
frame after its 5-byte header). -/
def grpcMsgBytes (W : ProtoWire) (m : W.M) : List w8 := pbEncodeTree (W.tree m)

/-- **A unary method of a service**: its messages' wire parts and its spec (no `HeapGS`). -/
structure GrpcEntry (GF : BundledGFunctors) [GooseExts] where
  Wq : ProtoWire
  Wp : ProtoWire
  spec : GrpcMd → Wq.M → (Wp.M → IProp GF) → (GoString → IProp GF) → IProp GF

/-- **A service table**: the unary methods by full name (`"/etcdserverpb.KV/Put"`). -/
abbrev GrpcSvc (GF : BundledGFunctors) [GooseExts] := GoString → Option (GrpcEntry GF)
```

**The model's bytes** (`models/grpc/model_wire.go`). The constants and frame builders are Lean
functions of the Go code's:
- `clientPrefaceBytes`: the 24 bytes of `clientPreface`;
- `settingsBytes`: `[frameSettings]`;
- `headFrame fs`: `appendHeaderBlock nil frameHead fs`;
- `dataFrame bs`: `frameData :: 0 :: be32 bs.length ++ bs` (uncompressed);
- `closeFrame`, `cancelFrame`, `headerFrame fs`, `trailerFrame fs`, `resetFrame code`.

Over `fs : List (GoString × GoString)` (the header fields, as `headerField`s):
- `pathOf fs`: the `:path` value;
- `mdOfFields fs : GrpcMd`: what `operateHeaders` makes the run's incoming metadata (the fields
  whose keys are not reserved, `grpcReservedKey`);
- `statusOf fs : Option (w32 × GoString)`: `grpc-status` and `grpc-message`, decoded as
  `model_http_util.go` does.

```lean
/-- What a unary attempt deposits for the entry `e`: its request precondition at the attempt's
metadata (the caller's own spec converted with `grpcSvcAt`'s wand, under the later the slot needs). -/
def grpcDeposit (e : GrpcEntry GF) (md : GrpcMd) (m : e.Wq.M) (Φ : e.Wp.M → IProp GF)
    (Ψe : GoString → IProp GF) : IProp GF := iprop(▷ |==> e.spec md m Φ Ψe)

/-- What the attempt gets back for an outcome: a reply whose bytes are some `m'`'s, with `Φ m'`;
or a handler's error description with its `Ψe`. -/
def grpcSlotCont (e : GrpcEntry GF) (Φ : e.Wp.M → IProp GF) (Ψe : GoString → IProp GF) :
    SlotOut → IProp GF
  | .ok bs => iprop(∃ m', ⌜grpcMsgBytes e.Wp m' = bs⌝ ∗ Φ m')
  | .err d => iprop(⌜d ∈ handlerDescs⌝ ∗ Ψe d)
  | .refused => iprop(True)

/-- A dialer's prefix after which the server may claim: the preface and the whole head. -/
def headReady (fs : List (GoString × GoString)) (W : List w8) : Prop :=
  clientPrefaceBytes ++ headFrame fs <+: W

/-- The slot of a unary attempt on `cn` (persistent): the head `fs` names `e`'s method, the
request's bytes are `bs` (some `m`'s), and the slot holds the deposit at `fs`'s metadata. -/
def grpcAttemptSlot (Svc : GrpcSvc GF) (cn : Nat) (fs : List (GoString × GoString))
    (bs : List w8) : IProp GF :=
  iprop(∃ (name : GoString) (e : GrpcEntry GF) (γ : SlotNames) (m : e.Wq.M)
      (Φ : e.Wp.M → IProp GF) (Ψe : GoString → IProp GF),
    ⌜pathOf fs = some name ∧ Svc name = some e ∧ grpcMsgBytes e.Wq m = bs⌝ ∗
    depSlotOf cn γ (fs, bs) ∗
    depSlotInv cn γ (grpcCliP Svc) (headReady fs) (grpcDeposit e (mdOfFields fs) m Φ Ψe)
      (grpcSlotCont e Φ Ψe))
-- `grpcCliP` and `grpcAttemptSlot` name each other: either one mutual definition, or
-- `depSlotInv`'s `P` parameter is dropped (the withdrawn state then holds `sendTok cn false _ W`
-- at an existential protocol, which `depSlot_withdraw` needs no more of).

/-- **What a client writes** on a connection to an address serving `Svc`: the preface; then a head
`fs`. If `fs` names a unary method of `Svc` (`unaryOf Svc fs`), the attempt's slot, one data frame
of the slot's bytes, the end of the request, and possibly a cancel (`unaryTail bs rest`: `rest`
is a prefix of `dataFrame bs ++ closeFrame`, or that followed by a prefix of `cancelFrame`). A head
of any other path (a stream, or a name `Svc` lacks) allows anything after it (S3's case, §2.6). -/
def grpcCliP (Svc : GrpcSvc GF) : Proto GF := fun cn W =>
  iprop(⌜W <+: clientPrefaceBytes⌝ ∨
    ∃ fs rest, ⌜W = clientPrefaceBytes ++ headFrame fs ++ rest⌝ ∗
      ((⌜unaryOf Svc fs = false⌝) ∨
       (⌜unaryOf Svc fs = true⌝ ∗ ∃ bs, ⌜unaryTail bs rest⌝ ∗ grpcAttemptSlot Svc cn fs bs)))

/-- **What a server writes**: its preface; then header and trailer blocks, at most one data frame
and a reset. Each frame that answers for the attempt's slot carries that answer: a data frame of
bytes `bs'` carries the slot's `.ok bs'`; a trailer whose status description `d` is a handler's
(`d ∈ handlerDescs`) carries `.err d`; a `REFUSED_STREAM` reset carries `.refused`. Frames that
claim nothing (an OK header, a status grpc makes itself, a `CANCEL` reset) need nothing. The slot
is the one of the client's head (`depSlotOf cn γ (fs, bs)`, unique per connection). -/
def grpcSrvP (Svc : GrpcSvc GF) : Proto GF := fun cn W =>
  iprop(⌜W <+: settingsBytes⌝ ∨
    ∃ frames, ⌜W <+: settingsBytes ++ (frames.map srvFrameBytes).flatten⌝ ∗
      [∗list] f ∈ frames, srvFrameOk cn f)
-- srvFrameOk cn (.data bs')        := ∃ γ k, depSlotOf cn γ k ∗ slotDone γ (.ok bs')
-- srvFrameOk cn (.trailer fs)      := ∀ c d, ⌜statusOf fs = some (c, d) ∧ d ∈ handlerDescs⌝ -∗
--                                       ∃ γ k, depSlotOf cn γ k ∗ slotDone γ (.err d)
-- srvFrameOk cn (.reset refused)   := ∃ γ k, depSlotOf cn γ k ∗ slotDone γ .refused
-- srvFrameOk cn _                  := True

/-- **The address `a` serves `Svc`** (persistent): its protocols are grpc's for `Svc`, and the
slot map exists. -/
def grpcAddrAt (a : GoString) (Svc : GrpcSvc GF) : IProp GF :=
  iprop(addrProto a (grpcCliP Svc) (grpcSrvP Svc) ∗ depSlotsCtx)

/-- **The start law**: an unset address is set to serve `Svc` (the net library's
`addr_set_proto`). -/
theorem grpc_addr_set (E : CoPset) (a : GoString) (Svc : GrpcSvc GF) :
    ⊢ regCtx -∗ depSlotsCtx -∗ addrUnset a ={E}=∗ grpcAddrAt a Svc

/-- **The method `name` at `a` meets `Spec`** (persistent, no heap; it replaces
`grpcAddrIs a γ ∗ isGrpcRpcAt γ name Spec`): the table `a` serves has an entry for `name` at the
wire parts `Wq`, `Wp`, and a caller of `Spec` meets that entry's spec after an update. So the
registration is monotone (`grpcSvcAt_mono_upd`), as `isGrpcRpcMd_mono_upd` is today. -/
def grpcSvcAt (a name : GoString) (Wq Wp : ProtoWire)
    (Spec : GrpcMd → Wq.M → (Wp.M → IProp GF) → (GoString → IProp GF) → IProp GF) : IProp GF :=
  iprop(∃ (Svc : GrpcSvc GF) Spec₀, grpcAddrAt a Svc ∗ ⌜Svc name = some ⟨Wq, Wp, Spec₀⟩⌝ ∗
    □ ∀ md m Φ Ψe, Spec md m Φ Ψe ==∗ Spec₀ md m Φ Ψe)

theorem grpcSvcAt_of_addr (a name : GoString) (Svc : GrpcSvc GF) (e : GrpcEntry GF)
    (h : Svc name = some e) : grpcAddrAt a Svc ⊢ grpcSvcAt a name e.Wq e.Wp e.spec

/-- **Redefined** (every user's statement unchanged): -/
def isGrpcRpcMd {Req Rep : ProtoMsg GF} (addr name : GoString) (Spec : GrpcSpecMd Req Rep) :
    IProp GF :=
  grpcSvcAt addr name Req.wire Rep.wire Spec       -- `Req.wire.M` is `Req.M` by definition
-- `isGrpcRpc`, `isGrpcRpcs`, `isGrpcRpcsMd` and their laws (`_md`, `_mono`, `_mono_upd`,
-- `_singleton`, `_of_all`) keep their text; the `_mono` laws are reproved from `grpcSvcAt`'s wand.

/-- **The server serves `Svc` with Go's chain `ics` and unary registrations `regs`** (persistent;
`Serve`'s obligation): every registered unary method has an entry in `Svc` at its registered
messages' wire parts, and its handler meets that entry's spec as a run (`grpcRunOkMd`, unchanged,
on the server's own heap). Entries without a registration are allowed (their callers get
`Unimplemented`, an error that carries no `Ψe`). A method that no caller of the theorem uses can
have the entry `grpcNoCall := fun _ _ _ _ => False`, which every handler meets. -/
def grpcServes (Svc : GrpcSvc GF) (ics : List GoFunc)
    (regs : List (GoString × GoFunc × GoInterface)) : IProp GF :=
  iprop(□ ∀ (name : GoString) (mh : GoFunc) (srv : GoInterface), ⌜(name, mh, srv) ∈ regs⌝ -∗
    ∃ (Req Rep : ProtoMsgT GF) (Spec : GrpcSpecMd Req.toProtoMsg Rep.toProtoMsg),
      ⌜grpcReqModelOf GF Req.ty = some Req ∧ grpcRepModelOf GF Rep.ty = some Rep⌝ ∗
      ⌜Svc name = some ⟨Req.wire, Rep.wire, Spec⟩⌝ ∗ grpcRunOkMd #mh srv ics Spec)
```

**How a unary call travels.** The model has one stream per connection (`model_transport.go`).

1. **The client dials and exchanges prefaces.** The attempt dials `a` (`dial_au` at the
   `addrProto` inside `grpcAddrAt a Svc`). It gets `connEnd cn false (grpcCliP Svc) (grpcSrvP Svc)
   [] []` and `connFresh cn false`. It writes the preface, which meets `P` on its own, and reads
   the server's `settingsBytes`.
2. **The client registers its slot and writes its request.**
   - `newClientTransportStream` computes the head `fs` with `createHeaderFields`: the credentials'
     metadata, then the context's. This is where `grpcAttemptMd conn om (mdOfFields fs)` gets
     *proved*.
   - It converts the caller's `▷ Spec (mdOfFields fs) m Φ Ψe` into the deposit with `grpcSvcAt`'s
     wand.
   - It registers the slot (`depSlot_register`) with the key `(fs, grpcMsgBytes e.Wq m)`, which
     `Req.send inp m` and the codec give.
   - It writes `headFrame fs`, then the data and close frames (`SendMsg`, `CloseSend`). Each
     write's protocol fact is `grpcAttemptSlot`.
3. **The server accepts and claims.**
   - The server (`handleRawConn` → `HandleStreams`) accepts with `accept_au`, getting
     `connEnd cn true …` and `connFresh cn true`. It writes its preface and reads the head.
   - The protocol fact of `recvTok` gives the slot. `operateHeaders` dispatches, and
     `depSlot_claim` (at the read prefix, `headReady fs`) gives the deposit and `slotRunTok γ`.
   - The data frame's bytes are the key's `bs` (`depSlotOf_agree`). So grpc's decoder stores
     `e.Wq.tree m` (the codec's law, O7), and the run gets `grpcDecOk dec Req m`.
4. **The run answers.** `grpcServes` gives the handler's run contract at the entry. The run (the
   chain, then the handler) returns `Φ m'` with the reply, or `Ψe d` for a handler's error.
   `sendResponse`/`WriteStatus` first answer the slot (`depSlot_answer` at
   `.ok (grpcMsgBytes e.Wp m')` or `.err d`), then write the frame whose protocol fact is that
   `slotDone`.
5. **The client takes the answer.**
   - The client reads the reply's data frame, which gives `slotDone γ (.ok bs')`. `depSlot_take`
     with its token gives `∃ m', grpcMsgBytes e.Wp m' = bs' ∗ Φ m'`.
   - Its decoder stores the tree of the bytes, which is `e.Wp.tree m'` (O7), so it has
     `Rep.recv out m'`.
   - With the OK trailer, `Invoke` returns `nil` and `Φ m'`. On a trailer with a handler's
     description it takes `Ψe d` instead.

**At most once.** This maps the old "one deposit, one run" argument (`InvGrpcRun.lean`'s header)
onto the connection:
- **One run per deposit.** A deposit is in one slot, which belongs to one connection: the slot map
  keeps `connFresh cn false`. The slot is claimed once, because the claim keeps `connFresh cn true`
  (`connFresh_excl`). This is what `grpcReplyTo`'s exclusivity said, now a theorem.
- **(a) grpc's transparent retry.** The model retries an attempt in only two cases:
  - Its head did not reach the server whole (`newClientTransportStream`'s `n < len(b)`). The client
    applies `depSlot_withdraw` at the written `W`, where `¬ headReady fs W`. The attempt's
    `sendTok` is frozen and the connection is closed.
  - The server refused it before dispatch (`REFUSED_STREAM`). The server applies `depSlot_refuse`,
    and the client applies `depSlot_take` at `.refused`.

  Either way, the deposit is back with the client before the retry's new connection registers it
  again.
- **(b) No retry policy, hedging or `healthCheckConfig`.** This stays a premise of the client's
  connection (`grpcResolverAt`'s service config), as now. The proof of the model's `stream.go`
  now uses it rather than citing it: `shouldRetry` has no case for a processed stream without a
  policy.
- **(c) D7 is retired.** D7 said that every connection to a served address is a `NewClient`
  connection, and that grpc makes no calls of its own. Now the net library's protocol binds every
  writer of a connection to `a`, whoever dialed it, and a head of a unary method can be written
  only with a slot.
- An attempt that returns early leaves its deposit in its slot, unclaimed or with the run, as now.

#### 1.3 etcd's side (`Proof/github_com/mit_pdos/etcd_grove/examples/lib/etcdstart/EnvPub.lean`, a defs module)

```lean
/-- **The client-facing view of a member's apply environment** (countable: ghost names, the
member's ids, the modes; O1 fixes its fields). -/
structure EnvView where
  ...
deriving DecidableEq             -- with `Pos.Countable`

/-- The member's environment from its view (the member's construction, `srvEnv`/`env₀`'s). -/
def etcdEnvOf (ν : EnvView) : apply.AEnv GF := ...

/-- Not published yet (exclusive; one per member, from the start). -/
def envPubTok (γE : GName) : IProp GF := dghostVar γE (.own 1) (none : Option EnvView)
/-- **Published: the member's view is `ν`** (persistent, one-shot). -/
def envAt (γE : GName) (ν : EnvView) : IProp GF := dghostVar γE .discard (some ν)
/-- The phrase of #24, over the view. -/
def envAtE (γE : GName) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ ν, envAt γE ν ∗ ⌜E = etcdEnvOf ν⌝)

theorem envPub_alloc : ⊢ |==> ∃ γE, envPubTok (GF := GF) γE
theorem env_publish (γE : GName) (ν : EnvView) : envPubTok γE ==∗ envAt γE ν
theorem envAt_agree (γE : GName) (ν ν' : EnvView) : envAt γE ν ∗ envAt γE ν' ⊢ ⌜ν = ν'⌝

/-- **A spec over the published environment**: its caller's obligation for every view published
at `γE` (the server, which holds `envAt γE ν`, instantiates it at its own). -/
def etcdPubSpec {Req Rep : ProtoMsg GF} (γE : GName) (S : EnvView → GrpcSpecMd Req Rep) :
    GrpcSpecMd Req Rep :=
  fun md m Φ Ψe => iprop(∀ ν, envAt γE ν -∗ S ν md m Φ Ψe)

/-- **What a member publishes for its clients**, fixed by the start (`Pub` is a Lean function of
the view: the putget invariant, the read names, ...): an invariant the start allocates, open to
every client, holding `□ Pub ν` once `envAt γE ν` holds (the member puts it in when it
publishes). -/
def envPubInv (γE : GName) (Pub : EnvView → IProp GF) : IProp GF :=
  inv envPubN (dghostVar γE (.own (1/2)) (none : Option EnvView) ∨ ∃ ν, envAt γE ν ∗ □ Pub ν)

/-- **etcd's service**, as a table: KV, Lease, Cluster, Maintenance, Auth, health's `Check`, and
every other unary method `v3rpc.Server` registers, with `grpcNoCall` for those no client of the
theorem calls. -/
def etcdSvc (γE : GName) (cid mid : w64) : GrpcSvc GF := fun name =>
  if name = go!"/etcdserverpb.KV/Put" then
    some ⟨pbPutRequest.wire, pbPutResponse.wire,
      etcdPubSpec γE (fun ν => (etcdPutSpec (etcdEnvOf ν) (viewRd ν) cid mid).md)⟩
  else if ... else none

/-- **The client's registrations before it knows the view**, and after (clientv3's statements). -/
def kvRegsPub (addr : GoString) (γE : GName) (cid mid : w64) : IProp GF :=
  iprop(isGrpcRpcMd addr go!"/etcdserverpb.KV/Put"
      (etcdPubSpec γE (fun ν => (etcdPutSpec (etcdEnvOf ν) (viewRd ν) cid mid).md)) ∗ ...)
theorem kvRegsPub_at (addr : GoString) (γE : GName) (ν : EnvView) (cid mid : w64) :
    kvRegsPub addr γE cid mid ∗ envAt γE ν ⊢
      client.kvRegsAt ⟨addr, etcdEnvOf ν, viewRd ν, cid, mid⟩
```

`kvRegsPub_at` is `isGrpcRpcMd_mono` with `envAt_agree`:
- Once the client holds the view, it has clientv3's `kvRegsAt`, and every clientv3 spec applies
  unchanged. It gets the view from its first call's `Φ`, which a `Pub` caller writes as
  `∃ ν, envAt γE ν ∗ …`.
- A call made before that is made at the `etcdPubSpec` form. The client proves its obligation for
  an arbitrary `ν` with `envAt γE ν` by opening `envPubInv`: agreement makes the invariant's
  content `□ Pub ν`.

The deployment start (S4's `NetStart`/`ServerStart`, which is kaashoek's) does the setup:
1. It allocates `γE` (`envPub_alloc`) and splits `envPubTok` into the invariant's half and the
   member's.
2. It allocates `envPubInv` and the slot map.
3. It sets the member's client address with `grpc_addr_set a (etcdSvc γE cid mid)`.
4. It hands the member `grpcAddrAt a (etcdSvc …)` and its half of `envPubTok γE`. It hands every
   client `kvRegsPub a γE cid mid` and `envPubInv γE Pub`.

### 2. The specs

#### 2.1 `grpc.NewClient`

The text is unchanged (`Spec/google_golang_org/grpc/NewClient.lean`).
`grpcConn conn addrs ics dopts Ok` becomes a definition (a theorem's post, not an axiom). It is
over:
- the model's `*ClientConn`: its read-only fields (the target's resolved addresses `addrs`, the
  composed chain `ics`, `dopts`, the credentials `credsOfDial ds` with their contract at `Ok`);
- an invariant for its state guarded by `mu` (the idle flag, the set of streams, the resolver's
  state);
- the net library's `regCtx` and the slot map `depSlotsCtx`.

For `connCredsOk` and `credsYield`, see O4.

#### 2.2 `ClientConn.Invoke`

The text is unchanged (`Spec/google_golang_org/grpc/ClientConn__Invoke.lean`). It is proved over the
model's `call.go`, `stream.go`, `model_transport.go` and `model_clientconn.go`, under the net
extension: the spec file gains the section variables `[HasExt netExt] [NetProtoGS] [NetSlotGS]`.

The **new form of `grpcInvokerOk conn addrs Ok inv` is its current text** (`InvGrpc.lean:1895`).
The registration conjunct no longer depends on a heap because of the redefinition:

```lean
def grpcInvokerOk (conn : Loc) (addrs : List GoString) (Ok : IProp GF → Prop) (inv : GoFunc) :
    IProp GF :=
  iprop(□ ∀ (method : GoString) (Req Rep : ProtoMsgT GF)
      (_ : grpcReqModelOf GF Req.ty = some Req) (_ : grpcRepModelOf GF Rep.ty = some Rep)
      (Spec : GrpcSpecMd Req.toProtoMsg Rep.toProtoMsg) (m : Req.M)
      (Φ : Rep.M → IProp GF) (Ψe : GoString → IProp GF) (ctx : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (om : GrpcMd)
      (inp out : Loc) (opts : GoSlice) (vs : List GoInterface) (ps : List Loc) (R : IProp GF),
    {{ ⌜Ok R⌝ ∗ R ∗ isGrpcRpcsMd addrs method Spec ∗ metadata.outMD ctx om ∗
        ▷ (∀ md, ⌜grpcAttemptMd conn om md⌝ -∗ Spec md m Φ Ψe) ∗
        ctxOk ctx cd ∗ Req.send inp m ∗ ⌜Req.wireLen m < grpcMsgMax⌝ ∗
        Rep.own out ∗ opts ↦*□ vs ∗ ⌜∀ v ∈ vs, grpcOptOk ps v⌝ ∗ ([∗list] p ∈ ps, grpcPeerBuf p) }}
      (invokerCall inv #(GoInterface.ok ctx) #method
        #(interface.mkOk (go.GoType.PointerType Req.ty) #inp : GoInterface)
        #(interface.mkOk (go.GoType.PointerType Rep.ty) #out : GoInterface) #conn #opts)
    {{ (err : GoInterface), RET #err; R ∗ Req.send inp m ∗ ([∗list] p ∈ ps, grpcPeerBuf p) ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ m' : Rep.M, Rep.recv out m' ∗ Rep.recvOwn out m' ∗ Φ m') ∨
          (⌜err ≠ GoInterface.nil ∧ clientErr err⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk err ∗
            go_etcd_io.etcd.cache.v3.errCellOk err ∗ Rep.own out ∗ notLearnerErr err ∗
            ∃ d : GoString, go_etcd_io.etcd.cache.v3.descIs err d ∗
            ⌜(kvMethod method ∧ ∀ a ∈ addrs, noRefusalAt a) →
              d ∉ go_etcd_io.etcd.cache.v3.refusalDescs⌝ ∗
            (⌜d ∈ handlerDescs⌝ -∗ Ψe d))) }})
```

What changes is what makes it true:
- The docstring's claims about grpc-go become the proof's, over the model. They are: one write of
  the request, transparent retry only for unprocessed streams, the error types, and the
  credentials running on the caller's goroutine.
- The model's own trusted claim (`models/README.md`: the model behaves as grpc-go does, as the
  program observes it) replaces them.
- A refused dial (no listener yet) is the error arm: `Unavailable`, a description grpc makes.
- The client machine needs nothing of the server's heap: `isGrpcRpcsMd` is `grpcSvcAt` at every
  address.

#### 2.3 `grpc.NewServer`, `Server.RegisterService` (`grpcSrvNew` defined)

The texts are unchanged (`Spec/google_golang_org/grpc/{NewServer,Server__RegisterService}.lean`),
proved over the model's `NewServer`/`register`. The axiom `grpcSrvNew` becomes this definition:

```lean
/-- **The server `gs` being built** (exclusive): the model's `*Server` before `Serve`. Its options
compose the unary chain `ics` and the stream chain `sics` (`chainUnaryServerInterceptors` has
already run: `opts.unaryInt` meets `grpcSrvChainAll ics`, `opts.streamInt` meets
`grpcSrvStreamChainAll sics`). Its services map holds the services `svcs`, whose method and stream
descriptors give exactly `regs` and `sregs` (by `descRegs`/`descSRegs` per service, in order). It
has no listener and no connection, `serve = false`, and its events, wait groups and `cv` are
fresh. -/
def grpcSrvNew (gs : Loc) (ics sics : List GoFunc) (svcs : List GoString)
    (regs sregs : List (GoString × GoFunc × GoInterface)) : IProp GF :=
  iprop(∃ (so : serverOptions.t) (smap : Loc) (infos : GMap GoString Loc) (mu cv : Loc) ...,
    gs ↦ Server.mk so ... ∗ srvOptsOk so ics sics ∗ ownMap smap (.own 1) infos ∗
    ⌜infos.dom = svcs.toFinset⌝ ∗ ([∗map] sn ↦ si ∈ infos, srvInfoIs si sn regs sregs) ∗
    ⌜(regs.map Prod.fst).Nodup ∧ ...⌝ ∗ isMutex mu ... ∗ ... )
```

The helpers:
- `srvOptsOk` comes from S1's `srvOptFnOk` kinds.
- `srvInfoIs si sn regs sregs` describes the `serviceInfo`'s `serviceImpl` and `streams` map: the
  entries of `regs`/`sregs` whose names have the prefix `/sn/`, with unary methods wrapped by
  `wrapUnaryHandler` as the model does.

`RegisterService`'s `⌜sn ∉ svcs⌝` premise and `Serve`'s joint `Nodup` stay.

#### 2.4 `Server.Serve` and `grpc.start`

```lean
/-- **The right to serve `gs` on the listener `lis` at `a`** (redefined; it was the link, the
configuration and the size premise): the server built, the node's open listener at `a` (the net
library's), the address serving `Svc`, the server serving `Svc`, the stream half's facts (§2.6),
the names jointly distinct, and the replies' size premise. -/
def grpcServeTok (gs : Loc) (lis : GoInterface) (a : GoString) (Svc : GrpcSvc GF) : IProp GF :=
  iprop(∃ (ics sics : List GoFunc) (svcs : List GoString)
      (regs sregs : List (GoString × GoFunc × GoInterface)) (l : w64),
    grpcSrvNew gs ics sics svcs regs sregs ∗
    isListener lis l ∗ netLis hL l a true ∗ netLisAt hL l a ∗
    grpcAddrAt a Svc ∗ grpcServes Svc ics regs ∗ grpcStreamHalf a sics sregs ∗
    ⌜((regs ++ sregs).map Prod.fst).Nodup ∧ grpcRepliesFit⌝)

abbrev grpc.Server.Serve.spec : Prop :=
  ∀ (gs : Loc) (lis : GoInterface) (a : GoString) (Svc : GrpcSvc GF),
  {{ grpcServeTok (GF := GF) gs lis a Svc }}
    (App (Val (gs @!! go.GoType.PointerType google_golang_org.grpc.Server.ty @!! go!"Serve"))
      (Val #lis))
  {{ (err : GoInterface), RET #err; True }}
```

`Serve` is now the model's code with its body, no longer the trusted `Server.Serve.impl`. The path
is `server.go`'s `Serve` → `handleRawConn` → `serveStreams` → `HandleStreams` → `handleStream` →
`processRPC`. The proof's invariants:
- Per accepted connection: §1.2's steps 3-4.
- Per server: `gs`'s maps guarded by `mu` (listeners, connections), the wait groups (thread tokens,
  `notes/bounds-plan.md`), and `quit`/`done`.

`grpc.start` is no longer the unary half's axiom: the unary half reads none of what it made
(`grpcAddrIs`, `grpcSrvCfg`, the link). It survives only narrowed to the stream half (§2.6).
`grpc.start'` and `grpc.serve` (theorems today) are replaced by two things: introducing
`grpcServeTok`, which is a definition with nothing to prove, and `grpcSvcAt_of_addr`.

#### 2.5 The stage-B leaves

| Leaf | In S2 |
|---|---|
| `grpc.model.acceptRun` | **Retired.** Its unary arm becomes `Serve`'s proof over the model. Its stream arm becomes §2.6's axiom. |
| `grpc.model.acceptRunConns` | **Retired.** The model's open connections keep serving in their own goroutines, so there is no `lisFailed` composite. |
| `grpc.model.respond` | **Retired.** It becomes `processRPC`'s `sendResponse`/`WriteStatus` over the model's transport, which answer the slot. |
| `grpc.model.finishStream` | **Retired** with the trusted `Serve`: the model's `processRPC` ends a stream. §2.6's axiom covers what the stream handler's return needs. |
| `Server.Serve.impl` (the trusted model), `model.runCall`, `model.serveRest`, the old form of `grpcServeTok` | **Retired.** |

#### 2.6 The stream half, until S3

A head of a stream method carries no slot (the `unaryOf … = false` arm of `grpcCliP`). The
server's proof of `processRPC` at a stream descriptor uses one narrowed axiom: the old pair's stream
arm, moved to the point of dispatch.

```lean
/-- **A dispatched stream** (an axiom until S3): on the server `γ` with Go's configuration `c`
(`grpcSrvCfg`, made by the narrowed `grpc.start`), a stream that the model's `HandleStreams`
dispatched for a path in `c.sregs` gives `processRPC` what `grpcAccepted`'s stream arm gives today:
the deposited stream registration (`isGrpcStreamAt γ name Up Spec`), the shared `□ Spec md γs Dn`,
the raw server end with both tokens at `[]`, grpc's composed stream interceptor, and `info`. -/
axiom grpc.streamDispatch ... :
  grpcSrvCfg γ c ∗ srvStreamHead st cn fs ∗ ⌜pathOf fs = some name ∧ name ∈ c.sregs.map Prod.fst⌝ ⊢
    |={⊤}=> grpcAcceptedStream γ c name st ...

def grpcStreamHalf (a : GoString) (sics : List GoFunc)
    (sregs : List (GoString × GoFunc × GoInterface)) : IProp GF :=
  iprop(∃ γ ics regs, grpcAddrIs a γ ∗ grpcSrvCfg γ ⟨ics, sics, regs, sregs⟩)
```

Its soundness argument is the stream bullet of "The pair". It is sound only where the client's
`NewStream` runs on the server's heap. `NewStream` is still an axiom, consuming
`grpcAddrIs a γ ∗ isGrpcStreamAt γ …`, and a stream registration is a WP of the server's handler,
so no other machine can hold one. Streams across machines (watch, lease keep-alive) wait for S3.

### 3. What changes for existing users; the axioms

**clientv3** (`Proof/go_etcd_io/etcd/client/v3/*`, 21 files mention `isGrpcRpc*`). No statement
changes:
- `isGrpcRpcMd` is redefined; `kvRegsAt` and the client specs keep their text.
- Proofs that use `isGrpcRpcMd_mono`/`_mono_upd`/`isGrpcRpcs_*` keep them; the laws are reproved.
- Two proofs outside grpc's files unfold `isGrpcRpcMd` down to `grpcAddrIs`/`isGrpcRpcAt`:
  - `InvLeaseGrant.lean:200`'s `isGrpcRpc_mono_with` (monotone with a persistent context). It is
    reproved from `grpcSvcAt`'s wand, with the persistent fact framed into it. Its statement stays.
  - `cluster3/Defs.lean:258-270` (the bridges' `grpcAddrIs` forwarding). This goes with O5.
- If O4 makes `grpcAttemptMd` an `IProp`, its users (the auth clients' `connCredsOk` proofs) change
  one premise.

What is new in etcd's files is §1.3.

**v3rpc's server** (`v3rpc.Server`). Its post (`grpcSrvNew` with etcd's `regs`) is unchanged, and so
are its handlers' proofs (`grpcMethodOkMd`, the adapter `grpcRunOkMd_of_pools`). The new
obligation, which goes in `etcdstart`, is `grpcServes (etcdSvc γE cid mid) ics regs`:
- from each handler's `grpcRunOkMd` at `etcdPutSpec (etcdEnvOf ν) …`, with `envAt γE ν`, by
  `grpcRunOkMd_mono` through `etcdPubSpec`;
- with `grpcNoCall` entries for the rest.

**`etcdstart`** (`Serve`, `Served`, `etcdKVAt_regs`, the callers in cluster3). Today the spec of
`etcdstart.Serve` *produces* `kvRegsAt` on the member, through `grpc.start'`/`grpc.serve`. Now:
- It takes `grpcAddrAt a (etcdSvc γE …)`, the member's half of `envPubTok γE`, and
  `envPubInv γE Pub`.
- It publishes (`env_publish`, putting `□ Pub ν` into the invariant) and returns `envAt γE ν`.

The single-process examples (the eleven of `etcd_safe`) need the net extension in their programs
and the start of §1.3 (`addrs_start`, `netProto_alloc`, `depSlots_alloc`). This is the plan's
coupling 2, under the user's decision of 2026-11-22 (one machine per member). An interim statement
on one machine, over `goose_dist_adequacy`, keeps their shape.

**Retired by S2** (from `etc/tcb-baseline.txt` and the trusted texts):
- `grpcSrvNew` (an axiom, now a definition);
- `grpcReplyTo`, `grpcSrvLink`, `grpcConnsLink`;
- `grpc.model.acceptRun`, `grpc.model.acceptRunConns`, `grpc.model.respond`,
  `grpc.model.finishStream`;
- `grpc.NewServer`, `grpc.Server.RegisterService`, `grpc.NewClient`, `grpc.ClientConn.Invoke`;
- `grpcConn` and `grpcConn_persistent` (now definitions);
- `grpcWrotePeer` (now a definition: the model's transport writes the peer);
- `credsYield` (opaque, now defined; O4);
- the trusted `Server.Serve.impl`;
- the world premise D7. It is no axiom, but a claim the proof cited that is no longer needed.

Of the vocabulary, `isGrpcRpcAt` and `grpcServerAt` lose their unary role: `isGrpcRpcAt` is
deleted, and `grpcServerAt` goes with `grpc.serve`.

**Kept by S2:**
- `grpcAddrIsRaw`, `grpcSrvCfgRaw`, `grpcAddrIs_agree`, `grpcSrvCfg_agree`, and `grpc.start`,
  narrowed to the stream half only and taking the net extension's listener in place of
  `netListenerAt`;
- the new `grpc.streamDispatch`;
- `ClientConn.NewStream` and the stream ends (S3);
- the codec (`grpcProtoCodec`, the laws of the decoder and the marshaller: O7), until phase 5's
  `PbCodec`;
- `grpcRepliesFit` (a named workload premise), and `noRefusalAt`/`noOtherRefusalAt` (opaque
  premises);
- `grpcResolverAt` and `etcdResolver_grpc` (grpc3), `WithKeepaliveParams`, `grpcStatsHandlerOk`,
  `grpcHealthSrv`, `promSrvMetrics`;
- the per-type registration axioms (`pb*T_reg`).

**Possibly added:** init axioms of `mem`, if its pools are translated with initializers that do not
translate. S1 avoided that, and S2 should too.

### 4. Open questions

- **O1. The view.** Two things to find out:
  - Which fields of `AEnv` the client-facing specs read: `etcdPutSpec`, `etcdRangeSpecE`,
    `putReplied`, `rangeReplyOk`, ... use `E.γs`, and what else?
  - Whether the member's `E` is a function of countable names (`etcdEnvOf ν`), with its predicate
    fields (`Nx`) fixed definitions over them.

  If a client-facing spec reads a predicate field that cannot be defined from names, that field
  needs a saved predicate beside the view (`savedPredOwn` over a countable domain, such as `Nx` over
  `mvcc.Log`).
- **O2. Specs in the table must not depend on a heap.** `#check @client.etcdPutSpec`, and the same
  for the others in `etcdSvc`, must show no `HeapGS` argument. The auth-on specs
  (`etcdPutSpecOn s E …`, over the server location `s` through `v3rpc.kvOpAuOn`) are suspect. A
  spec that needs the server's heap has to be split: the heap part stays in the server's run
  contract (`grpcMethodOkMd`'s bundle), and the client sees only ghost state.
- **O3. `tree` into `ProtoMsg`.** The change is mechanical: each `pbX` model defines its tree, and
  `ProtoMsgT` becomes an abbreviation. It touches every message model. The alternative is for
  `isGrpcRpcMd` to quantify over the trees (`∃ tq tp, grpcSvcAt … ⟨Req.ty, Req.M, tq⟩ …`). That
  needs a registry of trees per Go type, independent of the heap, so that the client's `Req.tree`
  can be shown to be `tq`: more trust, not less.
- **O4. `credsYield`.** The attempt contract's `grpcAttemptMd conn om md` rests on the opaque
  `credsYield conn cm`, which the proof over the model cannot produce. Two options:
  - **Proposal:** an `IProp` `credsYieldI conn cm`, persistent: `cm` is in a ghost set of the
    connection's credential outputs, which `grpcConn` names and whose invariant ties it to
    `connCredsOk`'s `□ Q cm`. `grpcAttemptMd` becomes an `IProp` premise in `grpcInvokerOk`, so one
    premise changes for its users.
  - Keep `credsYield` Prop-valued, defined by the connection's list of credentials. This works only
    if every user needs only `connCredsOk`'s `[]` case (to check).
- **O5. Bridges.** `bridge.New` (the partition examples, linkv3p) forwards bytes between two
  connections. The client's slot is on the client→bridge connection, but the server claims on the
  bridge→server one. A bridge proof would claim on one side and re-register on the other, at the
  ghost level, once the forwarded bytes hold a whole head; the bridge's address serves the target's
  `Svc`. Until then the bridged examples keep their current axioms (they run in one process).
- **O6. Wildcard listeners** (branch `net-wildcard-listen`, `02fae64e64`, not yet on `lean`). A
  wildcard listener accepts on every address of its port (`lisAccepts`). `grpcServeTok` then needs
  `grpcAddrAt a' Svc` for each accepted address `a'`, with one `Svc` for all of them. `grpcSvcAt` is
  keyed by the dialed string, as `grpcAddrIs` is today.
- **O7. The codec.** The deposit's bytes are `pbEncodeTree (tree m)`. S2 needs two facts about
  grpc's codec:
  - marshalling a sender's `*T` holding `m` produces those bytes;
  - unmarshalling them is `storeInto ty l t`, where `pbEncodeTree t = bytes` determines `t` (decode
    after encode is the identity on trees).

  Phase 5's `models_lab.pbcodec` proves this for its own codec, but grpc's default codec is
  protobuf-go's. So S2 either installs that codec as the model's default (as phase 5 item 1 plans
  for `grpcProtoCodec`) or keeps the codec's two laws as axioms.
- **O8. The mask of `grpcDeposit`'s update.** The deposit is `▷ |==> spec`, from `grpcSvcAt`'s `==∗`
  wand. If converting a spec needs an invariant, the wand must be `={⊤}=∗` and the mask of the
  claim law adjusted. Opening `envPubInv` does not count: the *client* does it before depositing.
- **O9. One machine in the interim.** Until S4, S2's theorems can serve the single-process examples
  only by adding the net extension to them (coupling 2). Whether kaashoek's `NetStart`/`ServerStart`
  lands first decides whether S2 states anything for `etcd_safe`, or only for putget-dist.

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
