# Repair: group `grpc-v3rpc` (2026-11-09)

Owned: `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/`, `Spec/go_etcd_io/etcd/api/v3/
{etcdserverpb,v3rpc,version}/`, `v3lock/v3lockpb`, `v3election/v3electionpb`, `Spec/google_golang_org/`,
`Spec/net/http`, `Spec/sort`; snippets `examples/specreq/{v3rpc,v3rpcwatch,etcdserverpb,grpc}`.
Reports: `A6-grpc-boundary-provability.md` (P-), `A6-grpc-boundary-completeness.md` (C-),
`A2-client-watch-lease-completeness.md` F2; coordinator-routed requests (raft-conf-pb, mvcc,
client-watch).

## First tier

### P-F2 `endsDecoded`/`decodedAt` inconsistent — fixed, more broadly than suggested

The reviewer's counterexample holds, and there is a deeper one independent of `decodedAt`:
`Proto.Content` was "up to `proto.Equal`", while W0's models distinguish a `nil` range end from a
non-`nil` empty one (`endOf`). `proto.Equal` of a `RangeRequest` with `RangeEnd: nil` and one with
`RangeEnd: []byte{}` is `true` (both fields unpopulated), so `Equal.spec` gave the two contents
equal, `holds_fun` the two models equal, and `rangeReqOwn_unfold` `[] = [0]`: `False` from a
terminating program, with no `decodedAt` at all. Fix (`Spec/google_golang_org/protobuf/proto/`):

- `Content` holds Go values (no longer up to `Equal`); new opaque `norm c` (the wire view: every
  proto3-unset field at its zero Go value), `norm_facts`, `encodes_norm`, `encodes_fun` up to `norm`,
  `encodes_marshalOk` (second tier: invalid UTF-8 encodes no content), `msgAt_split`, `noFloats`.
- `decodedAt` removed; a decoded content is canonical, `⌜norm c = c⌝` (`Unmarshal.spec`, grpc's
  `decOk_call`, `srvRecv_recv`, `cliRecv_recv`).
- `Equal.spec`: `b = true → norm c = norm d`, converse under `noFloats t` (second-tier NaN fixed).
- `Clone.spec`: the copy holds `norm c` (protobuf-go's merge skips empty proto3 fields).
- grpc transports wire views (`Spec/google_golang_org/grpc/Api.lean`): `attemptOk_call`'s caller
  hands `S md (norm c) Φ`, `unaryOut` gives `Φ (.ok (norm c))`, `cliSend_send`/`srvSend_send` take
  `S.up/dn … (norm c)`.
- 3h (`etcdserverpb/Api.lean`): pure opaque `endsOk c` (every range end `nil` or non-empty),
  `endsOk_canon`, `endsOk_range_intro` (a model end other than `"\x00"`: replaces the address-keyed
  intro), and **`endsDecoded t p` redefined (transparent) as `∃ dq c, msgAt t p dq c ∗ ⌜endsOk c⌝`**:
  tied to a share of the message, so a holder cannot rewrite the field; same arity, so 2c's
  `Range`/`RangeStream`/`Txn` statements stand. Not persistent (persistent at `DFrac.discard`:
  `endsDecoded_ro`). Laws `endsDecoded_range/delete/compare` give it back; `endsDecoded_txn`/`_op`
  split it into `opsDecoded`/`cmpsDecoded` (now share-carrying) with wands back.
- `holds_norm.spec`: every response/event relation is kept by `norm`; request relations (and
  `compareHolds`, `requestOpHolds`, `watchReqHolds`) under `endsOk c`. A non-`nil` empty end is
  read as the key alone over gRPC: the client already excludes it (`OpM.emptyEnd`,
  `nonissues/etcd-client-withrange-empty-end.md`).
- v3rpc: `HandlerTriple`/`icEtcdOk` take `⌜norm c = c ∧ depth c < depthMax⌝` in place of
  `decodedAt`; the 15 generated `_*_Handler` specs likewise; `kvServer.RangeStream.spec`.

### P-F3 `FromOutgoingContext` nil map + `MD.Set` — fixed

`FromOutgoingContext.spec`: `⌜(ok = false → m = null ∧ md = []) ∧ (ok = true → m ≠ null)⌝`
(`mdAt` of the `nil` map still given: reads are fine). `MD.Set.spec` takes `m ≠ null`;
`MD.Copy`, `Pairs`, `New` give a non-`nil` map. Snippet `grpc/metadata-out` copies first: unchanged.

### P-F4 log interceptor needs the request after the handler — fixed

New `reqBack reqT q := ∃ dq c', msgAt reqT q dq c' ∗ ⌜depth c' < depthMax⌝`; `HandlerTriple`'s
post and `icEtcdOk`'s continuation posts carry it (any share: 2c's `LeaseGrant` writes the ID, and
`endsDecoded` keeps part of the share). Handlers give back the share 2c's `SrvCallTriple` returns.

### P-F5 Compact's admin denial — fixed in 2a, W0 request

`AuthAdmin.isPermitted.spec`'s error post is now a token refusal (`invalidAuthToken`) or
`∃ σ e, etcdLb γ σ ∗ ⌜adminDenied σ who e ∧ srvErrOf err e⌝`, with `V3rpc.adminDenied` the shape
3d's `adminPost` gives (the flag on at one table, the user absent or not root at another).
W0's `.compact` denial is at one table, which the code does not give (`IsAuthEnabled` and the user
read at two moments): **request to client-core (W0)**. `kvServer__Compact.lean`'s stale sketch
updated.

### P-F6 reply depths; Txn at `maxTxnOps` — fixed differently

- `holds_depth_resp.spec` (3h): put/delete/compact replies ≤ 2, header/kv ≤ 1, `ResponseOp` ≤
  `respOpDepth`, `TxnResponse` ≤ `txnRespDepth` (new pure functions over W0's models).
- The off-by-one is protobuf's limit, not etcd's: `unmarshalPointer` decrements the budget at the top
  level too and fails below `0`, so depth ≤ 10000 decodes (`protobuf@v1.36.12/internal/impl/
  decode.go:105`). `Proto.depthMax` is now `10001` (`depth c < depthMax` = at most 10000 levels);
  `maxTxnOpsMax` stays 4999 (no stricter configuration premise), and a reply at `2L+2 = 10000` fits.

### P-F7 client→grpc leg — fixed for 2a/3h's slots; requests for 1c's

- `Realize.lean`: `unaryArgs_msgAt.spec` (the realization of 1c's `unaryArgs` slot: method
  `methodOf rq`, request/reply messages of `reqType rq`/`replyType rq`, `reqModels`, `endsOk`, the
  compaction's `r ≠ 0`, `R` of each reply answer from `ansContent`), `grpcCallOptsOk_unfold.spec`,
  `grpcConnAt_of.spec`; pure `svcOf`, `methodOf`, `replyType`, `ansContent`.
- `reqRight`: `etcdUnary`'s second way gives `reqRight γ rq` back with the update.
- **Requests to client-core** below: `connOk` laws, `AttemptTriple`/`uiOk_call` carrying `reqRight`.

### P-F1 `hdr.fill` on a `nil` header — fixed with server-core

server-core's replies are now `srvHdrReply` (`replyHdrOwn`); the lease handlers' sketches cite
`replyHdrOwn_header` (a non-`nil` header to fill) and `replyHdrOwn_replyOwn`. The `Alarm` half of
the finding was wrong: `maintenanceServer.Alarm` replaces a `nil` header with
`&pb.ResponseHeader{}` before `fill` (`maintenance.go:263-265`, checked).

### server-core's late requests — done

`togRPCError`, `AuthAdmin.{requireAuthInfo,isPermitted}`, `authMaintenanceServer.{requireAuthInfo,
isPermitted}` and the Api text moved from the pure `srvErrOf` to the persistent `srvErr err e`
(values through 2c's `sentinelAt`); the handlers' sketches cite `srvErr`, 2c's
`EtcdServer.MemberList`, `CommittedIndex`/`Backend`/`Config`/`ClusterVersion`, `MoveLeader`,
`Downgrade`, `AuthStore` specs. v3rpc rebuilt: OK (115 modules).

### P-F8 range-stream records — fixed

`chunk_msgAt.spec` (3h: a `RangeStreamResponse` carrying a chunk has a non-`nil` `RangeResponse`
holding it, through W0's `rangeRespOwn`); `rsSink_send.spec` takes `⌜∀ m0 ∈ ms, m0.hdr = none⌝`
(so `rsChunk_hdr_last` is realizable); `headerFillingRangeStream.Send`'s sketch updated.
2c's `RangeStream` must establish the premise (it puts the header on its last chunk only):
**request to server-core**.

### P-F9 / open question 7.4 — stays open (what it blocks below)

### P-F10 snippets — fixed

- `v3rpc/kv.go` `refusalOrIndefinite`/`indefinite`: every `EtcdErr.refusal` and every mapped
  indefinite error (`ErrNotLeader`, `ErrUnhealthy`, `ErrClusterIDMismatch`, ...).
- `ReqRangeStream`: `Assumes: prefix non-empty`, and an early return for `""`.
- `v3rpcwatch/serve.go`: `Assumes` states `srvBuild gs B` and the service unregistered.
- `go vet ./specreq/{v3rpc,v3rpcwatch,grpc,etcdserverpb}/...`: clean.

### C-F1 missing stubs/handlers — done by a sub-agent (see "Completeness, sub-agent" below)

### C-F2 / A2-F2 Kubernetes' dial options — fixed

New assumed specs `WithChainUnaryInterceptor`, `WithChainStreamInterceptor`, `WithStatsHandler`,
`WithContextDialer`, each a `dialOptAt v (fun cfg => cfg)` under a premise on its argument
(`cliIcPass`, `cliSicPass`, `statsOk`, `ctxDialerOk`; `cliIcPass_call` is the unary one's WP
meaning). They feed client-core's existing `dialOptsOk_neutral`, so no `DialCfg` chain model was
needed (chosen differently from the reviewer: a pass-through interceptor is, for every call, the
rest of the chain; the reviewer's `uis : List val` would change `connAt`'s arity in other groups'
files for no extra guarantee). Snippet `grpc/kube-dial-opts` (`examples/specreq/grpc/dialopts.go`).
The server's `StatsHandler.spec` now takes `statsOk h` too (a panicking handler broke its claim).

### C-F3 `grpc.Peer`, `Peer.String`, `peerOk` — sub-agent (below)

### C-F4 Election/Lock registration — fixed

`etcdContract` has the election service's `Campaign`/`Proclaim`/`Leader`/`Resign` (`etcdLocal`),
`Observe` (`snapSpec`) and the lock service's `Lock`/`Unlock` (`etcdLocal`): their handlers run over
the in-process `v3client` (open 1.5) and no gRPC client of them is in scope, so a member promises
only that a run returns. New `RegisterElectionServer.spec`, `RegisterLockServer.spec` (WP form),
`electionDesc_init.spec`, `lockDesc_init.spec` (descriptor initializers are untranslated: facts as
`EtcdServerPb`'s). The `regsOk` extension needs no law (`regsOk` is a `[∗list]` over the
registrations); 2e's handler specs give each `unaryOk` at `etcdLocal`.

### C-F6 dropped specs — sub-agent (below)

### C-F7 `ansOutcome`'s Unknown — fixed

New `V3rpc.errCode e` (`Unknown` only for `memberNotEnoughStarted`, `tooManyRequests`, the two
`EtcdError`s of `toGRPCErrorMap`); `ansOutcome`, `etcdUnary`'s second way and `togRPCError.spec`'s
post pin the code to it.

### C-F8 `version.LessThan` over any `val` — not fixed

`semver.Version` is not translated (no Lean type to quantify over); the spec is assumed and Go's
type checker admits only `Version` arguments. Recorded in its Margin is the honest fix: name the
type in the Goose configuration.

### Brief item 3: sentinel errors — checked, no change

rpctypes' client-side mapped `Err*` are `EtcdError` **struct values** (`Error(ErrGRPC*)` returns
`EtcdError{code, desc}`), compared by value: equating them with the Lean constant `errVal e` is
right. The `ErrGRPC*` are status pointers and `init.spec` already gives them existentially; their
pairwise distinctness follows from `statusErr_agree` and `desc_inj`.

## Coordinator-routed requests

- **raft-conf-pb (A5-compl F4)**: `Unmarshal.spec` (success) and `Clone.spec` now return
  `Proto.mergeDst t p c` (freshly allocated: slices owned to capacity); `mergeDst_msgAt` gives the old
  `msgAt (own 1)`. Callers that needed `msgAt` apply that law.
- **mvcc**: `ApiWatch.lean`'s "Open (3f's reader tokens)" replaced by 2d's `srvReader_mvcc.spec`;
  `recvLoop`'s sketch treats mvcc's closed-stream refusal of `Watch` as its error branch (the loop
  holds no `wsOpen`: the receive goroutine outlives the run).
- **client-watch**: `NewKVClient`/`NewLeaseClient`/`NewAuthClient`/`NewWatchClient` now take the
  client `c` (`clientConnOk c γ who`, `c.conn ↦□ conn`) and give `□ (clientReady c -∗ remote*At v γ
  who)`; `sendFragments`/`sendLoop` sketches cite the fragment-agreement rule and mvcc's `wStep`
  unconditional event clause.

- **server-boot**: `V3lockpb.resp_unfold`, `V3electionpb.resp_unfold` (the replies' header and
  fields, the converse of `resp_fold`); `V3electionpb.observeStreamAt ss ctx` (opaque, its
  realization grpc's generic server stream and send half under the service's trivial contract) with
  `observeStream_send.spec` (`Send` of a `leaderResp`) and `observeStream_context.spec`, so
  `electionServer.Observe` can get a spec.
- **client-core** (`repair-client-core.md`, "Requests to grpc-v3rpc"):
  1. `via`: `NewLeaseClient`'s post adds `□ ∀ ep, grpcConnVia conn ep -∗ remoteVia v ep`;
     `Realize.lean`'s `grpcConnVia_unfold.spec` realizes 1c's slot (a connection whose resolver
     reports `ep` alone), from which `AttemptTriple`'s `viaFact` follows (the member at `ep`'s
     `leaseFact` in `etcdUnary`). The stubs pass `via` through unchanged (`unaryStubWP` is WP form).
  2. Readiness: every `New*Client` gated (done, with client-watch's W3).
  3. Dial options: done (C-F2); no chain in `DialCfg` (see C-F2 for why): `dialOptsOk_neutral`
     applies to the four new options.
  4. Realization text for `errorsIs_callErr_eof`, `callErr_errorsNew`'s `io.EOF`,
     `wireStreamAt_recv`'s non-EOF error and `protoRest_persist`: `Realize.lean`'s header.
  5. `ClientConn__Invoke.lean`: the nonexistent `servesAt_serves` replaced by `servesAt_addr`.
  6. `fmt.Sprintf("%+v", md)`: fmt is client-core's; its triple belongs with theirs (it reads the
     map through `Grpc.mdAt_ownMap`): not added here.

## Second tier

- `mdSeen` order: `mdSeen (mdc ++ md0) md` (credentials first, grpc-go's order) in
  `attemptOk_call`, `streamerOk_call`, `V3rpc.mdPrin_of` — fixed.
- `Proto.Equal` NaN, `encodes`/UTF-8 (`encodes_marshalOk`), `decOk_call`'s closed world (docstring)
  — fixed.
- `start`'s pool: `GracefulStop` gives back `threadToks n` with the run resources — fixed.
- `icChain [] ic`: `icChain_nil.spec` — fixed. `ownErr_sent` in the header: removed (derivable).
- `sicEtcdOk`'s meaning: **not fixed**. Stating it transparently needs grpc laws for a wrapped
  server stream (`newStreamInterceptor` wraps it with a context canceled on leader loss; the halves
  and `streamOut` would have to transfer between the wrapper and the stream). Left opaque; its
  intended meaning is the docstring. `metricsOk_stream` (assumed) still produces an undefined
  predicate: recorded.
- `LeaseKeepAlive`'s leaked loop sending after the run: unchanged (recorded open 3.6).

## Open question 7.4 (untranslated handlers): what it blocks

The generated handlers of the untranslated methods (`_KV_RangeStream_Handler`, 11 `_Auth_*`,
`_Cluster_*`, `_Maintenance_*`) and stubs now have specs (stated in WP form), but their **proofs**
need the bodies translated. Until then: `Server.spec`'s `regsOk` for those registrations,
`Grpc.start.spec` downstream, `NewKVClient`'s `RangeStreamTriple`, `NewAuthClient` (11 methods),
`NewClusterClient`, `NewMaintenanceClient`, and the snippets `v3rpc/range-stream`, `v3rpc/serve`,
`etcdserverpb/sort-names` rest on assumed-shaped statements of generated code.

## Requests to server-core

1. **P-F1**: done by server-core (`srvHdrReply`, `replyHdrOwn_header`); withdrawn.
2. **P-F8**: `EtcdServer.RangeStream`'s proof must meet `rsSink_send`'s new premise
   `⌜∀ m0 ∈ ms, m0.hdr = none⌝` (only the last chunk has a header); sketch only.
3. **P-F2**: the sketches of `EtcdServer__Range.lean`, `__RangeStream.lean`, `__Txn.lean` cite
   `Proto.decodedAt`/`endsDecoded_of_decoded`/`endsDecoded_range_intro`, now `⌜norm c = c⌝`,
   `endsDecoded_of_canon`, `endsOk_range_intro`; `endsDecoded` is a share (not persistent): the
   proofs consume it, or use `endsDecoded_ro` at `DFrac.discard`. Statements unchanged.

## Requests to apply-txn

1. **P-F2**: `apply/Api.lean`'s provisional `endsDecoded rt` / `opsDecoded sl` (persistent,
   `reqMsgAt_endsDecoded`): realize them as 3h's `□ EtcdServerPb.endsDecoded TxnRequest.ty rt`
   (`endsDecoded_ro`, the entry being read-only) and the persistent closure of 3h's `opsDecoded`;
   3h's `opsDecoded` is no longer persistent itself.

## Requests to client-core

1. **P-F5 (W0, `api/v3/Model.lean`)**: `.compact`'s denial disjunct at two tables, as `V3rpc.adminDenied`
   (the flag on at `af`, the user absent or not root at `ax`), like the reads' `deniedSince`.
2. **P-F7 (`client/v3/Api.lean`)**: laws for 1c's `connOk`: `connOk_elim : connOk conn γ who ⊢ ∃ A ui si,
   Grpc.connAt conn A (some ui) (some si) (Credentials.credMD γ who) ∗ … ∗ □ (∀ ep, A ep -∗
   servesAt γ ep)` and its introduction from `Grpc.NewClient.spec`'s post (in `Client.dial`).
3. **P-F7 (`ApiClient.lean`)**: `AttemptTriple` and `uiOk_call` take `reqRight γ rq` in the pre and
   give it back in the unfired outcome (token/learner refusal), as `etcdUnary`'s second way now does.
4. **C-F2**: `otelgrpc.NewClientHandler`/`NewServerHandler` (otel's owner) give `Grpc.statsOk`; the
   `dialOptsOk` docstring can drop "need 2a's model of chained interceptors first".
5. A law `clientConnOk c γ who ⊢ ∃ conn, c.conn ↦□ conn ∗ connOk conn γ who` if not already
   present (what the stub constructors' new pre needs from `RetryKVClient` etc.).
6. Sketches citing grpc's transport: the server receives `norm c` (`holds_norm` with `endsOk`,
   which `OpM.emptyEnd` gives); `Proto.Clone` of a `Compare` gives `mergeDst … (norm c)`.

## Requests to raft-conf-pb, backend-schema, lease-auth, mvcc, server-boot (owners of message relations)

`Proto.Content` is no longer up to `proto.Equal`: a relation `xModels c m` used across `Clone`, a
`Marshal`/`Unmarshal` round trip or gRPC needs `xModels c m → xModels (Proto.norm c) m` (true when
the model does not distinguish a `nil` field from an empty one), and `encodes_fun` now gives
`norm c = norm c'` (an `Unmarshal`ed content is canonical, so `c' = norm c`).

## New decisions

- **`Proto.Content` holds Go values; the wire carries `norm c`.** Quotienting by `proto.Equal` was
  inconsistent with W0's `endOf` (nil vs empty end). Every owner of a message relation must now say
  its model survives `norm` (one law each); a model that distinguishes `nil` from empty (W0's range
  ends) survives only under `endsOk`.
- **`depthMax = 10001`.** protobuf-go decodes 10000 levels, not 9999; the old bound was one too strict
  and made the transaction reply at `--max-txn-ops = 4999` unsendable in the spec.
- **Election and lock services under `etcdContract` with trivial contracts**, rather than a contract
  sum `etcdContract ⊕ X`: simpler, and nothing in scope calls them over gRPC.

## Completeness, sub-agent (C-F1, C-F3, C-F6)

- **C-F1, fixed (specs stated; proofs wait on 7.4).** `etcdserverpb/StreamShapes.lean`
  (`serverStreamStubWP`, `serverStreamHandlerWP`, for server-streaming RPCs); WP-form specs of the
  11 missing `authClient.*` stubs and `_Auth_*_Handler`s, `clusterClient.*` and `_Cluster_*_Handler`
  (5), `maintenanceClient.*` and `_Maintenance_*_Handler` (7 unary + `Snapshot`),
  `kVClient.RangeStream`, `_KV_RangeStream_Handler`, `NewClusterClient`, `NewMaintenanceClient` (in
  the clientReady-gated shape). `kvDesc_init`, `authDesc_init`, `otherDescs_init` now name every
  handler (the descriptor initializers are translated in `chunk0`, with the names): no unknown
  handler lists remain, so `regsOk`'s obligations are all stated. `descStreams_init` covers
  `KV_ServiceDesc.Streams[0]` and `Maintenance_ServiceDesc.Streams[0]`. Snippet `v3rpc/range-stream`
  cites the new stub and handler specs.
- **C-F6, fixed.** `grpc/grpclog/SetLoggerV2.lean`, `grpc/health/grpc_health_v1/
  HealthCheckResponse_ServingStatus__String.lean`, `etcdserverpb/RangeRequest__String.lean`,
  `AlarmType__String.lean` (ASCII post), `NewLoggableTxnRequest.lean` (returns `stringerAt s ∗
  (stringerAt s -∗ msgAt TxnRequest r dq c)`), `etcdserverpb/Stringer.lean` (`stringerAt`, not
  persistent; `stringerAt_call`, `stringerAt_msg`, `stringerAt_discard`).
- **C-F3, fixed.** `grpc/peer/Api.lean` (`addrOk`, `authOk`, `peerFieldsOk`; `peer_persistent`,
  `peer_nil`, `addrOk_string`, `authOk_authType`, `peerOk_fields`: a `peerOk` peer's fields print,
  `Addr` non-`nil`, what `interceptor.go:106` needs); `peerVar_inv` moved there, field by field (the
  old one in `grpc/Api.lean`, over a `*Peer` variable, was false for `var p peer.Peer; grpc.Peer(&p)`,
  and is deleted); `Grpc.Peer.spec` restated over the struct variable (`p ↦ v ∗ peerFieldsOk v`,
  post `callOptOk o ∗ peerVar p`); `grpc/peer/Peer__String.lean` restored.
- Not done: an introduction law for `Grpc.genCliAt`/`genSrvAt` (the generic wrappers' persisted
  points-to): the generic struct's field cannot be named in today's points-to syntax; the stream
  stub and handler specs (old and new) rely on the intended realization. Recorded.

## Requests to apply-txn (from the sub-agent, C-F6)

2. `txn/Api.lean`: replace the provisional persistent `stringerOk` with `EtcdServerPb.stringerAt`
   (not persistent: a persistent "its `String()` returns" cannot be introduced for a request held
   at a share, which a later write would race; `EtcdServer.Range`'s deferred
   `WarnOfExpensiveReadOnlyRangeRequest` gets its share back), the `Warn*` specs giving it back; the
   apply thread's read-only messages use `stringerAt_discard`.

## Stale notes in other groups' files

- client-core: `retryKVClient__RangeStream.lean`'s "Open … `lo = 0`" (C-F1).
- server-boot: `NewElectionServer.lean`'s "Users: `v3rpc.Server`" (embed registers it, C-F4).

## Build

`etc/specs-build.sh --dir` OK on every owned directory: `Spec/google_golang_org/{protobuf/proto,
grpc, grpc/metadata, grpc/status, grpc/health, grpc/health/grpc_health_v1, grpc/credentials,
grpc/credentials/insecure, grpc/peer, grpc/grpclog}`, `Spec/go_etcd_io/etcd/api/v3/{etcdserverpb,
v3rpc/rpctypes, version}`, `.../api/v3lock/v3lockpb`, `.../api/v3election/v3electionpb`,
`.../api/v3rpc` (115), `Spec/net/http`, `Spec/sort`; and the importers checked: 2c's
`EtcdServer__{Range,Txn,RangeStream}`, `api/v3election`, `api/v3lock`. Snippets: `go vet
./specreq/{v3rpc,v3rpcwatch,grpc,etcdserverpb}/` clean (new `grpc/dialopts.go`).

## Follow-up: `norm` and explicit presence (coordinator, from raft-conf-pb's second pass)

`Proto/Api.lean`'s header and `norm`'s docstring now say what `norm` does field by field. It
turns empty repeated fields and maps into `nil`. It unsets implicit-presence (proto3) fields that
hold their zero value. A field with explicit presence (proto2 `optional` scalars and `bytes`, proto3
`optional`, every submessage) keeps a set zero or empty value, and a set empty submessage stays a
non-`nil` empty message.

This is what protobuf-go does, checked against v1.36.12:
- explicit-presence fields are encoded and decoded as set;
- `Clone` copies a set empty `bytes` field through `mergeBytes` (`internal/impl/merge.go:187`), so it
  stays non-`nil`;
- only implicit-presence `bytes` fields use `mergeBytesNoZero` (`:191`).

So raftpb's `raftpb_norm` holds, with `ConfState.AutoLeave = false` (a proto2 field) surviving
`norm`.

## Follow-up: a stringer for `InternalRaftStringer` (apply-txn's second pass)

New law `EtcdServerPb.stringerAt_irr.spec` in `etcdserverpb/Stringer.lean`. Given
`w.[InternalRaftStringer, "Request"] ↦□ r` and `Proto.msgAt InternalRaftRequest.ty r DFrac.discard c`,
it gives `□ stringerAt` of `&pb.InternalRaftStringer{Request: r}`. This is the stringer source for
dispatch's warnings at `uber_applier.go:99,101`.

apply-txn's `irrMsgAt p ir`, the apply thread's read-only request, must give the `msgAt … DFrac.discard`
that this law takes. That follows from its realization. `etcdserverpb` rebuilt: OK (142 modules).

Other groups' new `*_norm` laws, read only (no edits to their files):
- raftpb's `raftpb_norm` and leasehttp's `ltlReply_norm` are consistent with this reading.
- W0's `urlsRight_norm` is unrelated: it is about URL normalization, not `Proto.norm`.
