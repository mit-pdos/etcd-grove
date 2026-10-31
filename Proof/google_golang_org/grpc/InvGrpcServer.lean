/-
**grpc's server, built and started** (item 4 of the client→server path, 2026-10-17; Lean-first,
no Rocq counterpart): what produces the tokens `grpcServerAt addr ics regs` (`InvGrpc.lean`) and
`grpcStreamServerAt addr sics sregs` (`InvGrpcStream.lean`) that `grpc.serve` and
`grpc.serveStream` consume. The Go-level specs of grpc's `NewServer`, its options,
`Server.RegisterService` and `Server.Serve`, and of `net.Listen`, are trust-boundary axioms
(`Spec/google_golang_org/grpc/`, `Spec/net/Listen.lean`); this file is their vocabulary.

**Options** (`grpcSrvOpt v k`, an axiomatized property of a `grpc.ServerOption` `v`, introduced
only by the option constructors' specs): what `NewServer` does with it, `k`:
* `.chainUnary ics` (`ChainUnaryInterceptor(ics...)`): the unary interceptors `ics`, appended to
  the server's chain in order (grpc's `chainUnaryServerInterceptors`; no `UnaryInterceptor`
  option is specified, so the chain is these lists, concatenated);
* `.chainStream ics` (`ChainStreamInterceptor(ics...)`): likewise for streams;
* `.neutral`: an option that does not change which handler runs for a method, nor what a run is
  given (the run's context, `grpcRunCtx`; the decoded request, `grpcDecOk`): message size limits
  (a call over the limit fails before its handler runs, or its response is not delivered: an error
  for the client), `MaxConcurrentStreams` (calls wait), a protobuf codec (`CustomCodec` of a codec with `grpcProtoCodec`: the wire models `ProtoMsg` are protobuf's),
  a stats handler that adds no value under etcd's context keys (`StatsHandler` of a handler with
  `grpcStatsHandlerOk`: otelgrpc's, `grpcRunCtx`).

**The server being built** (`grpcSrvNew gs ics sics svcs regs sregs`, exclusive, axiomatized):
`NewServer`'s `*grpc.Server` `gs`, not serving yet, with the unary and stream chains `ics`,
`sics`, the services `svcs` registered (their names), and their unary methods `regs` and streams
`sregs` (full method name `/<service>/<method>`, `MethodDesc.Handler`/`StreamDesc.Handler`,
service value). `RegisterService` adds a service (`grpcDescIs`: its `ServiceDesc`, read-only; a
service name not registered yet, a service value implementing the descriptor's `HandlerType`, its
method and stream names distinct: grpc's `logger.Fatalf` otherwise).

**The start** (`grpc.start`, an axiom): the server being built and a listener bound at `addr`
(`netListenerAt`, `Proof/net/InvNet.lean`) become the server at `addr` (`grpcServerAt`,
`grpcStreamServerAt`: the chains and registrations are fixed from now on) and the right to serve
(`grpcServeTok gs lis`, what `gs.Serve(lis)` takes). A ghost step, before the `go
gs.Serve(lis)`: the server's methods are served at `addr` once `Serve` runs (`grpc.serve`'s facts
are about the calls `addr` answers; a call before `Serve` accepts waits, or fails: an error for
the client). After it the server can no longer register a service (grpc's `RegisterService`
after `Serve` is fatal).

**The replies' size** (`grpcRepliesFit`, a premise of `grpc.start`, 2026-10-31,
`notes/reply-size.md`): grpc marshals a reply before any size check, and the codec's `make` panics
above Go's `maxAlloc` (`grpcReplyMax`). The start takes the named workload premise that no reply of
the run (the replies to the program's own clients' calls) exceeds it; the three tokens it makes
exist only in such a run, so `grpc.serve`, `grpc.serveStream` and `grpc.Server.Serve.wp_proof`,
which consume them, are true under it, and so is every result built on the tokens (the served results `etcd_kv_served`, `ServedOn`, `AuthnServedOn`,
v3rpc's, whose statements do not show it). No law turns a token back into the premise.

**The health service** (`grpcHealthSrv hs`, persistent, axiomatized): grpc's `*health.Server`
`hs` (`health.NewServer()`), whose `SetServingStatus` is safe from any goroutine.

**grpc-prometheus's server metrics** (`promSrvMetrics m`, persistent, axiomatized): a
`*ServerMetrics` `m` made by `NewServerMetrics` (its counters and histograms, safe from any
goroutine), whose interceptors are transparent; `promSrvMetricsOpt o`: `o` is one of the
provider's own `ServerMetricsOption`s (`WithServerHandlingTimeHistogram()`), which only set the
metrics' configuration.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcStream
public import Proof.net.InvNet

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-- **What `grpc.NewServer` does with an option** (see the file header). -/
inductive SrvOptKind [GooseExts] : Type where
  | chainUnary (ics : List GoFunc)
  | chainStream (ics : List GoFunc)
  | neutral

/-- The unary interceptors an option adds to the chain. -/
def SrvOptKind.unary [GooseExts] : SrvOptKind → List GoFunc
  | .chainUnary ics => ics
  | _ => []

/-- The stream interceptors an option adds to the chain. -/
def SrvOptKind.stream [GooseExts] : SrvOptKind → List GoFunc
  | .chainStream ics => ics
  | _ => []

/-- The unary chain of a server built with options of the kinds `ks`. -/
def srvOptsUnary [GooseExts] (ks : List SrvOptKind) : List GoFunc := ks.flatMap SrvOptKind.unary

/-- The stream chain of a server built with options of the kinds `ks`. -/
def srvOptsStream [GooseExts] (ks : List SrvOptKind) : List GoFunc := ks.flatMap SrvOptKind.stream

/-- **The `grpc.ServerOption` `v` is one of the kind `k`** (an axiomatized property; see the file
header). -/
axiom grpcSrvOpt [GooseExts] (v : GoInterface) (k : SrvOptKind) : Prop

/-- **The `grpc.Codec` `c` is a protobuf codec** (an axiomatized property): its `Marshal` and
`Unmarshal` are protobuf's (`proto.Marshal`/`proto.Unmarshal` of the message), as the default
codec's; what the wire models (`ProtoMsg`) presume. etcd's `v3rpc.codec` is one
(`v3rpc.codec_proto`). -/
axiom grpcProtoCodec [GooseExts] (c : GoInterface) : Prop

/-- **The `stats.Handler` `h` adds no value under etcd's context keys and lets every call run**
(an axiomatized property, introduced by `otelgrpc.NewServerHandler`'s spec): what `grpcRunCtx`
presumes of the stats handlers in front of a method's handler. -/
axiom grpcStatsHandlerOk [GooseExts] (h : GoInterface) : Prop

/-- **The server being built** (exclusive; see the file header). -/
axiom grpcSrvNew {GF : BundledGFunctors} [GooseExts] (gs : Loc) (ics sics : List GoFunc)
  (svcs : List GoString) (regs sregs : List (GoString × val × GoInterface)) : IProp GF

/-- **The right to serve `gs` on the listener `lis`** (exclusive; `grpc.start`'s, what
`gs.Serve(lis)` takes). Exists only in a run satisfying `grpcRepliesFit`: made only by
`grpc.start`, which takes it. -/
axiom grpcServeTok {GF : BundledGFunctors} [GooseExts] (gs : Loc) (lis : GoInterface) : IProp GF

/-- **grpc's health server `hs`** (persistent; see the file header). -/
axiom grpcHealthSrv {GF : BundledGFunctors} [GooseExts] (hs : Loc) : IProp GF

axiom grpcHealthSrv_persistent {GF : BundledGFunctors} [GooseExts] (hs : Loc) :
  Persistent (grpcHealthSrv (GF := GF) hs)

attribute [instance] grpcHealthSrv_persistent

/-- **grpc-prometheus's server metrics `m`** (persistent; see the file header). -/
axiom promSrvMetrics {GF : BundledGFunctors} [GooseExts] (m : Loc) : IProp GF

axiom promSrvMetrics_persistent {GF : BundledGFunctors} [GooseExts] (m : Loc) :
  Persistent (promSrvMetrics (GF := GF) m)

attribute [instance] promSrvMetrics_persistent

/-- **`o` is one of grpc-prometheus's own server-metrics options** (see the file header). -/
axiom promSrvMetricsOpt [GooseExts] (o : GoFunc) : Prop

section pure
variable [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]

/-- A method's full name, as grpc's server dispatches it (`/<service>/<method>`). -/
def grpcFullName (sn mn : GoString) : GoString := go!"/" ++ sn ++ go!"/" ++ mn

/-- The unary methods a `ServiceDesc` with the service name `sn` and the methods `mds` registers,
for the service value `ss`. -/
def descRegs (sn : GoString) (mds : List google_golang_org.grpc.MethodDesc) (ss : GoInterface) :
    List (GoString × val × GoInterface) :=
  mds.map fun md => (grpcFullName sn md.MethodName', #md.Handler', ss)

/-- The streams a `ServiceDesc` with the service name `sn` and the streams `sds` registers, for
the service value `ss`. -/
def descSRegs (sn : GoString) (sds : List google_golang_org.grpc.StreamDesc) (ss : GoInterface) :
    List (GoString × val × GoInterface) :=
  sds.map fun sd => (grpcFullName sn sd.StreamName', #sd.Handler', ss)

/-- The method and stream names of a `ServiceDesc`. -/
def descNames (mds : List google_golang_org.grpc.MethodDesc)
    (sds : List google_golang_org.grpc.StreamDesc) : List GoString :=
  mds.map (·.MethodName') ++ sds.map (·.StreamName')

/-- **The service value `ss` implements the handler type `ht`** (grpc's `RegisterService` check,
`reflect.TypeOf(ss).Implements(reflect.TypeOf(ht).Elem())`): `ht` is a nil pointer to an
interface type `T` (the generated `(*KVServer)(nil)`), `ss` a non-nil value whose type is in
`T`'s type set. -/
def grpcImplements (ss ht : GoInterface) : Prop :=
  ∃ (T : go.GoType) (si : GoInterfaceOk),
    ht = interface.mkOk (go.GoType.PointerType T) #(null : Loc) ∧ ss = GoInterface.ok si ∧
    go.typeSetContains si.ty T = true

/-- The interface `interface{ testEmbeddedByValue() }` the generated `Register*Server` assert a
service value to (it calls the method if the value embeds the `Unimplemented*Server` by value).
The method is unexported, so its id is qualified by the package that declares it, `etcdserverpb`
(Go's `go/types.Id`, as goose names it). -/
def testEmbeddedIface : go.GoType :=
  go.GoType.InterfaceType [go.InterfaceElem.MethodElem
    go!"go.etcd.io/etcd/api/v3/etcdserverpb.testEmbeddedByValue"
    (go.signature.Signature [] false [])]

/-- **The service value `ss` has no `testEmbeddedByValue`** (a method-set fact: etcd's services
embed the `Unsafe*Server` interfaces, not `Unimplemented*Server` by value): the generated
`Register*Server`'s type assertion fails and it calls nothing. -/
def grpcNoTestEmbedded (ss : GoInterface) : Prop :=
  ∃ si : GoInterfaceOk, ss = GoInterface.ok si ∧ go.typeSetContains si.ty testEmbeddedIface = false

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The `*grpc.ServiceDesc` `sd`** (persistent, read-only): its service name `sn`, its handler
type `ht`, its methods `mds` and its streams `sds`. -/
def grpcDescIs (sd : Loc) (sn : GoString) (ht : GoInterface)
    (mds : List google_golang_org.grpc.MethodDesc) (sds : List google_golang_org.grpc.StreamDesc) :
    IProp GF :=
  iprop(∃ msl ssl : GoSlice,
    structFieldRef google_golang_org.grpc.ServiceDesc go!"ServiceName" sd ↦□ sn ∗
    structFieldRef google_golang_org.grpc.ServiceDesc go!"HandlerType" sd ↦□ ht ∗
    structFieldRef google_golang_org.grpc.ServiceDesc go!"Methods" sd ↦□ msl ∗ msl ↦*□ mds ∗
    structFieldRef google_golang_org.grpc.ServiceDesc go!"Streams" sd ↦□ ssl ∗ ssl ↦*□ sds)

instance grpcDescIs_persistent (sd : Loc) (sn : GoString) (ht : GoInterface)
    (mds : List google_golang_org.grpc.MethodDesc) (sds : List google_golang_org.grpc.StreamDesc) :
    Persistent (grpcDescIs (GF := GF) sd sn ht mds sds) := by
  unfold grpcDescIs; infer_instance

/-- **Go's `maxAlloc` on linux/amd64** (`runtime/malloc.go:213,220`): grpc's codecs `make` a
reply's encoded length before any size check (protobuf-go `proto/encode.go:184-194`; grpc's default
codec `internal/mem/buffer_pool.go:354-356`, page-rounded), and `make` panics above this. A reply
at most this long marshals; in `(2 ^ 31 - 1, 2 ^ 48]` it then fails with `ResourceExhausted`
(etcd's `MaxSendMsgSize`, `encode`'s `MaxUint32` check), which the client's attempt contract
allows. Running out of memory below it is outside the model. -/
def grpcReplyMax : Nat := 2 ^ 48

/-- **The replies fit** (opaque; a named workload premise, D19a's first kind, as
`apply.backendUnderQuota` and `authRecordsFit`): in every run of the theorem's program, every reply
message a gRPC server marshals for sending (a unary reply after its handler returns, a stream
handler's `SendMsg`/`Send`) has an encoded length, as a natural number, of at most `grpcReplyMax`,
counting a submessage, or a byte slice's contents, once per reference (`notes/reply-size.md`).
Global, one for the run, not per server. It is about the replies to the calls of the program's own
clients: a process outside the program could connect to a member's port and send the request
below that makes it false, which is outside the scope of every closed theorem (they model no
outside peer).

**What makes it true**: each byte slice and submessage is referenced a bounded number of times
per reply, so the encoding is at most a small multiple of the memory the reply references, and Go's
user address space on linux/amd64 is `2 ^ 47` bytes (out of memory comes first); or the workload's
replies are small outright.

**True of the closed theorems' programs**, whose replies are at most tens of kilobytes:
- putget, putget3, putgetc: one point `Get`;
- linkvtxn, and linkv3p's `Main` (linkvtxn's workload over three members, through bridges): point
  operations, flat transactions of at most three point operations, and one bounded range;
- authkv: fixed literals, its one nested transaction a write;
- k8setcd3: a bounded loop. k8s' keys-only `getKeys` runs only with the cacher's size estimation,
  which this program never builds;
- the watch examples (watchkv, cachekv, linkv3p's `MainWatch`): small literal prefixes; a watch
  reply batches at most 1000 revisions (`watchBatchMaxRevs`) of one small put each, tens of
  kilobytes. cachekv's `etcd/cache` library adds its own requests: a whole-prefix `Get`, a
  count-only `Get` with limit 1, a prefix watch with progress and created notifications, and
  `RequestProgress`, all over the same few small keys.
None of them sends a transaction of many keys-only ranges.

**False of** etcd under a client that sends a transaction whose nested transactions hold many
keys-only ranges over long keys (`issues/etcd-txn-keysonly-reply-alloc-panic.md`, reproduced: 4
keys under a 32 MiB `--max-request-bytes`, a 12.8 GiB member, the panic). A keys-only range's
`KeyValue`s share the index's key slices (`mvcc/index.go:181`, `kvstore_txn.go:88-106`), and
`checkTxnRequest` bounds the operations per nesting level, not the tree, so the reply's encoding
grows with the leaves times the keys' bytes and can pass `grpcReplyMax`, which panics the member
marshalling it. Such a transaction is not read-only (`IsTxnReadonly` looks at the top level only,
where its operations are transactions), so it goes through raft, bounded by `--max-request-bytes`,
and every member builds the reply in apply; the member serving the client marshals it. A flat
read-only transaction is served locally, without the proposal's `--max-request-bytes` check, but
holds at most `--max-txn-ops` ranges (128 by default), so its reply is at most that many copies of
the stored keys' keys-only encodings (each key's bytes plus at most 34 bytes of revisions and
framing): below `grpcReplyMax` unless that limit times the sum of those encodings passes it (at
the defaults, 2 TiB of such encodings; the suggested maximum quota is 8 GiB). Also false of a program whose handler
returns a reply sharing a submessage or byte slice many times. A theorem taking this premise says
nothing about such runs. The client's send side has its own checked premise (`grpcInvokerOk`'s
`Req.wireLen m < grpcMsgMax`). -/
opaque grpcRepliesFit : Prop

/-- **The start** (an axiom; see the file header): the server being built and a listener bound
at `addr` become the server at `addr`, with its chains and registrations, and the right to serve
it on the listener. True of grpc: `Serve(lis)` serves every call accepted on `lis` with the
server's chains and its registered methods (`handleStream`: the method of the call's path
`/<service>/<method>` in `services[service]`), and no registration is made after it. Under the
named workload premise `grpcRepliesFit` (2026-10-31, `notes/reply-size.md`), which the three
tokens carry: what makes `grpc.serve`, `grpc.serveStream` and `grpc.Server.Serve.wp_proof` true. -/
axiom grpc.start (gs : Loc) (lis : GoInterface) (addr : GoString) (ics sics : List GoFunc)
    (svcs : List GoString) (regs sregs : List (GoString × val × GoInterface)) :
  grpcRepliesFit →
  grpcSrvNew (GF := GF) gs ics sics svcs regs sregs ∗ netListenerAt lis addr ⊢
    |={⊤}=> grpcServerAt addr ics regs ∗ grpcStreamServerAt addr sics sregs ∗ grpcServeTok gs lis

end defs

end EtcdGrove
end Perennial
