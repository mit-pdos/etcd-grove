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
`gs.Serve(lis)` takes). -/
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
service value to (it calls the method if the value embeds the `Unimplemented*Server` by value). -/
def testEmbeddedIface : go.GoType :=
  go.GoType.InterfaceType [go.InterfaceElem.MethodElem go!"testEmbeddedByValue"
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

/-- **The start** (an axiom; see the file header): the server being built and a listener bound
at `addr` become the server at `addr`, with its chains and registrations, and the right to serve
it on the listener. True of grpc: `Serve(lis)` serves every call accepted on `lis` with the
server's chains and its registered methods (`handleStream`: the method of the call's path
`/<service>/<method>` in `services[service]`), and no registration is made after it. -/
axiom grpc.start (gs : Loc) (lis : GoInterface) (addr : GoString) (ics sics : List GoFunc)
    (svcs : List GoString) (regs sregs : List (GoString × val × GoInterface)) :
  grpcSrvNew (GF := GF) gs ics sics svcs regs sregs ∗ netListenerAt lis addr ⊢
    |={⊤}=> grpcServerAt addr ics regs ∗ grpcStreamServerAt addr sics sregs ∗ grpcServeTok gs lis

end defs

end EtcdGrove
end Perennial
