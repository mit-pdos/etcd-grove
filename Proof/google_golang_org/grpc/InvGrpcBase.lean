/-
**A generic gRPC specification** (2026-10-14; replaces unit C1's `Put`/`Range`-specific
transport contract): the vocabulary of grpc's trust boundary, for any service, method and message
type, in the predicate-transformer style of Grove's urpc (`is_urpc_spec_pred`,
`is_urpc_handler_pred`, `wp_Client__Call_pred`). Lean-first (no Rocq counterpart); the design:
`notes/decisions.md`, "A generic gRPC specification".

**Messages** (`ProtoMsg`): a protobuf message type `T` (passed as `*T`) with the model `M` of its
wire content; `send l m`: the sender's `*T` holding `m`, what the codec needs to marshal it (it
comes back); `recv l m` (persistent): a decoded `*T` holding `m`, read-only, and `recvOwn l m` what else of it
the receiver owns (nothing but for a request its handler writes, and for a reply whose decoded
slices its caller writes: k8s 7e-1, `RangeResponse.Kvs`); `blank l`: a zero `*T`
the receiver owns, into which a reply is decoded. That the codec's copy of a message `send` holds
at `m` is one `recv` holds at `m` is what an instance asserts: each instance is a trusted wire
model of its Go type (read it against the type's fields).

**A method's spec** (`Spec : Req.M → (Rep.M → IProp) → IProp`): a predicate transformer over the
request's and reply's models (urpc's saved spec): `Spec m Φ` is what a caller asking `m` must give
for the handler to answer some `m'` with `Φ m'`.

**The server side** (unit P3b: the boundary below etcd's generated handlers and interceptors).
A service method `h` meets `Spec` with the per-run resource `S` (`grpcHandlerOk h S Spec`). grpc's
runtime runs, for a call of a registered method, its `MethodDesc.Handler` `mh` on the registered
service value `srv`, with grpc's `dec` (`grpcDecOk`) and the interceptor it composes for the
server's chain `ics` (`grpcSrvChain`, `srvChainWP`); `grpcMethodOk mh srv ics S Spec` is what
such a run must meet. Since per-type stage B (B1b), a run is a fork of grpc's `Server.Serve`
(its trusted model, `TrustedCode/google_golang_org/grpc.lean`), given the fork's thread
token and one later credit and returning the token (`grpcRunOkMd`, the run contract; handlers
proved against `grpcMethodOkMd` at a bundle get it from the adapters, `InvGrpcRun.lean`). The server's
configuration is Go's (`grpcSrvNew`), which the start (`grpc.start'`) makes the address's service
table; `grpc.serve` (a theorem) packages it with the run contracts into registrations. (Until B1b, `grpc.serve` was an axiom taking a caller-chosen run
resource `S` and count `n`, `axiom/grpc-serve-pool`.)
Interceptors are specified as transparent (`srvInterceptorOk`, `srvChainWP_of_ok`).

**Registration** (`isGrpcRpc addr name Spec`, persistent, a definition): the handler Go's
configuration of the server at `addr` registers under `name` meets `Spec` as grpc runs it
(`isGrpcRpcAt`, `grpcRunOkMd`). Several specs of one
method may hold (each a fact about the one handler); a client needs one.

**The client side** (unit P3a, 2026-10-14: the boundary below the interceptors).
`grpcConn conn addr ics dopts` (persistent, opaque): the client's `*ClientConn` `conn` reaches the
server at `addr`, with the unary interceptor chain `ics` and the default call options `dopts`.
`ClientConn.Invoke` (the one client-side axiom, `Spec/google_golang_org/grpc/
ClientConn__Invoke.lean`) of any method is the chain (`chainWP`, as grpc composes it) over grpc's
`invoke`, which makes one attempt (`grpcInvokerOk`: a run of the handler served for a registered
method, or an error); an attempt's call options are scalar or `grpc.Peer(p)` options
(`grpcOptOk`, `grpcPeerOpt`), whose buffers `*p` (`grpcPeerBuf`) the attempt writes.

**Per-type message models** (stage A, the Scope's R and V for `ProtoMsg`, revisions 4 to 6; moved
here from the prototype's `grpc/PerType.lean`, CP2; today's `ProtoMsg` and the trusted grpc specs
stay until CP3): `ProtoMsgT`, a `ProtoMsg` (whose normalizing store `tree`, `Store.lean`, moved into
`ProtoMsg` at phase 7 S2's interface); the
role-split registries `grpcReqModelOf` (a method's request) and `grpcRepModelOf` (its reply), keyed
on the Go type, taking the heap's instances (`hG`; `ProtoMsg GF` mentions no heap, so an
`hG`-independent registry would equate models across heaps) and `go.Semantics`; and what a
registration must prove: `ProtoMsgT.ReqSat` (from a `blank`, with the request's `wireLen` below
`grpcMsgMax`, the store gives `recv` and `recvOwn`) and `ProtoMsgT.RepSat` (from an `own`, what a
failed attempt leaves, no `wireLen` premise, the store gives `recv` and `recvOwn`), each with the laws that make
its resources satisfiable: `blank` the zero struct (`BlankZero`), `own` any struct (`OwnAny`),
`send` at `nil` false.
-/
module

public import Perennial.Proof.context
public import Proof.go_opentelemetry_io.otel.trace.Defs
public import Proof.context.LibKeys
public import Proof.context.LibKeysChain
public import Proof.net.http.NetCtx
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.SrvCtxWeak
public import Proof.go_etcd_io.etcd.client.v3.ClientErr
public import GeneratedProof.google_golang_org.grpc.peer
public import Proof.google_golang_org.grpc.metadata.Outgoing
public import Code.google_golang_org.grpc.credentials
public import Proof.google_golang_org.protobuf.proto.Store

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The size below which grpc's codec sends a message** (`2 ^ 32` bytes; 64-bit Go, the model's
platform; `notes/decisions.md`, "The encoded-size bound at grpc's send side";
`issues/grpc-codec-alloc-before-size-check.md`). grpc-go v1.84's `codecV2.Marshal` allocates
`proto.Size(m)` bytes (rounded up to 4 KiB) before any size check, and `make` panics above Go's
`maxAlloc` (`2 ^ 48` on linux/amd64); at `2 ^ 32` bytes and above, grpc refuses the message
(`encode`'s `MaxUint32` check, an error), so no message at or above the bound is ever delivered. -/
def grpcMsgMax : Nat := 2 ^ 32

/-- **A protobuf message type** (see the file header). -/
structure ProtoMsg (GF : BundledGFunctors) where
  /-- The message's Go type `T` (the message is passed as `*T`). -/
  ty : go.GoType
  /-- The model of the message's wire content. -/
  M : Type
  /-- **The message's stored form** (phase 7 S2's interface, O3, 2026-11-23: moved here from
  `ProtoMsgT`, unchanged): the tree of values (`Store.lean`) that `storeInto ty l` writes for a `*T`
  holding `m`. With `ty` and `M` it is the message's wire part (`ProtoMsg.wire`, no heap). -/
  tree : M → VTree
  /-- **The model is countable** (phase 7, SW1, 2026-11-24, `notes/phase7-endstate.md` §1.2): a
  call's queues are ghost lists of models (`ProtoWire.cnt`). Filled by instance resolution at the
  instance's `M`; not itself a global instance (a projection instance could disagree with `M`'s own). -/
  cnt : Pos.Countable M := by infer_instance
  /-- The sender's `*T` holding `m` (what marshaling needs; it comes back). -/
  send : Loc → M → IProp GF
  /-- **An upper bound on the length of the encoding** (`proto.Size`) of every message `send`
  holds at `m`, counting a submessage at each reference (as protobuf-go's `Size` does). Read it
  against `send`: every wire field must be pinned by `send`. Scope: the unknown fields of the
  messages `send` holds field by field (inside `txnReqAt` at every nested level, `createReqSend`,
  `userOptsAt`, `ownPermW`, the Lease replies' headers and `LeaseStatus` elements, and the watch
  stream's outer, cancel and progress messages) are not pinned to none (`userOptsAt` holds them as
  some valid bytes, auth-schema-fix MAJ-2); translated code never sets unknown fields (`SetUnknown` is not
  translated; requests are struct literals), so the bound is claimed for messages without them
  (the whole-struct sends pin them; the rest is to come, `notes/decisions.md`, "The encoded-size
  bound at grpc's send side"). `grpcMsgMax` or more: no bound known (the default; responses),
  so the message cannot be sent (`grpcInvokerOk`). Part of the instance's trusted wire model. -/
  wireLen : M → Nat := fun _ => grpcMsgMax
  /-- A decoded `*T` holding `m` (read-only). -/
  recv : Loc → M → IProp GF
  recv_persistent : ∀ l m, Persistent (recv l m)
  /-- What else of a decoded `*T` holding `m` the receiver owns (exclusive; the auth plan's E3za:
  a handler that writes the decoded request, etcd's `UserAdd` replacing its password by the
  hash; k8s 7e-1: a caller that writes the decoded reply, Kubernetes' store setting
  `resp.Kvs[i] = nil`). Nothing by default. -/
  recvOwn : Loc → M → IProp GF := fun _ _ => iprop(True)
  /-- A zero `*T` the receiver owns. -/
  blank : Loc → IProp GF
  /-- A `*T` the receiver owns, at any content (unit P3a: what a failed attempt leaves of the
  reply, into which the next attempt decodes; grpc's codec resets the message first). -/
  own : Loc → IProp GF
  blank_own : ∀ l, blank l ⊢ own l

attribute [instance] ProtoMsg.recv_persistent

/-- **A gRPC method's spec** over the request's and reply's models (a predicate transformer). -/
abbrev GrpcSpec (Req Rep : ProtoMsg GF) : Type := Req.M → (Rep.M → IProp GF) → IProp GF

/-- **A call's metadata** (a context's incoming metadata, `metadata.ctxInMD`: `none`, or each key's
values). -/
abbrev GrpcMd : Type := Option (GoString → Option (List GoString))

/-- **The error descriptions only a handler makes** (k8s etcd3 stage 7c, `notes/k8s-etcd3-plan.md`,
"7c-1"): grpc forwards a status the server sends unchanged and never makes one of these itself, so
an attempt's error with one of them is the handler's own, with the handler's error outcome
(`grpcInvokerOk`): the two read errors', mvcc's future revision and compacted revision as
`togRPCError` maps them (k8s etcd3 7c-2 part 2, S7). -/
def handlerDescs : List GoString :=
  [go_etcd_io.etcd.cache.v3.futureRevDesc, go_etcd_io.etcd.cache.v3.compactedDesc]

/-- Go's two context messages are no handler's description (incomingof Part B, T2'). -/
theorem ctxErrMsg_not_handler {m : GoString} (h : go_etcd_io.etcd.cache.v3.ctxErrMsg m) :
    m ∉ handlerDescs := by
  rcases h with rfl | rfl <;> decide

/-- **A handler's error outcome** (errdesc stage 2b, 2026-11-21): the error `err` has a description
`m` (`descIs`), and if it is a non-nil error with a handler's description, the caller's continuation
`Ψe m` holds. What grpc relays to the client for a handler's error (`grpc.model.respond`). Until
2026-11-21 the literal `⌜err ≠ nil ∧ errDesc err ∈ handlerDescs⌝ -∗ Ψe (errDesc err)` of the pure
`errDesc`. -/
def handlerErrOut (Ψe : GoString → IProp GF) (err : GoInterface) : IProp GF :=
  iprop(∃ m : GoString, go_etcd_io.etcd.cache.v3.descIs err m ∗
    (⌜err ≠ GoInterface.nil ∧ m ∈ handlerDescs⌝ -∗ Ψe m))

/-- **An error that is not a handler's** (persistent; errdesc stage 2b): non-nil, with a description
none of `handlerDescs`' (grpc's own errors: `dec`'s, an interceptor's refusal). -/
abbrev notHandlerErr (err : GoInterface) : IProp GF :=
  go_etcd_io.etcd.cache.v3.notDescIn handlerDescs err

/-- A handler's success holds its error outcome vacuously. -/
theorem handlerErrOut_nil (Ψe : GoString → IProp GF) : ⊢ handlerErrOut Ψe GoInterface.nil := by
  unfold handlerErrOut
  iexists go!""
  isplitl
  · iapply go_etcd_io.etcd.cache.v3.descIs_nil
  · iintro %h
    exact absurd rfl h.1

/-- An error that is not a handler's holds every error outcome. -/
theorem handlerErrOut_not (Ψe : GoString → IProp GF) (err : GoInterface) :
    notHandlerErr (GF := GF) err ⊢ handlerErrOut Ψe err := by
  unfold notHandlerErr go_etcd_io.etcd.cache.v3.notDescIn handlerErrOut
  iintro ⟨%hne, %m, #Hd, %hm⟩
  iexists m
  iframe Hd
  iintro %h
  exact absurd h.2 hm

/-- A caller's error outcome at every description holds at every error with a description. -/
theorem handlerErrOut_all (Ψe : GoString → IProp GF) (err : GoInterface) (m : GoString) :
    (□ ∀ d, Ψe d) ⊢ go_etcd_io.etcd.cache.v3.descIs err m -∗ handlerErrOut Ψe err := by
  iintro #H #Hd
  unfold handlerErrOut
  iexists m
  iframe Hd
  iintro -
  iapply H

/-- A caller's error outcome at every description holds at every error grpc's `status` accepts. -/
theorem handlerErrOut_allS (Ψe : GoString → IProp GF) (err : GoInterface) :
    (□ ∀ d, Ψe d) ⊢ go_etcd_io.etcd.cache.v3.statusErrOk err -∗ handlerErrOut Ψe err := by
  iintro #H #Hs
  ihave ⟨%m, #Hd⟩ := go_etcd_io.etcd.cache.v3.statusErrOk_descIs err $$ Hs
  iapply handlerErrOut_all $$ H Hd

/-- A caller's error outcome at every description holds at every handler error. -/
theorem handlerErrOut_allSrv [EtcdGrove.ErrorStringLeaf] (Ψe : GoString → IProp GF) (err : GoInterface) :
    (□ ∀ d, Ψe d) ⊢ go_etcd_io.etcd.cache.v3.srvErrOk err -∗ handlerErrOut Ψe err := by
  iintro #H #Hs
  ihave ⟨%m, #Hd⟩ := go_etcd_io.etcd.cache.v3.srvErrOk_descIs err $$ Hs
  iapply handlerErrOut_all $$ H Hd

/-- An error outcome is monotone in its continuation. -/
theorem handlerErrOut_mono (Ψe Ψe' : GoString → IProp GF) (err : GoInterface) :
    handlerErrOut Ψe err ⊢ (∀ d, Ψe d -∗ Ψe' d) -∗ handlerErrOut Ψe' err := by
  unfold handlerErrOut
  iintro ⟨%m, #Hd, H⟩ Hw
  iexists m
  iframe Hd
  iintro %h
  iapply Hw
  iapply H $$ %h

/-- **A method's spec at the call's metadata, with an error outcome** (the auth plan's E3zb; the
error outcome since k8s etcd3 stage 7c, `notes/k8s-etcd3-plan.md`, "7c-1"): `Spec md m Φ Ψ` is
what a caller asking `m` with an attempt whose handler sees the metadata `md` must give, for the
handler to answer some `m'` with `Φ m'`, or to fail with an error of description `d` (`errDesc`)
with `Ψ d`. A plain spec (`GrpcSpec`) is one for every metadata whose caller gives every error's
`Ψ` (`GrpcSpec.md`). -/
abbrev GrpcSpecMd (Req Rep : ProtoMsg GF) : Type :=
  GrpcMd → Req.M → (Rep.M → IProp GF) → (GoString → IProp GF) → IProp GF

/-- A plain spec, at every metadata: its caller gives every error's continuation. -/
abbrev GrpcSpec.md {Req Rep : ProtoMsg GF} (Spec : GrpcSpec Req Rep) : GrpcSpecMd Req Rep :=
  fun _ m Φ Ψ => iprop(Spec m Φ ∗ □ ∀ d, Ψ d)

/-- **The request precondition of a run of context `ci`** at the metadata the context carries:
`Spec md m Φ Ψe` for some `md` with `metadata.ctxInMD ci md` (perheap 1b, 2026-11-18: until then
`Spec (metadata.incomingOf ci) m Φ Ψe`, a pure function of the context). The contracts' form of
"`∀ md`, pre `ctxInMD ci md ∗ Spec md …`". -/
def grpcSpecAt {Req Rep : ProtoMsg GF} (Spec : GrpcSpecMd Req Rep) (ci : GoInterfaceOk) (m : Req.M)
    (Φ : Rep.M → IProp GF) (Ψe : GoString → IProp GF) : IProp GF :=
  iprop(∃ md : GrpcMd, metadata.ctxInMD ci md ∗ Spec md m Φ Ψe)

/-- **The prefix of etcd's Go package paths** (`go.etcd.io/etcd/`). -/
def etcdPkgPrefix : GoString := go!"go.etcd.io/etcd/"

/-- **The context a server's runtime makes for a run** (persistent; part of the trusted server
runtime, unit P3a with unit P1b's traces): its `Value(k)` of a key whose type is a named type of
etcd's own packages (`go.etcd.io/etcd/...`, e.g. `traceutil.TraceKey`) returns `nil`: grpc's
server context carries grpc's values (metadata, peer, stream) and those of the stats handlers
and interceptors in front of the handler (etcd's `v3rpc` interceptors, otelgrpc's), none under
such a key. What the server's handlers rely on: a request's context carries no trace
(`traceutil.ctxTraceIs ci none`, `v3rpc.srvCall`). And (2026-11-06, the fix of
`trace.SpanFromContext`'s axiom, `notes/axiom-review/otel-spanfromcontext-todo.md`) its span is a
span (`trace.spanCtxOk`): grpc's own contexts store none under otel's `currentSpanKey` (an
unexported key of otel's `trace` package, set only by `trace.ContextWithSpan`), nor do etcd's
interceptors; otelgrpc's stats handler (`otelgrpc.NewServerHandler`, `TagRPC`) stores the span
its tracer's `Start` returns (an SDK span, or the no-op tracer's `Span`, over the remote parent
`ContextWithRemoteSpanContext` stores, a `nonRecordingSpan`), each a span whose `End`,
`AddEvent` and `RecordError` return. And (premise-fixes-7, 2026-11-11) its library values are
well formed (`context.libCtxOk`, `Proof/context/LibKeys.lean`): grpc's server stores under
`mdIncomingKey{}` the `MD` its transport read from the stream's headers (`metadata.transportMDRaw`, through
`metadata.ctxInMD`; perheap step 0), under
`peerKey{}` the transport's `*Peer` (`transportPeer`), nothing under `mdOutgoingKey{}` (only
`NewOutgoingContext`/`AppendToOutgoingContext` store there, which no server code here calls on a
run's context), and under otel's `currentSpanKey` nothing or otelgrpc's span (`otelSpan`; its
tracer is etcd's provider, the only `otelgrpc.WithTracerProvider` etcd passes,
`server/embed/config_tracing.go`, which is of `otelSpan`'s narrowed set, 2026-11-13). (k8s
7f-4, Revision 1, m1) Of etcd's configuration: no `GRPCAdditionalServerOptions`
(`server/embed/etcd.go:789`) adds interceptors or stats handlers that store values at these keys, as
in the etcd binary (`etcdmain` never sets it). (k8s 7f-4, Addendum T-h6) It holds nothing at the keys
net/http's client reads (`http.netCtxOk`: `nil` at `httptrace`'s `clientEventContextKey{}`,
`nettrace.TraceKey{}`, `nettrace.LookupIPAltResolverKey{}`): unexported standard-library types, stored only
by `httptrace.WithClientTrace`, `net`'s tests, and `net`'s `Dialer.DialContext` on a context it derives
internally (go1.27.3 `net/dial.go:539`, never the caller's), which neither grpc's server, otelgrpc's stats
handler nor etcd's interceptors call (the run context's chain: `TestRunCtxChain`,
`examples/premisefix/streamctx`). (k8s 7f-4, Addendum T-k) Its causes are context errors
(`v3rpc.ctxCauseOk`): grpc v1.84.0 makes the run's contexts with `WithCancel`, `WithTimeout` and
`WithValue` only (e.g. `internal/transport/http2_server.go:537-539`, `handler_server.go:396-398`,
`server.go:1637, 1787`; no `WithCancelCause`, `WithDeadlineCause`, `WithTimeoutCause` or
`context.Cause` in its non-test sources), over `Background()` or, through `ServeHTTP`, the request context of net/http's HTTP/2 server
(`net/http/internal/http2`; `WithCancel`/`WithValue` of its base context; net/http's only cause variant is
the client transport's own child, `transport.go:675`, `clientconn.go:403`); otelgrpc's stats handler and
etcd's unary interceptors add `WithValue` links only. Each such context's `cause` is its `err`
(`cancel` stores `err` when the cause is nil), `Canceled` or `DeadlineExceeded`, and every `Err()` is
one of them (`TestRunCtxChain`, `TestRunCtxChainUnary`: `context.Cause` of the handler's context once
the call ends is `context.Canceled`). -/
def grpcRunCtx (ci : GoInterfaceOk) : IProp GF :=
  iprop((□ ∀ (n : GoString) (x : val) (Φ : val → IProp GF), ⌜etcdPkgPrefix <+: n⌝ →
    ▷ Φ #GoInterface.nil -∗
    WP (App (Val #(methods ci.ty go!"Value" ci.v))
      (Val #(interface.mkOk (go.GoType.Named n []) x : GoInterface))) {{ Φ }}) ∗
    trace.spanCtxOk ci ∗ context.libCtxOk ci ∗ http.netCtxOk ci ∗ v3rpc.ctxCauseOk ci)

instance grpcRunCtx_persistent (ci : GoInterfaceOk) : Persistent (grpcRunCtx (GF := GF) ci) := by
  unfold grpcRunCtx; infer_instance

/-- **A run's context has a span-key fact** (`grpcRunCtx`'s second part): what
`trace.SpanFromContext` needs of it. -/
theorem spanCtxOk_of_runCtx (ci : GoInterfaceOk) :
    grpcRunCtx (GF := GF) ci ⊢ trace.spanCtxOk ci := by
  iintro #H
  iunfold grpcRunCtx at H
  icases H with ⟨-, #H, -, -, -⟩
  iexact H

/-- **A run's context's library values are well formed** (`grpcRunCtx`'s third part). -/
theorem libCtxOk_of_runCtx (ci : GoInterfaceOk) :
    grpcRunCtx (GF := GF) ci ⊢ context.libCtxOk ci := by
  iintro #H
  iunfold grpcRunCtx at H
  icases H with ⟨-, -, #H, -, -⟩
  iexact H

/-- **A plain spec's precondition at a run's context** (`grpcSpecAt` of `GrpcSpec.md`), at the
metadata the context's library values give it (`libCtxOk`'s incoming part). -/
theorem grpcSpecAt_md_intro {Req Rep : ProtoMsg GF} (Spec : GrpcSpec Req Rep) (ci : GoInterfaceOk)
    (m : Req.M) (Φ : Rep.M → IProp GF) (Ψe : GoString → IProp GF) :
    grpcRunCtx (GF := GF) ci ∗ Spec m Φ ∗ □ (∀ d, Ψe d) ⊢ grpcSpecAt (GrpcSpec.md Spec) ci m Φ Ψe := by
  iintro ⟨#Hrc, HS, #Hall⟩
  ihave #Hl := libCtxOk_of_runCtx ci $$ Hrc
  iunfold context.libCtxOk at Hl
  icases Hl with ⟨#Hin, -⟩
  iunfold metadata.incomingCtxOk at Hin
  icases Hin with ⟨%md, #Hmd⟩
  iunfold grpcSpecAt
  iexists md
  isplitr
  · iexact Hmd
  simp only [GrpcSpec.md]
  iframe HS
  iexact Hall

/-- `grpcSpecAt` is monotone in the spec. -/
theorem grpcSpecAt_mono {Req Rep : ProtoMsg GF} (Spec Spec' : GrpcSpecMd Req Rep)
    (h : ∀ md m Φ Ψe, Spec' md m Φ Ψe ⊢ Spec md m Φ Ψe) (ci : GoInterfaceOk) (m : Req.M)
    (Φ : Rep.M → IProp GF) (Ψe : GoString → IProp GF) :
    grpcSpecAt (GF := GF) Spec' ci m Φ Ψe ⊢ grpcSpecAt Spec ci m Φ Ψe := by
  iintro H
  iunfold grpcSpecAt at H
  icases H with ⟨%md, #Hmd, H⟩
  iunfold grpcSpecAt
  iexists md
  iframe Hmd
  iapply (h md m Φ Ψe) $$ H

/-- `grpcSpecAt` is monotone in the spec, up to an update. -/
theorem grpcSpecAt_mono_upd {Req Rep : ProtoMsg GF} (Spec Spec' : GrpcSpecMd Req Rep)
    (h : ∀ md m Φ Ψe, Spec' md m Φ Ψe ⊢ |==> Spec md m Φ Ψe) (ci : GoInterfaceOk) (m : Req.M)
    (Φ : Rep.M → IProp GF) (Ψe : GoString → IProp GF) :
    grpcSpecAt (GF := GF) Spec' ci m Φ Ψe ⊢ |==> grpcSpecAt Spec ci m Φ Ψe := by
  iintro H
  iunfold grpcSpecAt at H
  icases H with ⟨%md, #Hmd, H⟩
  ihave H := (h md m Φ Ψe) $$ H
  imod H
  imodintro
  iunfold grpcSpecAt
  iexists md
  iframe Hmd H

/-- **A plain spec's precondition at a run's context is the spec's** (`grpcSpecAt_md_intro`'s
converse). -/
theorem grpcSpecAt_md_elim {Req Rep : ProtoMsg GF} (Spec : GrpcSpec Req Rep) (ci : GoInterfaceOk)
    (m : Req.M) (Φ : Rep.M → IProp GF) (Ψe : GoString → IProp GF) :
    grpcSpecAt (GF := GF) (GrpcSpec.md Spec) ci m Φ Ψe ⊢ Spec m Φ ∗ □ (∀ d, Ψe d) := by
  iintro H
  iunfold grpcSpecAt at H
  icases H with ⟨%md, -, H⟩
  iexact H

/-- **A run's context holds nothing at net/http's keys** (`grpcRunCtx`'s fourth part; T-h6). -/
theorem netCtxOk_of_runCtx (ci : GoInterfaceOk) :
    grpcRunCtx (GF := GF) ci ⊢ http.netCtxOk ci := by
  iintro #H
  iunfold grpcRunCtx at H
  icases H with ⟨-, -, -, #H, -⟩
  iexact H

/-- **A run's context's causes are context errors** (`grpcRunCtx`'s fifth part; Addendum T-k). -/
theorem ctxCauseOk_of_runCtx (ci : GoInterfaceOk) :
    grpcRunCtx (GF := GF) ci ⊢ v3rpc.ctxCauseOk ci := by
  iintro #H
  iunfold grpcRunCtx at H
  icases H with ⟨-, -, -, -, #H⟩
  iexact H

/-- **A service method `h` meets `Spec` with the per-run resource `S`** (persistent; see the file
header; unit P3b: the registered service's method, which the generated handler calls below the
interceptors, `grpcMethodOk`; until P3b it was what grpc ran): a call, given `S`, the context the
runtime made for the run (`isContext`, `grpcRunCtx`), the decoded request `r` at `m` and
`Spec m Φ`, returns `S` and, on success, a response at some `m'` with `Φ m'`; on failure, an
error grpc's server handles (`srvErrOk`: a `status` error, or a `fmt.Errorf` `%w` chain to a
context error, which the server maps to `Canceled`/`DeadlineExceeded`). -/
def grpcHandlerOk {Req Rep : ProtoMsg GF} (h : val) (S : IProp GF) (Spec : GrpcSpec Req Rep) :
    IProp GF :=
  iprop(∀ (m : Req.M) (Φ : Rep.M → IProp GF) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (r : Loc),
    {{ S ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ Req.recv r m ∗ Spec m Φ }}
      (App (App (Val h) (Val #(GoInterface.ok ci))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        S ∗ (⌜err = GoInterface.nil⌝ -∗ ∃ m' : Rep.M, Rep.send resp m' ∗ Φ m') ∗
        go_etcd_io.etcd.cache.v3.srvErrOk err }})

instance grpcHandlerOk_persistent {Req Rep : ProtoMsg GF} (h : val) (S : IProp GF)
    (Spec : GrpcSpec Req Rep) : Persistent (grpcHandlerOk h S Spec) := by
  unfold grpcHandlerOk; infer_instance

/-- **A service method `h` meets the metadata-indexed `Spec` with `S`** (persistent; the auth plan's
E3zb): as `grpcHandlerOk`, the run's request precondition at its context's incoming metadata
(`grpcSpecAt`). A plain spec's is `grpcHandlerOk` (`grpcHandlerOk_md`). -/
def grpcHandlerOkMd {Req Rep : ProtoMsg GF} (h : val) (S : IProp GF) (Spec : GrpcSpecMd Req Rep) :
    IProp GF :=
  iprop(∀ (m : Req.M) (Φ : Rep.M → IProp GF) (Ψe : GoString → IProp GF) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (r : Loc),
    {{ S ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ Req.recv r m ∗
        grpcSpecAt Spec ci m Φ Ψe }}
      (App (App (Val h) (Val #(GoInterface.ok ci))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        S ∗ (⌜err = GoInterface.nil⌝ -∗ ∃ m' : Rep.M, Rep.send resp m' ∗ Φ m') ∗
        handlerErrOut Ψe err ∗ go_etcd_io.etcd.cache.v3.srvErrOk err }})

instance grpcHandlerOkMd_persistent {Req Rep : ProtoMsg GF} (h : val) (S : IProp GF)
    (Spec : GrpcSpecMd Req Rep) : Persistent (grpcHandlerOkMd h S Spec) := by
  unfold grpcHandlerOkMd; infer_instance

theorem grpcHandlerOk_md [EtcdGrove.ErrorStringLeaf] {Req Rep : ProtoMsg GF} (h : val) (S : IProp GF)
    (Spec : GrpcSpec Req Rep) : grpcHandlerOk h S Spec ⊣⊢ grpcHandlerOkMd h S (GrpcSpec.md Spec) := by
  constructor
  · iintro #Hh
    unfold grpcHandlerOkMd
    iintro %m %Φ %Ψe %ci %cd %r !> %Ψ ⟨HS, Hctx, Hrc, Hr, HSpec⟩ HΨ
    ihave ⟨HSpec, #Hall⟩ := grpcSpecAt_md_elim _ _ _ _ _ $$ HSpec
    iunfold grpcHandlerOk at Hh
    iapply Hh $$ %m %Φ %ci %cd %r [HS Hctx Hrc Hr HSpec]
    · iframe
    inext
    iintro %resp %err ⟨HS, Hok, #Hse⟩
    iapply HΨ
    iframe
    isplitl
    · iapply (handlerErrOut_allSrv _ err) $$ Hall Hse
    · iexact Hse
  · iintro #Hh
    unfold grpcHandlerOk
    iintro %m %Φ %ci %cd %r !> %Ψ ⟨HS, Hctx, Hrc, Hr, HSpec⟩ HΨ
    iunfold grpcHandlerOkMd at Hh
    iapply Hh $$ %m %Φ %(fun _ => iprop(True)) %ci %cd %r [HS Hctx Hrc Hr HSpec]
    · ihave #Hrc' := Hrc
      iframe
      iframe #
      iapply (grpcSpecAt_md_intro Spec ci m Φ (fun _ => iprop(True)))
      iframe HSpec Hrc'
      imodintro
      iintro %_
      itrivial
    inext
    iintro %resp %err ⟨HS, Hok, -, #Hse⟩
    iapply HΨ
    iframe
    iexact Hse

/-- **A service method `h` that writes its request meets `Spec` with `S`** (persistent; the auth
plan's E3za): as `grpcHandlerOk`, also given what the run owns of the decoded request
(`Req.recvOwn r m`). -/
def grpcHandlerOwnOk {Req Rep : ProtoMsg GF} (h : val) (S : IProp GF) (Spec : GrpcSpec Req Rep) :
    IProp GF :=
  iprop(∀ (m : Req.M) (Φ : Rep.M → IProp GF) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (r : Loc),
    {{ S ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ Req.recv r m ∗ Req.recvOwn r m ∗ Spec m Φ }}
      (App (App (Val h) (Val #(GoInterface.ok ci))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        S ∗ (⌜err = GoInterface.nil⌝ -∗ ∃ m' : Rep.M, Rep.send resp m' ∗ Φ m') ∗
        go_etcd_io.etcd.cache.v3.srvErrOk err }})

instance grpcHandlerOwnOk_persistent {Req Rep : ProtoMsg GF} (h : val) (S : IProp GF)
    (Spec : GrpcSpec Req Rep) : Persistent (grpcHandlerOwnOk h S Spec) := by
  unfold grpcHandlerOwnOk; infer_instance

/-- **A service method `h` that writes its request meets the metadata-indexed `Spec` with `S`**
(persistent): as `grpcHandlerOwnOk`, at the run's metadata. -/
def grpcHandlerOwnOkMd {Req Rep : ProtoMsg GF} (h : val) (S : IProp GF)
    (Spec : GrpcSpecMd Req Rep) : IProp GF :=
  iprop(∀ (m : Req.M) (Φ : Rep.M → IProp GF) (Ψe : GoString → IProp GF) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (r : Loc),
    {{ S ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ Req.recv r m ∗ Req.recvOwn r m ∗
        grpcSpecAt Spec ci m Φ Ψe }}
      (App (App (Val h) (Val #(GoInterface.ok ci))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        S ∗ (⌜err = GoInterface.nil⌝ -∗ ∃ m' : Rep.M, Rep.send resp m' ∗ Φ m') ∗
        handlerErrOut Ψe err ∗ go_etcd_io.etcd.cache.v3.srvErrOk err }})

instance grpcHandlerOwnOkMd_persistent {Req Rep : ProtoMsg GF} (h : val) (S : IProp GF)
    (Spec : GrpcSpecMd Req Rep) : Persistent (grpcHandlerOwnOkMd h S Spec) := by
  unfold grpcHandlerOwnOkMd; infer_instance

/-- A method that does not write its request meets the metadata-indexed spec of one that may. -/
theorem grpcHandlerOkMd_own {Req Rep : ProtoMsg GF} (h : val) (S : IProp GF)
    (Spec : GrpcSpecMd Req Rep) :
    grpcHandlerOkMd h S Spec ⊢ grpcHandlerOwnOkMd h S Spec := by
  iintro #Hh
  unfold grpcHandlerOwnOkMd
  iintro %m %Φ %Ψe %ci %cd %r !> %Ψ ⟨HS, #Hctx, #Hrc, #Hr, -, HSpec⟩ HΨ
  iunfold grpcHandlerOkMd at Hh
  iapply Hh $$ %m %Φ %Ψe %ci %cd %r [HS HSpec] HΨ
  iframe; iframe #

/-- A method that does not write its request meets the spec of one that may. -/
theorem grpcHandlerOk_own {Req Rep : ProtoMsg GF} (h : val) (S : IProp GF)
    (Spec : GrpcSpec Req Rep) :
    grpcHandlerOk h S Spec ⊢ grpcHandlerOwnOk h S Spec := by
  iintro #Hh
  unfold grpcHandlerOwnOk
  iintro %m %Φ %ci %cd %r !> %Ψ ⟨HS, #Hctx, #Hrc, #Hr, -, HSpec⟩ HΨ
  iunfold grpcHandlerOk at Hh
  iapply Hh $$ %m %Φ %ci %cd %r [HS HSpec] HΨ
  iframe; iframe #

/-- An owning service method's plain spec is its spec at every metadata (the client's
`kv.Compact`, 2026-11-01; as `grpcHandlerOk_md`). -/
theorem grpcHandlerOwnOk_md [EtcdGrove.ErrorStringLeaf] {Req Rep : ProtoMsg GF} (h : val) (S : IProp GF)
    (Spec : GrpcSpec Req Rep) :
    grpcHandlerOwnOk h S Spec ⊣⊢ grpcHandlerOwnOkMd h S (GrpcSpec.md Spec) := by
  constructor
  · iintro #Hh
    unfold grpcHandlerOwnOkMd
    iintro %m %Φ %Ψe %ci %cd %r !> %Ψ ⟨HS, Hctx, Hrc, Hr, Hown, HSpec⟩ HΨ
    ihave ⟨HSpec, #Hall⟩ := grpcSpecAt_md_elim _ _ _ _ _ $$ HSpec
    iunfold grpcHandlerOwnOk at Hh
    iapply Hh $$ %m %Φ %ci %cd %r [HS Hctx Hrc Hr Hown HSpec]
    · iframe
    inext
    iintro %resp %err ⟨HS, Hok, #Hse⟩
    iapply HΨ
    iframe
    isplitl
    · iapply (handlerErrOut_allSrv _ err) $$ Hall Hse
    · iexact Hse
  · iintro #Hh
    unfold grpcHandlerOwnOk
    iintro %m %Φ %ci %cd %r !> %Ψ ⟨HS, Hctx, Hrc, Hr, Hown, HSpec⟩ HΨ
    iunfold grpcHandlerOwnOkMd at Hh
    iapply Hh $$ %m %Φ %(fun _ => iprop(True)) %ci %cd %r [HS Hctx Hrc Hr Hown HSpec]
    · ihave #Hrc' := Hrc
      iframe
      iframe #
      iapply (grpcSpecAt_md_intro Spec ci m Φ (fun _ => iprop(True)))
      iframe HSpec Hrc'
      imodintro
      iintro %_
      itrivial
    inext
    iintro %resp %err ⟨HS, Hok, -, #Hse⟩
    iapply HΨ
    iframe
    iexact Hse

/-- An owning service method meeting `Spec` with `S` meets it with more (as `grpcHandlerOk_frame`). -/
theorem grpcHandlerOwnOk_frame {Req Rep : ProtoMsg GF} (h : val) (S R : IProp GF)
    (Spec : GrpcSpec Req Rep) :
    grpcHandlerOwnOk h S Spec ⊢ grpcHandlerOwnOk h iprop(S ∗ R) Spec := by
  iintro #Hh
  unfold grpcHandlerOwnOk
  iintro %m %Φ %ci %cd %r !> %Ψ ⟨⟨HS, HR⟩, #Hctx, #Hrc, #Hr, Hown, HSpec⟩ HΨ
  iapply Hh $$ %m %Φ %ci %cd %r [HS Hown HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, Hres⟩
  iapply HΨ
  iframe

/-- A service method meeting `Spec` with `S` meets it with more (`S ∗ R`, `R` given back). -/
theorem grpcHandlerOk_frame {Req Rep : ProtoMsg GF} (h : val) (S R : IProp GF)
    (Spec : GrpcSpec Req Rep) :
    grpcHandlerOk h S Spec ⊢ grpcHandlerOk h iprop(S ∗ R) Spec := by
  iintro #Hh
  unfold grpcHandlerOk
  iintro %m %Φ %ci %cd %r !> %Ψ ⟨⟨HS, HR⟩, #Hctx, #Hrc, #Hr, HSpec⟩ HΨ
  iapply Hh $$ %m %Φ %ci %cd %r [HS HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, Hres⟩
  iapply HΨ
  iframe

/-- `grpcHandlerOk_frame`'s, for a metadata-indexed spec. -/
theorem grpcHandlerOkMd_frame {Req Rep : ProtoMsg GF} (h : val) (S R : IProp GF)
    (Spec : GrpcSpecMd Req Rep) :
    grpcHandlerOkMd h S Spec ⊢ grpcHandlerOkMd h iprop(S ∗ R) Spec := by
  iintro #Hh
  unfold grpcHandlerOkMd
  iintro %m %Φ %Ψe %ci %cd %r !> %Ψ ⟨⟨HS, HR⟩, #Hctx, #Hrc, #Hr, HSpec⟩ HΨ
  iapply Hh $$ %m %Φ %Ψe %ci %cd %r [HS HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, Hres⟩
  iapply HΨ
  iframe

/-! ## The server side: the generated handler, grpc's `dec`, the interceptor chain (unit P3b)

grpc's server (`server.go`, `processUnaryRPC`) runs, for a call of a registered unary method, the
`MethodDesc.Handler` of the registered `ServiceDesc` (etcd's generated `_KV_Put_Handler`, ...) on
the registered service value, the call's context, a `dec` closure that decodes the request into
the buffer it is given, and the server's interceptor: `nil` with no interceptor, else the chain
`chainUnaryServerInterceptors` composes (the interceptors in order, the first called with a
handler of grpc's making, `getChainUnaryHandler`, whose calls are the rest of the chain, the last
one's handler the generated handler's closure). -/

/-- **An interceptor's `info`** (the `*grpc.UnaryServerInfo` a generated handler allocates):
its `FullMethod`, read-only. -/
def srvInfoIs (info : Loc) : IProp GF :=
  iprop(∃ fm : GoString,
    structFieldRef google_golang_org.grpc.UnaryServerInfo go!"FullMethod" info ↦□ fm)

instance srvInfoIs_persistent (info : Loc) : Persistent (srvInfoIs (GF := GF) info) := by
  unfold srvInfoIs; infer_instance

/-- A unary handler's call `h(ctx, req)` (`grpc.UnaryHandler`). -/
abbrev srvHandlerCall (h : GoFunc) (ctx req : val) : Expr :=
  App (App (Val #h) (Val ctx)) (Val req)

/-- A server interceptor's call `ic(ctx, req, info, handler)` (`grpc.UnaryServerInterceptor`). -/
abbrev srvInterceptorCall (ic : GoFunc) (ctx req info : val) (h : GoFunc) : Expr :=
  App (App (App (App (Val #ic) (Val ctx)) (Val req)) (Val info)) (Val #h)

/-- A method handler's call `mh(srv, ctx, dec, interceptor)` (`grpc.MethodDesc.Handler`). -/
abbrev methodHandlerCall (mh srv ctx : val) (dec ui : GoFunc) : Expr :=
  App (App (App (App (Val mh) (Val srv)) (Val ctx)) (Val #dec)) (Val #ui)

/-- **The server's interceptor chain `ics` over the final handler `h`, with the resource `R`**
(grpc's `chainUnaryServerInterceptors`, `getChainUnaryHandler`; as `chainWP` on the client; the
resource parameter since 2026-11-23, #24's S2 signatures):
each call is given `R` and gives it back with its result (`R -∗ WP … {{ v, R ∗ Ψ v }}`). With no
interceptor, the call is `h`'s; otherwise the first interceptor is called with a handler `h'` of
grpc's making, whose calls are the rest of the chain's (with the same `info` and `R`). `Ψ` is the
call's postcondition. -/
def srvChainWP (R : IProp GF) (info : val) :
    List GoFunc → GoFunc → val → val → (val → IProp GF) → IProp GF
  | [], h, ctx, req, Ψ => iprop(R -∗ WP (srvHandlerCall h ctx req) {{ v, R ∗ Ψ v }})
  | ic :: ics, h, ctx, req, Ψ =>
    iprop(∀ h' : GoFunc,
      (□ ∀ (ctx' req' : val) (Ψ' : val → IProp GF),
        srvChainWP R info ics h ctx' req' Ψ' -∗
        R -∗ WP (srvHandlerCall h' ctx' req') {{ v, R ∗ Ψ' v }}) -∗
      R -∗ WP (srvInterceptorCall ic ctx req info h') {{ v, R ∗ Ψ v }})

/-- A postcondition's `True ∗` is dropped (the chains' calls at the trivial resource). -/
theorem wp_true_sep {s : Stuckness} {E : CoPset} {e : Expr} {Φ : val → IProp GF} :
    WP e @ s; E {{ v, iprop(True) ∗ Φ v }} ⊢ WP e @ s; E {{ Φ }} :=
  wp_mono (fun _ => by iintro ⟨-, H⟩; iexact H)

/-- A postcondition gains `True ∗` (the chains' calls at the trivial resource). -/
theorem wp_true_sep_intro {s : Stuckness} {E : CoPset} {e : Expr} {Φ : val → IProp GF} :
    WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, iprop(True) ∗ Φ v }} :=
  wp_mono (fun _ => by iintro H; iframe)

/-- **The interceptor grpc passes to a method handler, for the chain `ics`, with the resource `R`**
(persistent): `nil` for no interceptor; otherwise a non-nil interceptor whose calls, given `R`, are
the chain's at `R` (for one interceptor, the interceptor itself; for more, grpc's
`chainUnaryInterceptors` closure, `server.go:1227-1240`, which calls `interceptors[0]` with
`getChainUnaryHandler`'s closures, each calling the next interceptor or the final handler on the
same goroutine: they touch no resource, so the fact holds at every `R`, `grpcSrvChainAll`). -/
def grpcSrvChain (R : IProp GF) (ics : List GoFunc) (ui : GoFunc) : IProp GF :=
  match ics with
  | [] => iprop(⌜ui = func.nil⌝)
  | _ :: _ => iprop(⌜ui ≠ func.nil⌝ ∗ □ ∀ (ctx req info : val) (h : GoFunc) (Ψ : val → IProp GF),
      srvChainWP R info ics h ctx req Ψ -∗
      R -∗ WP (srvInterceptorCall ui ctx req info h) {{ v, R ∗ Ψ v }})

instance grpcSrvChain_persistent (R : IProp GF) (ics : List GoFunc) (ui : GoFunc) :
    Persistent (grpcSrvChain (GF := GF) R ics ui) := by
  unfold grpcSrvChain; cases ics <;> infer_instance

/-- **grpc's composed interceptor at every resource** (persistent; the Go fact a run is given,
`grpcAccepted`): `grpcSrvChain R ics ui` for every `R`. True of grpc-go v1.84: the composed
interceptor and the handlers `getChainUnaryHandler` makes are grpc's code, which allocates its
closures and calls the next interceptor (or the final handler) synchronously on the run's goroutine,
and touches no resource of the program's, so whatever the run holds (its `threadTok`, which the run
contract `grpcRunOkMd` gives it and takes back, or the loans it borrows with it) is the program's
to pass along. -/
def grpcSrvChainAll (ics : List GoFunc) (ui : GoFunc) : IProp GF :=
  iprop(□ ∀ R : IProp GF, grpcSrvChain R ics ui)

instance grpcSrvChainAll_persistent (ics : List GoFunc) (ui : GoFunc) :
    Persistent (grpcSrvChainAll (GF := GF) ics ui) := by
  unfold grpcSrvChainAll; infer_instance

/-- **grpc's `dec` for a call whose request is at `m`** (persistent; part of the trusted
runtime: the codec's unmarshaling of the request's bytes): called on a zero `*T` the caller owns
(`Req.blank`) of the method's request type, it decodes the request into it (`Req.recv l m`: the
decoded copy, read-only; `Req.recvOwn l m`: what the caller still owns of it) or fails, with an
error `status.FromError` accepts (`statusErrOk`; k8s etcd3 7c, HS-6: `serverStream.RecvMsg`'s
`*status.Error`s and the raw `io.ErrUnexpectedEOF` of its second `recv`, a leaf). That holds for
`Server.Serve`'s HTTP/2 transport only, the one `Server.Serve`'s axiom covers: under `ServeHTTP`,
`mapRecvMsgError` returns a raw `transport.ConnectionError`, not a leaf
(`notes/axiom-review/hs6.md`). -/
def grpcDecOk (dec : GoFunc) (Req : ProtoMsg GF) (m : Req.M) : IProp GF :=
  iprop(∀ l : Loc, {{ Req.blank l }}
      (App (Val #dec) (Val #(interface.mkOk (go.GoType.PointerType Req.ty) #l : GoInterface)))
    {{ (err : GoInterface), RET #err;
        (⌜err = GoInterface.nil⌝ ∗ Req.recv l m ∗ Req.recvOwn l m) ∨
          (notHandlerErr err ∗
            go_etcd_io.etcd.cache.v3.statusErrOk err) }})

instance grpcDecOk_persistent (dec : GoFunc) (Req : ProtoMsg GF) (m : Req.M) :
    Persistent (grpcDecOk dec Req m) := by
  unfold grpcDecOk; infer_instance

/-- grpc's `dec`, at the Go type `T` of the request (`Req.ty = T`). -/
theorem grpcDecOk_ty (dec : GoFunc) (Req : ProtoMsg GF) (m : Req.M) (T : go.GoType)
    (hT : Req.ty = T) :
    grpcDecOk (GF := GF) dec Req m ⊢ iprop(∀ l : Loc, {{ Req.blank l }}
      (App (Val #dec) (Val #(interface.mkOk (go.GoType.PointerType T) #l : GoInterface)))
    {{ (err : GoInterface), RET #err;
        (⌜err = GoInterface.nil⌝ ∗ Req.recv l m ∗ Req.recvOwn l m) ∨
          (notHandlerErr err ∗
            go_etcd_io.etcd.cache.v3.statusErrOk err) }}) := by
  subst hT; unfold grpcDecOk; exact .rfl

/-- **The method handler `mh` with the service `srv`, under the chain `ics`, meets `Spec` with
the per-run resource `S`** (persistent; unit P3b: what grpc's runtime runs for a call): a run,
given `S`, the run's context (`isContext`, `grpcRunCtx`), grpc's `dec` for the request at `m`,
the chain's interceptor (`grpcSrvChain`) and `Spec m Φ`, returns `S` and, on success, a response
`*T` (as `any`) at some `m'` with `Φ m'`. -/
def grpcMethodOk {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface) (ics : List GoFunc)
    (S : IProp GF) (Spec : GrpcSpec Req Rep) : IProp GF :=
  iprop(∀ (m : Req.M) (Φ : Rep.M → IProp GF) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (dec ui : GoFunc),
    {{ S ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ grpcDecOk dec Req m ∗ grpcSrvChainAll ics ui ∗
        Spec m Φ }}
      (methodHandlerCall mh #srv #(GoInterface.ok ci) dec ui)
    {{ (resp err : GoInterface), RET (PairV #resp #err); S ∗
        (⌜err = GoInterface.nil⌝ -∗ ∃ (l : Loc) (m' : Rep.M),
          ⌜resp = interface.mkOk (go.GoType.PointerType Rep.ty) #l⌝ ∗ Rep.send l m' ∗ Φ m') ∗
        go_etcd_io.etcd.cache.v3.srvErrOk err }})

instance grpcMethodOk_persistent {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface)
    (ics : List GoFunc) (S : IProp GF) (Spec : GrpcSpec Req Rep) :
    Persistent (grpcMethodOk mh srv ics S Spec) := by
  unfold grpcMethodOk; infer_instance

/-- **The method handler `mh` meets the metadata-indexed `Spec`** (persistent; the auth plan's
E3zb): as `grpcMethodOk`, the run's request precondition at its context's incoming metadata
(`grpcSpecAt`): what grpc delivers of the attempt's metadata. A plain spec's is
`grpcMethodOk` (`grpcMethodOk_md`). -/
def grpcMethodOkMd {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface) (ics : List GoFunc)
    (S : IProp GF) (Spec : GrpcSpecMd Req Rep) : IProp GF :=
  iprop(∀ (m : Req.M) (Φ : Rep.M → IProp GF) (Ψe : GoString → IProp GF) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (dec ui : GoFunc),
    {{ S ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ grpcDecOk dec Req m ∗ grpcSrvChainAll ics ui ∗
        grpcSpecAt Spec ci m Φ Ψe }}
      (methodHandlerCall mh #srv #(GoInterface.ok ci) dec ui)
    {{ (resp err : GoInterface), RET (PairV #resp #err); S ∗
        (⌜err = GoInterface.nil⌝ -∗ ∃ (l : Loc) (m' : Rep.M),
          ⌜resp = interface.mkOk (go.GoType.PointerType Rep.ty) #l⌝ ∗ Rep.send l m' ∗ Φ m') ∗
        handlerErrOut Ψe err ∗ go_etcd_io.etcd.cache.v3.srvErrOk err }})

instance grpcMethodOkMd_persistent {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface)
    (ics : List GoFunc) (S : IProp GF) (Spec : GrpcSpecMd Req Rep) :
    Persistent (grpcMethodOkMd mh srv ics S Spec) := by
  unfold grpcMethodOkMd; infer_instance

theorem grpcMethodOk_md [EtcdGrove.ErrorStringLeaf] {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface) (ics : List GoFunc)
    (S : IProp GF) (Spec : GrpcSpec Req Rep) :
    grpcMethodOk mh srv ics S Spec ⊣⊢ grpcMethodOkMd mh srv ics S (GrpcSpec.md Spec) := by
  constructor
  · iintro #Hh
    unfold grpcMethodOkMd
    iintro %m %Φ %Ψe %ci %cd %dec %ui !> %Ψ ⟨HS, Hctx, Hrc, Hd, Hch, HSpec⟩ HΨ
    ihave ⟨HSpec, #Hall⟩ := grpcSpecAt_md_elim _ _ _ _ _ $$ HSpec
    iunfold grpcMethodOk at Hh
    iapply Hh $$ %m %Φ %ci %cd %dec %ui [HS Hctx Hrc Hd Hch HSpec]
    · iframe
    inext
    iintro %resp %err ⟨HS, Hok, #Hse⟩
    iapply HΨ
    iframe
    isplitl
    · iapply (handlerErrOut_allSrv _ err) $$ Hall Hse
    · iexact Hse
  · iintro #Hh
    unfold grpcMethodOk
    iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨HS, Hctx, Hrc, Hd, Hch, HSpec⟩ HΨ
    iunfold grpcMethodOkMd at Hh
    iapply Hh $$ %m %Φ %(fun _ => iprop(True)) %ci %cd %dec %ui [HS Hctx Hrc Hd Hch HSpec]
    · ihave #Hrc' := Hrc
      iframe
      iframe #
      iapply (grpcSpecAt_md_intro Spec ci m Φ (fun _ => iprop(True)))
      iframe HSpec Hrc'
      imodintro
      iintro %_
      itrivial
    inext
    iintro %resp %err ⟨HS, Hok, -, #Hse⟩
    iapply HΨ
    iframe
    iexact Hse

/-- **The interceptor `ic` is transparent, with its per-run resource `R`, for requests with
`Q`** (persistent; unit P3b: what etcd's `newUnaryInterceptor` and `newLogUnaryInterceptor`
return, proved; what grpc-prometheus's is assumed to be): called with `R`, the run's context, a
request with `Q` (what the interceptor reads of it: etcd's learner check reads a
`*RangeRequest`'s `Serializable`), an `info` (`srvInfoIs`) and a handler `h`, it either calls `h`
once on the same context and request and returns its result, or returns `(nil, err)` for some
non-nil error without calling `h`; either way `R` comes back. It lends `R` to the handler's call
(per-type stage B, r5 §2.5): the handler's call takes `R` and gives it back with its result, and
the interceptor, done with it, hands it to the rest (`R -∗ Ψ v`). The caller gives both
continuations (`∧`: one is taken). -/
def srvInterceptorOk (ic : GoFunc) (R : IProp GF) (Q : GoInterface → IProp GF) : IProp GF :=
  iprop(□ ∀ (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (req : GoInterface)
      (info : Loc) (h : GoFunc) (Ψ : val → IProp GF),
    R -∗ context.isContext ci cd -∗ grpcRunCtx ci -∗ srvInfoIs info -∗ □ Q req -∗
    ((R -∗ WP (srvHandlerCall h #(GoInterface.ok ci) #req)
        {{ v, ∃ resp err : GoInterface, ⌜v = PairV #resp #err⌝ ∗
          go_etcd_io.etcd.cache.v3.srvErrOk err ∗ R ∗ (R -∗ Ψ v) }}) ∧
      (R -∗ ∀ err : GoInterface,
        notHandlerErr err -∗
        go_etcd_io.etcd.cache.v3.srvErrOk err -∗ Ψ (PairV #GoInterface.nil #err))) -∗
    WP (srvInterceptorCall ic #(GoInterface.ok ci) #req #info h) {{ Ψ }})

instance srvInterceptorOk_persistent (ic : GoFunc) (R : IProp GF) (Q : GoInterface → IProp GF) :
    Persistent (srvInterceptorOk (GF := GF) ic R Q) := by
  unfold srvInterceptorOk; infer_instance

/-- **Each interceptor of `ics` is transparent, with its resource in `Rs`, for requests with
`Q`** (persistent). -/
def srvInterceptorsOk (Q : GoInterface → IProp GF) : List GoFunc → List (IProp GF) → IProp GF
  | [], [] => iprop(True)
  | ic :: ics, R :: Rs => iprop(srvInterceptorOk ic R Q ∗ srvInterceptorsOk Q ics Rs)
  | _, _ => iprop(⌜False⌝)

instance srvInterceptorsOk_persistent (Q : GoInterface → IProp GF) (ics : List GoFunc)
    (Rs : List (IProp GF)) : Persistent (srvInterceptorsOk Q ics Rs) := by
  induction ics generalizing Rs with
  | nil => cases Rs <;> (unfold srvInterceptorsOk; infer_instance)
  | cons ic ics ih =>
    cases Rs with
    | nil => unfold srvInterceptorsOk; infer_instance
    | cons R Rs => unfold srvInterceptorsOk; have := ih Rs; infer_instance

/-- **A chain of transparent interceptors runs the handler or fails** (`srvChainWP` from the
interceptors' contracts), at any chain resource `R` (passed through: the interceptors' own
resources are `Rs`, lent along the chain as before the resource parameter): with the interceptors'
resources, the run's context, an `info`, and both continuations of the handler's call (its result,
the resources lent to it and back, or an early `(nil, err)` with them back), the chain's call meets
`Ψ`. -/
theorem srvChainWP_of_ok (R : IProp GF) (ics : List GoFunc) (Rs : List (IProp GF)) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (req : GoInterface) (info : Loc) (h : GoFunc)
    (Ψ : val → IProp GF) (Q : GoInterface → IProp GF) :
    srvInterceptorsOk Q ics Rs ∗ ([∗list] R ∈ Rs, R) ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗
      srvInfoIs info ∗ □ Q req ∗
      ((([∗list] R ∈ Rs, R) -∗ WP (srvHandlerCall h #(GoInterface.ok ci) #req)
          {{ v, ∃ resp err : GoInterface, ⌜v = PairV #resp #err⌝ ∗ go_etcd_io.etcd.cache.v3.srvErrOk err ∗
            ([∗list] R ∈ Rs, R) ∗ (([∗list] R ∈ Rs, R) -∗ Ψ v) }}) ∧
        (([∗list] R ∈ Rs, R) -∗ ∀ err : GoInterface,
          notHandlerErr err -∗
          go_etcd_io.etcd.cache.v3.srvErrOk err -∗ Ψ (PairV #GoInterface.nil #err))) ⊢
    srvChainWP R #info ics h #(GoInterface.ok ci) #req Ψ := by
  induction ics generalizing Rs Ψ with
  | nil =>
    cases Rs with
    | cons R0 Rs =>
      rw [show srvInterceptorsOk (GF := GF) Q [] (R0 :: Rs) = iprop(⌜False⌝) from rfl]
      iintro ⟨%H, -⟩; exact H.elim
    | nil =>
      iintro ⟨-, HRs, -, -, -, -, H⟩
      unfold srvChainWP
      iintro HR
      icases H with ⟨H, -⟩
      ispecialize H $$ HRs
      iapply wp_wand_r
      isplitl [H]
      · iexact H
      iintro %v ⟨%resp, %err, -, -, HRs, HΨ⟩
      iframe HR
      iapply HΨ $$ HRs
  | cons ic ics ih =>
    cases Rs with
    | nil =>
      rw [show srvInterceptorsOk (GF := GF) Q (ic :: ics) [] = iprop(⌜False⌝) from rfl]
      iintro ⟨%H, -⟩; exact H.elim
    | cons R0 Rs =>
      rw [show srvInterceptorsOk (GF := GF) Q (ic :: ics) (R0 :: Rs) =
        iprop(srvInterceptorOk ic R0 Q ∗ srvInterceptorsOk Q ics Rs) from rfl]
      iintro ⟨⟨#Hic, #Hoks⟩, HRs, #Hctx, #Hrc, #Hinfo, #HQ, H⟩
      ihave ⟨HR0, HRs⟩ := (BigSepL.bigSepL_cons (PROP := IProp GF) (Φ := fun _ R => R) (x := R0)
        (xs := Rs)).1 $$ HRs
      unfold srvChainWP
      iintro %h' #Hh' HR
      iunfold srvInterceptorOk at Hic
      iapply Hic $$ HR0 Hctx Hrc Hinfo HQ
      isplit
      · iintro HR0'
        iapply wp_wand_r
        isplitl [H HRs HR0' HR]
        · iapply Hh' $$ %_ %_ %(fun v => iprop(∃ resp err : GoInterface, ⌜v = PairV #resp #err⌝ ∗
            go_etcd_io.etcd.cache.v3.srvErrOk err ∗ R0 ∗ (R0 -∗ Ψ v))) [H HRs HR0'] HR
          iapply (ih Rs (fun v => iprop(∃ resp err : GoInterface, ⌜v = PairV #resp #err⌝ ∗
            go_etcd_io.etcd.cache.v3.srvErrOk err ∗ R0 ∗ (R0 -∗ Ψ v))))
          iframe #
          iframe HRs
          isplit
          · icases H with ⟨H, -⟩
            iintro HRs'
            ihave HRR := (BigSepL.bigSepL_cons (PROP := IProp GF) (Φ := fun _ R => R) (x := R0)
              (xs := Rs)).2 $$ [HR0' HRs']
            · iframe
            ispecialize H $$ HRR
            iapply (wp_mono (Φ := fun v => iprop(∃ resp err : GoInterface, ⌜v = PairV #resp #err⌝ ∗
              go_etcd_io.etcd.cache.v3.srvErrOk err ∗ ([∗list] R ∈ R0 :: Rs, R) ∗
              (([∗list] R ∈ R0 :: Rs, R) -∗ Ψ v)))) $$ H
            iintro %v ⟨%resp, %err, %Hv, #Hse, HRR, HΨ⟩
            ihave ⟨HR2, HRs2⟩ := (BigSepL.bigSepL_cons (PROP := IProp GF) (Φ := fun _ R => R) (x := R0)
              (xs := Rs)).1 $$ HRR
            iexists resp, err
            isplitr
            · ipureintro; exact Hv
            iframe Hse
            iframe HRs2
            iintro HRs3
            iexists resp, err
            isplitr
            · ipureintro; exact Hv
            iframe Hse
            iframe HR2
            iintro HR3
            iapply HΨ
            iapply (BigSepL.bigSepL_cons (PROP := IProp GF) (Φ := fun _ R => R) (x := R0) (xs := Rs)).2
            iframe
          · icases H with ⟨-, H⟩
            iintro HRs' %err #Herr #Hse
            iexists GoInterface.nil, err
            isplitr
            · ipureintro; rfl
            iframe Hse
            iframe HR0'
            iintro HR3
            iapply H $$ [HR3 HRs'] %err Herr Hse
            iapply (BigSepL.bigSepL_cons (PROP := IProp GF) (Φ := fun _ R => R) (x := R0) (xs := Rs)).2
            iframe
        iintro %v ⟨HR, %resp, %err, %Hv, #Hse, HR0, HΨ⟩
        iexists resp, err
        isplitr
        · ipureintro; exact Hv
        iframe Hse
        iframe HR0
        iintro HR0
        iframe HR
        iapply HΨ $$ HR0
      · icases H with ⟨-, H⟩
        iintro HR0' %err #Herr #Hse
        iframe HR
        iapply H $$ [HR0' HRs] %err Herr Hse
        iapply (BigSepL.bigSepL_cons (PROP := IProp GF) (Φ := fun _ R => R) (x := R0) (xs := Rs)).2
        iframe

end defs

/-! ## Per-type message models: the stores and the role-split registries (stage A, CP2) -/

section pertype
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A unary method's message model with its normalizing store (its tree is `ProtoMsg.tree` since
phase 7 S2's interface; `ProtoMsgT` adds no field and stays for the registries and `ReqSat`/`RepSat`). -/
structure ProtoMsgT (GF : BundledGFunctors) extends ProtoMsg GF

/-- **`own` is any struct** of the type at some Lean representation (the one the store's type is). -/
def OwnAny (ty : go.GoType) (own : Loc → IProp GF) : Prop :=
  ∃ (V : Type) (_ : ZeroVal V) (_ : TypedPointsto (GF := GF) V) (_ : IntoValTyped (GF := GF) V ty),
    ∀ l, own l ⊣⊢ ∃ v : V, l ↦ v

/-- **A request model is satisfiable** (`[v5]`). -/
def ProtoMsgT.ReqSat (T : ProtoMsgT GF) : Prop :=
  BlankZero T.ty T.blank ∧ OwnAny T.ty T.own ∧ (∀ m, T.send null m ⊢ False) ∧
  ∀ (ls l : Loc) (m : T.M),
    T.send ls m ∗ ⌜T.wireLen m < grpcMsgMax⌝ ∗ T.blank l ⊢
      WP (storeInto T.ty l (T.tree m)) {{ _v, T.send ls m ∗ T.recv l m ∗ T.recvOwn l m }}

/-- **A reply model is satisfiable** (`[v5]`): no `wireLen` premise. Since k8s 7e-1 (2026-11-10,
approved by etcd-grove-81) the store gives `recvOwn` too, as for a request: what of the decoded reply
the caller owns (`grpcInvokerOk`'s success post). -/
def ProtoMsgT.RepSat (T : ProtoMsgT GF) : Prop :=
  BlankZero T.ty T.blank ∧ OwnAny T.ty T.own ∧ (∀ m, T.send null m ⊢ False) ∧
  ∀ (ls l : Loc) (m : T.M),
    T.send ls m ∗ T.own l ⊢
      WP (storeInto T.ty l (T.tree m)) {{ _v, T.send ls m ∗ T.recv l m ∗ T.recvOwn l m }}

/-- A reply model whose `recvOwn` is the default `True` is satisfiable when its store gives `recv`
(the form of `RepSat` before k8s 7e-1). -/
theorem ProtoMsgT.repSat_of_recvOwn_true (T : ProtoMsgT GF)
    (hT : ∀ l m, T.recvOwn l m = iprop(True))
    (H : BlankZero T.ty T.blank ∧ OwnAny T.ty T.own ∧ (∀ m, T.send null m ⊢ False) ∧
      ∀ (ls l : Loc) (m : T.M),
        T.send ls m ∗ T.own l ⊢ WP (storeInto T.ty l (T.tree m)) {{ _v, T.send ls m ∗ T.recv l m }}) :
    T.RepSat := by
  obtain ⟨h1, h2, h3, h4⟩ := H
  refine ⟨h1, h2, h3, fun ls l m => (h4 ls l m).trans (wp_mono fun _ => ?_)⟩
  rw [hT]
  iintro ⟨H1, H2⟩
  isplitl [H1]
  · iexact H1
  isplitl [H2]
  · iexact H2
  itrivial

/-- **The registry of request models** (`[v5]`: split by role). -/
opaque grpcReqModelOf {hlc : HasLC} (GF : BundledGFunctors) [GooseExts] [GooseSemantics] [GooseInterp]
    [GoGlobalContext] [hG : HeapGS hlc GF] [go.Semantics] : go.GoType → Option (ProtoMsgT GF)

/-- **The registry of reply models**. -/
opaque grpcRepModelOf {hlc : HasLC} (GF : BundledGFunctors) [GooseExts] [GooseSemantics] [GooseInterp]
    [GoGlobalContext] [hG : HeapGS hlc GF] [go.Semantics] : go.GoType → Option (ProtoMsgT GF)

end pertype

section method
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A method a server registers**: its full name (`"/etcdserverpb.KV/Put"`), its message
types (registered, stage A: the request's model is the one `grpcReqModelOf` registers for its Go
type, the reply's the one `grpcRepModelOf` registers), its spec, the generated handler its
`ServiceDesc`'s `MethodDesc` holds (`etcdserverpb._KV_Put_Handler`), and the service value
registered with the `ServiceDesc` (`RegisterKVServer(s, srv)`'s `srv`, as `any`). -/
structure GrpcMethod (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] where
  name : GoString
  Req : ProtoMsgT GF
  Rep : ProtoMsgT GF
  spec : GrpcSpecMd Req.toProtoMsg Rep.toProtoMsg
  handler : GoFunc
  srv : GoInterface
  reqReg : grpcReqModelOf GF Req.ty = some Req
  repReg : grpcRepModelOf GF Rep.ty = some Rep

end method

/-! ## The opaque facts about grpc's runtime -/

/-! ## Go's configuration of a server -/

section cfg
variable [GooseExts]

/-- **Go's configuration of one gRPC server**: the unary and stream interceptor chains
`grpc.NewServer`'s options compose (`ics`, `sics`), and the `(full method name, handler, service
value)` of every registered method (`regs`) and stream (`sregs`) (`RegisterService`). A handler is
Go's `MethodDesc.Handler`/`StreamDesc.Handler`, a function value (`GoFunc`). Every `sregs` entry
comes from a stream descriptor that sets `ClientStreams` or `ServerStreams` (`RegisterService`'s
premise, B1b): grpc calls the handler of a descriptor with neither directly, without the stream
interceptor (`server.go:1446-1450`, test T10b), which the model does not represent. -/
structure GrpcSrvCfg (GF : BundledGFunctors) where
  ics : List GoFunc
  sics : List GoFunc
  regs : List (GoString × GoFunc × GoInterface)
  sregs : List (GoString × GoFunc × GoInterface)

/-- **The full names of `c`'s methods and streams are jointly distinct** (`grpc.start'`'s premise, M1:
what makes the one entry named by a call's path the handler Go's split lookup finds). -/
def grpcSrvNodup {GF : BundledGFunctors} (c : GrpcSrvCfg GF) : Prop :=
  ((c.regs ++ c.sregs).map Prod.fst).Nodup

end cfg

/-! ## The run contracts -/

section run
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The run contract of a unary handler**: `grpcMethodOkMd`'s text with the per-run resource fixed
to what a run is given, the fork's thread token and later credit (`wp_fork_tok_upd`), in the pre, and
the token in the post. A run, given the token and the credit, the run's context (`isContext`,
`grpcRunCtx`), grpc's `dec` for the request at `m`, the chain's interceptor (`grpcSrvChain`) and
`Spec md m Φ Ψe` at the context's incoming metadata, returns the token and, on success, a response
`*T` (as `any`) at some `m'` with `Φ m'`, on a handler's error its `Ψe`, and an error grpc's
`status.FromError` takes. Handlers are proved against `grpcMethodOkMd` at their bundle; the adapters
(`grpcRunOkMd_of_pools`) give this contract. Since 2026-11-23 (#24's S2 signatures) the chain's
interceptor is given at every resource (`grpcSrvChainAll`): the run holds its `threadTok`
throughout, from its fork to its return (grpc-go v1.84 runs each call's handler and its whole
interceptor chain on the goroutine `Server.handleStream` started for it, synchronously), and passes
what it holds, the token or the loans it borrows with it, along the chain. -/
def grpcRunOkMd {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface) (ics : List GoFunc)
    (Spec : GrpcSpecMd Req Rep) : IProp GF :=
  iprop(∀ (m : Req.M) (Φ : Rep.M → IProp GF) (Ψe : GoString → IProp GF) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (dec ui : GoFunc),
    {{ threadTok ∗ £ 1 ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ grpcDecOk dec Req m ∗
        grpcSrvChainAll ics ui ∗ grpcSpecAt Spec ci m Φ Ψe }}
      (methodHandlerCall mh #srv #(GoInterface.ok ci) dec ui)
    {{ (resp err : GoInterface), RET (PairV #resp #err); threadTok ∗
        (⌜err = GoInterface.nil⌝ -∗ ∃ (l : Loc) (m' : Rep.M),
          ⌜resp = interface.mkOk (go.GoType.PointerType Rep.ty) #l⌝ ∗ Rep.send l m' ∗ Φ m') ∗
        handlerErrOut Ψe err ∗ go_etcd_io.etcd.cache.v3.srvErrOk err }})

instance grpcRunOkMd_persistent {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface)
    (ics : List GoFunc) (Spec : GrpcSpecMd Req Rep) :
    Persistent (grpcRunOkMd mh srv ics Spec) := by
  unfold grpcRunOkMd; infer_instance

/-- A run contract at a spec is one at a stronger spec. -/
theorem grpcRunOkMd_mono {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface)
    (ics : List GoFunc) (Spec Spec' : GrpcSpecMd Req Rep)
    (h : ∀ md m Φ Ψe, Spec' md m Φ Ψe ⊢ Spec md m Φ Ψe) :
    grpcRunOkMd mh srv ics Spec ⊢ grpcRunOkMd mh srv ics Spec' := by
  iintro #Hm
  unfold grpcRunOkMd
  iintro %m %Φ %Ψe %ci %cd %dec %ui !> %Ψ ⟨HT, Hlc, Hctx, Hrc, Hd, Hch, HSpec⟩ HΨ
  iapply Hm $$ %m %Φ %Ψe %ci %cd %dec %ui [HT Hlc Hctx Hrc Hd Hch HSpec] HΨ
  iframe
  iapply (grpcSpecAt_mono Spec Spec' h ci m Φ Ψe) $$ HSpec

/-- A run contract at a spec is one at a spec that gives it after an update. -/
theorem grpcRunOkMd_mono_upd {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface)
    (ics : List GoFunc) (Spec Spec' : GrpcSpecMd Req Rep)
    (h : ∀ md m Φ Ψe, Spec' md m Φ Ψe ⊢ |==> Spec md m Φ Ψe) :
    grpcRunOkMd mh srv ics Spec ⊢ grpcRunOkMd mh srv ics Spec' := by
  iintro #Hm
  unfold grpcRunOkMd
  iintro %m %Φ %Ψe %ci %cd %dec %ui !> %Ψ ⟨HT, Hlc, Hctx, Hrc, Hd, Hch, HSpec⟩ HΨ
  ihave HSpec := (grpcSpecAt_mono_upd Spec Spec' h ci m Φ Ψe) $$ HSpec
  imod HSpec
  iapply Hm $$ %m %Φ %Ψe %ci %cd %dec %ui [HT Hlc Hctx Hrc Hd Hch HSpec] HΨ
  iframe

end run


/-- **The family of every resource** (`IProp GF → Prop`, the resource parameter's family): a
connection whose per-RPC credentials need no resource of their caller (none, or ones whose
contract holds at every `R`) takes any, `True` included. -/
abbrev anyRes {GF : BundledGFunctors} : IProp GF → Prop := fun _ => True

/-- **The client's connection `conn` reaches the servers at `addrs`, with the unary interceptors
`ics` and the default call options `dopts`** (persistent; an axiomatized predicate: a fact about
grpc's `*ClientConn` dialed to a resolver of the addresses `addrs`; unit P3a, it was
`isGrpcConn conn addr`, the interceptors inside the boundary; a list since 2026-10-21,
`notes/decisions.md` D27: each attempt goes to one of them, grpc's balancer's choice). `ics` is the chain `grpc.NewClient`/`Dial` compose
(`chainUnaryClientInterceptors`: `WithUnaryInterceptor`'s, then `WithChainUnaryInterceptor`'s, in
order), `dopts` the `WithDefaultCallOptions`. `Ok` (since 2026-11-23, #24's S2 signatures) is the
family of resources the connection's per-RPC credentials were dialed for (`perRPCCredsOk pc Ok Q`,
`grpc.NewClient`'s premise): a call on the connection (`Invoke`, `NewStream`, a stream's
`SendMsg`/`RecvMsg`/`CloseSend`) is given some `R` with `Ok R` by its caller, which grpc's attempts
lend the credentials (`grpcInvokerOk`, `cliStreamIs`). -/
axiom grpcConn {GF : BundledGFunctors} [GooseExts] (conn : Loc) (addrs : List GoString)
  (ics : List GoFunc) (dopts : List GoInterface) (Ok : IProp GF → Prop) : IProp GF

axiom grpcConn_persistent {GF : BundledGFunctors} [GooseExts] (conn : Loc) (addrs : List GoString)
    (ics : List GoFunc) (dopts : List GoInterface) (Ok : IProp GF → Prop) :
  Persistent (grpcConn (GF := GF) conn addrs ics dopts Ok)

attribute [instance] grpcConn_persistent

/-- **`v` is grpc's call option `grpc.Peer(p)`**: `PeerCallOption{PeerAddr: p}` as a `CallOption`
(grpc's `rpc_util.go`; `grpc.Peer`'s spec, `Spec/google_golang_org/grpc/Peer.lean`): after the call,
the attempt's peer is written to `*p`. (prove-grpcsmall, 2026-11-20) A definition since `grpc.Peer`
is translated and proved; it was an axiomatized property, introduced only by that spec. -/
def grpcPeerOpt [GooseExts] [GoGlobalContext] (v : GoInterface) (p : Loc) : Prop :=
  v = interface.mkOk google_golang_org.grpc.PeerCallOption.ty
    #(google_golang_org.grpc.PeerCallOption.mk p)

/-- **`pv` is a peer grpc's transport writes** for a call (an axiomatized property: its addresses
are `net`'s, its auth info grpc's credentials', so its `String()` returns). -/
axiom grpcWrotePeer [GooseExts] (pv : google_golang_org.grpc.peer.Peer) : Prop

/-! ## Metadata keys -/

/-- **Metadata's values at the key `k`** (`none` metadata: none). -/
def mdGet (md : GrpcMd) (k : GoString) : Option (List GoString) := md.bind fun m => m k

/-- **A key grpc sets itself** (the auth plan's C1): a pseudo-header (`:authority`, ...), a
`grpc-` key, `content-type`, `user-agent` (grpc's, before the caller's), `te`, and `host`, which
grpc's server deletes whenever `:authority` is present (gRFC A41; `http2_server.go:518-522`), as it
always is from grpc's client (`http2_client.go:595`): found by G2's axiom reviews,
`notes/axiom-review/g2-newstream.md`. What an attempt delivers at such a key is not stated. -/
def grpcReservedKey (k : GoString) : Prop :=
  go!":" <+: k ∨ go!"grpc-" <+: k ∨ k = go!"content-type" ∨ k = go!"user-agent" ∨ k = go!"te" ∨
    k = go!"host"

end EtcdGrove
end Perennial
