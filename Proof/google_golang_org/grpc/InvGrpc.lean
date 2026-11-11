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
configuration is Go's (`grpcSrvCfg γ c`, made only by `grpc.start` from `grpcSrvNew`), at the server
listening at `addr` (`grpcAddrIs addr γ`); `grpc.serve` (a theorem) packages it with the run
contracts into registrations. (Until B1b, `grpc.serve` was an axiom taking a caller-chosen run
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
stay until CP3): `ProtoMsgT`, a `ProtoMsg` with its normalizing store (`tree`, `Store.lean`); the
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
  /-- The sender's `*T` holding `m` (what marshaling needs; it comes back). -/
  send : Loc → M → IProp GF
  /-- **An upper bound on the length of the encoding** (`proto.Size`) of every message `send`
  holds at `m`, counting a submessage at each reference (as protobuf-go's `Size` does). Read it
  against `send`: every wire field must be pinned by `send`. Scope: the unknown fields of the
  messages `send` holds field by field (inside `txnReqAt` at every nested level, `createReqSend`,
  `userOptsAt`, `ownPermW`, the Lease replies' headers and `LeaseStatus` elements, and the watch
  stream's outer, cancel and progress messages) are not pinned; translated code never sets unknown fields (`SetUnknown` is not
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

/-- **A call's metadata** (as `metadata.incomingOf` gives a context's: `none`, or each key's
values). -/
abbrev GrpcMd : Type := Option (GoString → Option (List GoString))

/-- **The error descriptions only a handler makes** (k8s etcd3 stage 7c, `notes/k8s-etcd3-plan.md`,
"7c-1"): grpc forwards a status the server sends unchanged and never makes one of these itself, so
an attempt's error with one of them is the handler's own, with the handler's error outcome
(`grpcInvokerOk`): the two read errors', mvcc's future revision and compacted revision as
`togRPCError` maps them (k8s etcd3 7c-2 part 2, S7). -/
def handlerDescs : List GoString :=
  [go_etcd_io.etcd.cache.v3.futureRevDesc, go_etcd_io.etcd.cache.v3.compactedDesc]

/-- A handler's success holds its error outcome vacuously. -/
theorem handlerErr_nil (Ψe : GoString → IProp GF) :
    ⊢ (⌜GoInterface.nil ≠ GoInterface.nil ∧
        go_etcd_io.etcd.cache.v3.errDesc GoInterface.nil ∈ handlerDescs⌝ -∗
      Ψe (go_etcd_io.etcd.cache.v3.errDesc GoInterface.nil)) := by
  iintro %h
  exact absurd rfl h.1

/-- A caller's error outcome at every description holds at every error. -/
theorem handlerErr_all (Ψe : GoString → IProp GF) (err : GoInterface) :
    (□ ∀ d, Ψe d) ⊢ (⌜err ≠ GoInterface.nil ∧ go_etcd_io.etcd.cache.v3.errDesc err ∈ handlerDescs⌝ -∗
      Ψe (go_etcd_io.etcd.cache.v3.errDesc err)) := by
  iintro #H -
  iapply H

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
`mdIncomingKey{}` the `MD` its transport read from the stream's headers (`transportMD`), under
`peerKey{}` the transport's `*Peer` (`transportPeer`), nothing under `mdOutgoingKey{}` (only
`NewOutgoingContext`/`AppendToOutgoingContext` store there, which no server code here calls on a
run's context), and under otel's `currentSpanKey` nothing or otelgrpc's span (`otelSpan`). -/
def grpcRunCtx (ci : GoInterfaceOk) : IProp GF :=
  iprop((□ ∀ (n : GoString) (x : val) (Φ : val → IProp GF), ⌜etcdPkgPrefix <+: n⌝ →
    ▷ Φ #GoInterface.nil -∗
    WP (App (Val #(methods ci.ty go!"Value" ci.v))
      (Val #(interface.mkOk (go.GoType.Named n []) x : GoInterface))) {{ Φ }}) ∗
    trace.spanCtxOk ci ∗ context.libCtxOk ci)

instance grpcRunCtx_persistent (ci : GoInterfaceOk) : Persistent (grpcRunCtx (GF := GF) ci) := by
  unfold grpcRunCtx; infer_instance

/-- **A run's context has a span-key fact** (`grpcRunCtx`'s second part): what
`trace.SpanFromContext` needs of it. -/
theorem spanCtxOk_of_runCtx (ci : GoInterfaceOk) :
    grpcRunCtx (GF := GF) ci ⊢ trace.spanCtxOk ci := by
  iintro #H
  iunfold grpcRunCtx at H
  icases H with ⟨-, #H, -⟩
  iexact H

/-- **A run's context's library values are well formed** (`grpcRunCtx`'s third part). -/
theorem libCtxOk_of_runCtx (ci : GoInterfaceOk) :
    grpcRunCtx (GF := GF) ci ⊢ context.libCtxOk ci := by
  iintro #H
  iunfold grpcRunCtx at H
  icases H with ⟨-, -, #H⟩
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
(`metadata.incomingOf`). A plain spec's is `grpcHandlerOk` (`grpcHandlerOk_md`). -/
def grpcHandlerOkMd {Req Rep : ProtoMsg GF} (h : val) (S : IProp GF) (Spec : GrpcSpecMd Req Rep) :
    IProp GF :=
  iprop(∀ (m : Req.M) (Φ : Rep.M → IProp GF) (Ψe : GoString → IProp GF) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (r : Loc),
    {{ S ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ Req.recv r m ∗
        Spec (metadata.incomingOf (GoInterface.ok ci)) m Φ Ψe }}
      (App (App (Val h) (Val #(GoInterface.ok ci))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        S ∗ (⌜err = GoInterface.nil⌝ -∗ ∃ m' : Rep.M, Rep.send resp m' ∗ Φ m') ∗
        (⌜err ≠ GoInterface.nil ∧ go_etcd_io.etcd.cache.v3.errDesc err ∈ handlerDescs⌝ -∗
          Ψe (go_etcd_io.etcd.cache.v3.errDesc err)) ∗ go_etcd_io.etcd.cache.v3.srvErrOk err }})

instance grpcHandlerOkMd_persistent {Req Rep : ProtoMsg GF} (h : val) (S : IProp GF)
    (Spec : GrpcSpecMd Req Rep) : Persistent (grpcHandlerOkMd h S Spec) := by
  unfold grpcHandlerOkMd; infer_instance

theorem grpcHandlerOk_md {Req Rep : ProtoMsg GF} (h : val) (S : IProp GF)
    (Spec : GrpcSpec Req Rep) : grpcHandlerOk h S Spec ⊣⊢ grpcHandlerOkMd h S (GrpcSpec.md Spec) := by
  constructor
  · iintro #Hh
    unfold grpcHandlerOkMd
    iintro %m %Φ %Ψe %ci %cd %r !> %Ψ ⟨HS, Hctx, Hrc, Hr, HSpec, #Hall⟩ HΨ
    iunfold grpcHandlerOk at Hh
    iapply Hh $$ %m %Φ %ci %cd %r [HS Hctx Hrc Hr HSpec]
    · iframe
    inext
    iintro %resp %err ⟨HS, Hok, #Hse⟩
    iapply HΨ
    iframe
    isplitl
    · iintro %_
      iapply Hall
    · iexact Hse
  · iintro #Hh
    unfold grpcHandlerOk
    iintro %m %Φ %ci %cd %r !> %Ψ ⟨HS, Hctx, Hrc, Hr, HSpec⟩ HΨ
    iunfold grpcHandlerOkMd at Hh
    iapply Hh $$ %m %Φ %(fun _ => iprop(True)) %ci %cd %r [HS Hctx Hrc Hr HSpec]
    · simp only [GrpcSpec.md]
      iframe
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
        Spec (metadata.incomingOf (GoInterface.ok ci)) m Φ Ψe }}
      (App (App (Val h) (Val #(GoInterface.ok ci))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        S ∗ (⌜err = GoInterface.nil⌝ -∗ ∃ m' : Rep.M, Rep.send resp m' ∗ Φ m') ∗
        (⌜err ≠ GoInterface.nil ∧ go_etcd_io.etcd.cache.v3.errDesc err ∈ handlerDescs⌝ -∗
          Ψe (go_etcd_io.etcd.cache.v3.errDesc err)) ∗ go_etcd_io.etcd.cache.v3.srvErrOk err }})

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
theorem grpcHandlerOwnOk_md {Req Rep : ProtoMsg GF} (h : val) (S : IProp GF)
    (Spec : GrpcSpec Req Rep) :
    grpcHandlerOwnOk h S Spec ⊣⊢ grpcHandlerOwnOkMd h S (GrpcSpec.md Spec) := by
  constructor
  · iintro #Hh
    unfold grpcHandlerOwnOkMd
    iintro %m %Φ %Ψe %ci %cd %r !> %Ψ ⟨HS, Hctx, Hrc, Hr, Hown, HSpec, #Hall⟩ HΨ
    iunfold grpcHandlerOwnOk at Hh
    iapply Hh $$ %m %Φ %ci %cd %r [HS Hctx Hrc Hr Hown HSpec]
    · iframe
    inext
    iintro %resp %err ⟨HS, Hok, #Hse⟩
    iapply HΨ
    iframe
    isplitl
    · iintro %_
      iapply Hall
    · iexact Hse
  · iintro #Hh
    unfold grpcHandlerOwnOk
    iintro %m %Φ %ci %cd %r !> %Ψ ⟨HS, Hctx, Hrc, Hr, Hown, HSpec⟩ HΨ
    iunfold grpcHandlerOwnOkMd at Hh
    iapply Hh $$ %m %Φ %(fun _ => iprop(True)) %ci %cd %r [HS Hctx Hrc Hr Hown HSpec]
    · simp only [GrpcSpec.md]
      iframe
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

/-- **The server's interceptor chain `ics` over the final handler `h`** (grpc's
`chainUnaryServerInterceptors`, `getChainUnaryHandler`; as `chainWP` on the client): with no
interceptor, the call is `h`'s; otherwise the first interceptor is called with a handler `h'` of
grpc's making, whose calls are the rest of the chain's (with the same `info`). `Ψ` is the call's
postcondition. -/
def srvChainWP (info : val) : List GoFunc → GoFunc → val → val → (val → IProp GF) → IProp GF
  | [], h, ctx, req, Ψ => WP (srvHandlerCall h ctx req) {{ Ψ }}
  | ic :: ics, h, ctx, req, Ψ =>
    iprop(∀ h' : GoFunc,
      (□ ∀ (ctx' req' : val) (Ψ' : val → IProp GF),
        srvChainWP info ics h ctx' req' Ψ' -∗ WP (srvHandlerCall h' ctx' req') {{ Ψ' }}) -∗
      WP (srvInterceptorCall ic ctx req info h') {{ Ψ }})

/-- **The interceptor grpc passes to a method handler, for the chain `ics`** (persistent): `nil`
for no interceptor; otherwise a non-nil interceptor whose calls are the chain's (for one
interceptor, the interceptor itself; for more, grpc's `chainUnaryInterceptors` closure). -/
def grpcSrvChain (ics : List GoFunc) (ui : GoFunc) : IProp GF :=
  match ics with
  | [] => iprop(⌜ui = func.nil⌝)
  | _ :: _ => iprop(⌜ui ≠ func.nil⌝ ∗ □ ∀ (ctx req info : val) (h : GoFunc) (Ψ : val → IProp GF),
      srvChainWP info ics h ctx req Ψ -∗ WP (srvInterceptorCall ui ctx req info h) {{ Ψ }})

instance grpcSrvChain_persistent (ics : List GoFunc) (ui : GoFunc) :
    Persistent (grpcSrvChain (GF := GF) ics ui) := by
  unfold grpcSrvChain; cases ics <;> infer_instance

/-- **grpc's `dec` for a call whose request is at `m`** (persistent; part of the trusted
runtime: the codec's unmarshaling of the request's bytes): called on a zero `*T` the caller owns
(`Req.blank`) of the method's request type, it decodes the request into it (`Req.recv l m`: the
decoded copy, read-only; `Req.recvOwn l m`: what the caller still owns of it) or fails, with an
error `status.FromError` accepts (`statusErrOk`; k8s etcd3 7c, HS-6: `serverStream.RecvMsg`'s
`*status.Error`s and the raw `io.ErrUnexpectedEOF` of its second `recv`, a leaf). That holds for
`Server.Serve`'s HTTP/2 transport only, the one `grpc.start` covers: under `ServeHTTP`,
`mapRecvMsgError` returns a raw `transport.ConnectionError`, not a leaf
(`notes/axiom-review/hs6.md`). -/
def grpcDecOk (dec : GoFunc) (Req : ProtoMsg GF) (m : Req.M) : IProp GF :=
  iprop(∀ l : Loc, {{ Req.blank l }}
      (App (Val #dec) (Val #(interface.mkOk (go.GoType.PointerType Req.ty) #l : GoInterface)))
    {{ (err : GoInterface), RET #err;
        (⌜err = GoInterface.nil⌝ ∗ Req.recv l m ∗ Req.recvOwn l m) ∨
          (⌜err ≠ GoInterface.nil ∧ go_etcd_io.etcd.cache.v3.errDesc err ∉ handlerDescs⌝ ∗
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
          (⌜err ≠ GoInterface.nil ∧ go_etcd_io.etcd.cache.v3.errDesc err ∉ handlerDescs⌝ ∗
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
    {{ S ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ grpcDecOk dec Req m ∗ grpcSrvChain ics ui ∗
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
(`metadata.incomingOf`): what grpc delivers of the attempt's metadata. A plain spec's is
`grpcMethodOk` (`grpcMethodOk_md`). -/
def grpcMethodOkMd {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface) (ics : List GoFunc)
    (S : IProp GF) (Spec : GrpcSpecMd Req Rep) : IProp GF :=
  iprop(∀ (m : Req.M) (Φ : Rep.M → IProp GF) (Ψe : GoString → IProp GF) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (dec ui : GoFunc),
    {{ S ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ grpcDecOk dec Req m ∗ grpcSrvChain ics ui ∗
        Spec (metadata.incomingOf (GoInterface.ok ci)) m Φ Ψe }}
      (methodHandlerCall mh #srv #(GoInterface.ok ci) dec ui)
    {{ (resp err : GoInterface), RET (PairV #resp #err); S ∗
        (⌜err = GoInterface.nil⌝ -∗ ∃ (l : Loc) (m' : Rep.M),
          ⌜resp = interface.mkOk (go.GoType.PointerType Rep.ty) #l⌝ ∗ Rep.send l m' ∗ Φ m') ∗
        (⌜err ≠ GoInterface.nil ∧ go_etcd_io.etcd.cache.v3.errDesc err ∈ handlerDescs⌝ -∗
          Ψe (go_etcd_io.etcd.cache.v3.errDesc err)) ∗ go_etcd_io.etcd.cache.v3.srvErrOk err }})

instance grpcMethodOkMd_persistent {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface)
    (ics : List GoFunc) (S : IProp GF) (Spec : GrpcSpecMd Req Rep) :
    Persistent (grpcMethodOkMd mh srv ics S Spec) := by
  unfold grpcMethodOkMd; infer_instance

theorem grpcMethodOk_md {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface) (ics : List GoFunc)
    (S : IProp GF) (Spec : GrpcSpec Req Rep) :
    grpcMethodOk mh srv ics S Spec ⊣⊢ grpcMethodOkMd mh srv ics S (GrpcSpec.md Spec) := by
  constructor
  · iintro #Hh
    unfold grpcMethodOkMd
    iintro %m %Φ %Ψe %ci %cd %dec %ui !> %Ψ ⟨HS, Hctx, Hrc, Hd, Hch, HSpec, #Hall⟩ HΨ
    iunfold grpcMethodOk at Hh
    iapply Hh $$ %m %Φ %ci %cd %dec %ui [HS Hctx Hrc Hd Hch HSpec]
    · iframe
    inext
    iintro %resp %err ⟨HS, Hok, #Hse⟩
    iapply HΨ
    iframe
    isplitl
    · iintro %_
      iapply Hall
    · iexact Hse
  · iintro #Hh
    unfold grpcMethodOk
    iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨HS, Hctx, Hrc, Hd, Hch, HSpec⟩ HΨ
    iunfold grpcMethodOkMd at Hh
    iapply Hh $$ %m %Φ %(fun _ => iprop(True)) %ci %cd %dec %ui [HS Hctx Hrc Hd Hch HSpec]
    · simp only [GrpcSpec.md]
      iframe
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
non-nil error without calling `h`; either way `R` comes back. The caller gives both
continuations (`∧`: one is taken). -/
def srvInterceptorOk (ic : GoFunc) (R : IProp GF) (Q : GoInterface → IProp GF) : IProp GF :=
  iprop(□ ∀ (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (req : GoInterface)
      (info : Loc) (h : GoFunc) (Ψ : val → IProp GF),
    R -∗ context.isContext ci cd -∗ grpcRunCtx ci -∗ srvInfoIs info -∗ □ Q req -∗
    (WP (srvHandlerCall h #(GoInterface.ok ci) #req)
        {{ v, ∃ resp err : GoInterface, ⌜v = PairV #resp #err⌝ ∗ go_etcd_io.etcd.cache.v3.srvErrOk err ∗ (R -∗ Ψ v) }} ∧
      (R -∗ ∀ err : GoInterface,
        ⌜err ≠ GoInterface.nil ∧ go_etcd_io.etcd.cache.v3.errDesc err ∉ handlerDescs⌝ -∗
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
interceptors' contracts): with the interceptors' resources, the run's context, an `info`, and
both continuations of the handler's call (its result with the resources back, or an early
`(nil, err)` with them back), the chain's call meets `Ψ`. -/
theorem srvChainWP_of_ok (ics : List GoFunc) (Rs : List (IProp GF)) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (req : GoInterface) (info : Loc) (h : GoFunc)
    (Ψ : val → IProp GF) (Q : GoInterface → IProp GF) :
    srvInterceptorsOk Q ics Rs ∗ ([∗list] R ∈ Rs, R) ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗
      srvInfoIs info ∗ □ Q req ∗
      (WP (srvHandlerCall h #(GoInterface.ok ci) #req)
          {{ v, ∃ resp err : GoInterface, ⌜v = PairV #resp #err⌝ ∗ go_etcd_io.etcd.cache.v3.srvErrOk err ∗
            (([∗list] R ∈ Rs, R) -∗ Ψ v) }} ∧
        (([∗list] R ∈ Rs, R) -∗ ∀ err : GoInterface,
          ⌜err ≠ GoInterface.nil ∧ go_etcd_io.etcd.cache.v3.errDesc err ∉ handlerDescs⌝ -∗
          go_etcd_io.etcd.cache.v3.srvErrOk err -∗ Ψ (PairV #GoInterface.nil #err))) ⊢
    srvChainWP #info ics h #(GoInterface.ok ci) #req Ψ := by
  induction ics generalizing Rs Ψ with
  | nil =>
    cases Rs with
    | cons R Rs =>
      rw [show srvInterceptorsOk (GF := GF) Q [] (R :: Rs) = iprop(⌜False⌝) from rfl]
      iintro ⟨%H, -⟩; exact H.elim
    | nil =>
      iintro ⟨-, -, -, -, -, -, H⟩
      unfold srvChainWP
      icases H with ⟨H, -⟩
      iapply (wp_mono (Φ := fun v => iprop(∃ resp err : GoInterface, ⌜v = PairV #resp #err⌝ ∗
        go_etcd_io.etcd.cache.v3.srvErrOk err ∗ (([∗list] R ∈ ([] : List (IProp GF)), R) -∗ Ψ v)))) $$ H
      iintro %v ⟨%resp, %err, -, -, HΨ⟩
      iapply HΨ
      iapply BigSepL.bigSepL_nil.2
      itrivial
  | cons ic ics ih =>
    cases Rs with
    | nil =>
      rw [show srvInterceptorsOk (GF := GF) Q (ic :: ics) [] = iprop(⌜False⌝) from rfl]
      iintro ⟨%H, -⟩; exact H.elim
    | cons R Rs =>
      rw [show srvInterceptorsOk (GF := GF) Q (ic :: ics) (R :: Rs) =
        iprop(srvInterceptorOk ic R Q ∗ srvInterceptorsOk Q ics Rs) from rfl]
      iintro ⟨⟨#Hic, #Hoks⟩, HRs, #Hctx, #Hrc, #Hinfo, #HQ, H⟩
      ihave ⟨HR, HRs⟩ := (BigSepL.bigSepL_cons (PROP := IProp GF) (Φ := fun _ R => R) (x := R)
        (xs := Rs)).1 $$ HRs
      unfold srvChainWP
      iintro %h' #Hh'
      iunfold srvInterceptorOk at Hic
      iapply Hic $$ HR Hctx Hrc Hinfo HQ
      isplit
      · iapply Hh'
        iapply (ih Rs (fun v => iprop(∃ resp err : GoInterface, ⌜v = PairV #resp #err⌝ ∗
          go_etcd_io.etcd.cache.v3.srvErrOk err ∗ (R -∗ Ψ v))))
        iframe #
        iframe
        isplit
        · icases H with ⟨H, -⟩
          iapply (wp_mono (Φ := fun v => iprop(∃ resp err : GoInterface, ⌜v = PairV #resp #err⌝ ∗
            go_etcd_io.etcd.cache.v3.srvErrOk err ∗ (([∗list] R ∈ R :: Rs, R) -∗ Ψ v)))) $$ H
          iintro %v ⟨%resp, %err, %Hv, #Hse, HΨ⟩
          iexists resp, err
          isplitr
          · ipureintro; exact Hv
          iframe Hse
          iintro HRs'
          iexists resp, err
          isplitr
          · ipureintro; exact Hv
          iframe Hse
          iintro HR'
          iapply HΨ
          iapply (BigSepL.bigSepL_cons (PROP := IProp GF) (Φ := fun _ R => R) (x := R) (xs := Rs)).2
          iframe
        · icases H with ⟨-, H⟩
          iintro HRs' %err %Herr #Hse
          iexists GoInterface.nil, err
          isplitr
          · ipureintro; rfl
          iframe Hse
          iintro HR'
          iapply H $$ [HR' HRs'] %err %Herr Hse
          iapply (BigSepL.bigSepL_cons (PROP := IProp GF) (Φ := fun _ R => R) (x := R) (xs := Rs)).2
          iframe
      · icases H with ⟨-, H⟩
        iintro HR' %err %Herr #Hse
        iapply H $$ [HR' HRs] %err %Herr Hse
        iapply (BigSepL.bigSepL_cons (PROP := IProp GF) (Φ := fun _ R => R) (x := R) (xs := Rs)).2
        iframe

end defs

/-! ## Per-type message models: the stores and the role-split registries (stage A, CP2) -/

section pertype
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A unary method's message model with its normalizing store. -/
structure ProtoMsgT (GF : BundledGFunctors) extends ProtoMsg GF where
  tree : M → VTree

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

/-- **The full names of `c`'s methods and streams are jointly distinct** (`grpc.start`'s premise, M1:
what makes the one entry named by a call's path the handler Go's split lookup finds). -/
def grpcSrvNodup {GF : BundledGFunctors} (c : GrpcSrvCfg GF) : Prop :=
  ((c.regs ++ c.sregs).map Prod.fst).Nodup

end cfg

/-- **The server listening at `addr` is `γ`** (raw; see `grpcAddrIs`). Made only by `grpc.start` (and
carried to a bridge's address by `bridge.New`). `addr` is the exact string `grpc.start` listened on:
two strings for one socket (`":2379"`, `"127.0.0.1:2379"`) are different addresses here, so the
pair's "the server listening at `a`" assumes the client dials that string. -/
axiom grpcAddrIsRaw {GF : BundledGFunctors} (addr : List w8) (γ : GName) : IProp GF

/-- **Server `γ` was built with Go's configuration `c`** (raw). Made only by `grpc.start`, from
`grpcSrvNew gs c.ics c.sics _ c.regs c.sregs`: no registration is made after `Serve` starts (grpc
logs fatally on `RegisterService` after `Serve`, `server.go` `RegisterService`/`register`). -/
axiom grpcSrvCfgRaw {GF : BundledGFunctors} [GooseExts] (γ : GName) (c : GrpcSrvCfg GF) : IProp GF

/-- **The right to accept `γ`'s calls on `lis` through `gs`** (exclusive; made only by `grpc.start`;
`acceptRun` returns it with each accepted call, consumes it in its `lisFailed` arm, and drops it in
its `stopped` arm). -/
axiom grpcSrvLink {GF : BundledGFunctors} [GooseExts] (gs : Loc) (lis : GoInterface) (γ : GName) :
  IProp GF

/-- **The right to accept further calls on `gs`'s already-open connections** after its listener
failed (exclusive; made only by `acceptRun`'s `lisFailed` arm, one by each `lisFailed` return:
one per link consumed, so two `Serve` calls on one `gs` with two listeners can make two). -/
axiom grpcConnsLink {GF : BundledGFunctors} (gs : Loc) (γ : GName) : IProp GF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The server listening at `addr` is `γ`** (persistent by construction). -/
def grpcAddrIs (addr : GoString) (γ : GName) : IProp GF := iprop(□ grpcAddrIsRaw addr γ)

instance grpcAddrIs_persistent (addr : GoString) (γ : GName) :
    Persistent (grpcAddrIs (GF := GF) addr γ) := by
  unfold grpcAddrIs; infer_instance

/-- **Server `γ` was built with Go's configuration `c`** (persistent by construction). -/
def grpcSrvCfg (γ : GName) (c : GrpcSrvCfg GF) : IProp GF := iprop(□ grpcSrvCfgRaw γ c)

instance grpcSrvCfg_persistent (γ : GName) (c : GrpcSrvCfg GF) :
    Persistent (grpcSrvCfg (GF := GF) γ c) := by
  unfold grpcSrvCfg; infer_instance

end defs

section axioms
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **One server per address string.** True: `netAddrFree` allows one `Listen` per address in a run
(`Proof/net/InvNet.lean`), `grpc.start` consumes the listener, and `bridge.New` consumes the
bridge's own listener. Addresses are compared as strings (`grpcAddrIsRaw`): the law is used only at
one string, never to identify two spellings of one socket. (Restart's S10 must revisit this if a
`Stop` spec ever frees an address.) -/
axiom grpcAddrIs_agree (addr : GoString) (γ γ' : GName) :
  grpcAddrIs (GF := GF) addr γ ∗ grpcAddrIs addr γ' ⊢ ⌜γ = γ'⌝

/-- **One configuration per server**: `grpc.start` makes `grpcSrvCfg γ _` once per `γ`. -/
axiom grpcSrvCfg_agree (γ : GName) (c c' : GrpcSrvCfg GF) :
  grpcSrvCfg (GF := GF) γ c ∗ grpcSrvCfg γ c' ⊢ ⌜c = c'⌝
end axioms

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
(`grpcRunOkMd_of_pools`) give this contract. -/
def grpcRunOkMd {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface) (ics : List GoFunc)
    (Spec : GrpcSpecMd Req Rep) : IProp GF :=
  iprop(∀ (m : Req.M) (Φ : Rep.M → IProp GF) (Ψe : GoString → IProp GF) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (dec ui : GoFunc),
    {{ threadTok ∗ £ 1 ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ grpcDecOk dec Req m ∗
        grpcSrvChain ics ui ∗ Spec (metadata.incomingOf (GoInterface.ok ci)) m Φ Ψe }}
      (methodHandlerCall mh #srv #(GoInterface.ok ci) dec ui)
    {{ (resp err : GoInterface), RET (PairV #resp #err); threadTok ∗
        (⌜err = GoInterface.nil⌝ -∗ ∃ (l : Loc) (m' : Rep.M),
          ⌜resp = interface.mkOk (go.GoType.PointerType Rep.ty) #l⌝ ∗ Rep.send l m' ∗ Φ m') ∗
        (⌜err ≠ GoInterface.nil ∧ go_etcd_io.etcd.cache.v3.errDesc err ∈ handlerDescs⌝ -∗
          Ψe (go_etcd_io.etcd.cache.v3.errDesc err)) ∗ go_etcd_io.etcd.cache.v3.srvErrOk err }})

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
  iapply (h _ m Φ Ψe) $$ HSpec

/-- A run contract at a spec is one at a spec that gives it after an update. -/
theorem grpcRunOkMd_mono_upd {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface)
    (ics : List GoFunc) (Spec Spec' : GrpcSpecMd Req Rep)
    (h : ∀ md m Φ Ψe, Spec' md m Φ Ψe ⊢ |==> Spec md m Φ Ψe) :
    grpcRunOkMd mh srv ics Spec ⊢ grpcRunOkMd mh srv ics Spec' := by
  iintro #Hm
  unfold grpcRunOkMd
  iintro %m %Φ %Ψe %ci %cd %dec %ui !> %Ψ ⟨HT, Hlc, Hctx, Hrc, Hd, Hch, HSpec⟩ HΨ
  ihave HSpec := (h _ m Φ Ψe) $$ HSpec
  imod HSpec
  iapply Hm $$ %m %Φ %Ψe %ci %cd %dec %ui [HT Hlc Hctx Hrc Hd Hch HSpec] HΨ
  iframe

end run

/-! ## The registration and the accepted call -/

section reg
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The registration of `name` at server `γ`, as Go has it**: Go's configuration `c` lists
`(name, mh, srv)`, and the handler meets `Spec` under Go's chain, each run given a thread token and
one later credit and returning the token (`grpcRunOkMd`). -/
def isGrpcRpcAt {Req Rep : ProtoMsg GF} (γ : GName) (name : GoString) (Spec : GrpcSpecMd Req Rep) :
    IProp GF :=
  iprop(∃ (c : GrpcSrvCfg GF) (mh : GoFunc) (srv : GoInterface),
    grpcSrvCfg γ c ∗ ⌜(name, mh, srv) ∈ c.regs⌝ ∗ □ grpcRunOkMd #mh srv c.ics Spec)

instance isGrpcRpcAt_persistent {Req Rep : ProtoMsg GF} (γ : GName) (name : GoString)
    (Spec : GrpcSpecMd Req Rep) : Persistent (isGrpcRpcAt γ name Spec) := by
  unfold isGrpcRpcAt; infer_instance

/-- **The server listening at `addr` is `γ`, built with the unary chain `ics` and the unary methods
`regs`** (persistent; per-type stage B, B1b: it was an exclusive axiom): Go's configuration of `γ`
(`grpcSrvCfg`), whatever its stream chain and streams. Made by `grpc.start'` from `grpc.start`'s
facts. Several registrations of one Go handler at different specs are each a true fact about it. -/
def grpcServerAt (addr : GoString) (ics : List GoFunc)
    (regs : List (GoString × GoFunc × GoInterface)) (γ : GName) : IProp GF :=
  iprop(grpcAddrIs addr γ ∗ ∃ (sics : List GoFunc) (sregs : List (GoString × GoFunc × GoInterface)),
    grpcSrvCfg γ ({ ics := ics, sics := sics, regs := regs, sregs := sregs } : GrpcSrvCfg GF))

instance grpcServerAt_persistent (addr : GoString) (ics : List GoFunc)
    (regs : List (GoString × GoFunc × GoInterface)) (γ : GName) :
    Persistent (grpcServerAt (GF := GF) addr ics regs γ) := by
  unfold grpcServerAt; infer_instance

end reg

/-- **The client's connection `conn` reaches the servers at `addrs`, with the unary interceptors
`ics` and the default call options `dopts`** (persistent; an axiomatized predicate: a fact about
grpc's `*ClientConn` dialed to a resolver of the addresses `addrs`; unit P3a, it was
`isGrpcConn conn addr`, the interceptors inside the boundary; a list since 2026-10-21,
`notes/decisions.md` D27: each attempt goes to one of them, grpc's balancer's choice). `ics` is the chain `grpc.NewClient`/`Dial` compose
(`chainUnaryClientInterceptors`: `WithUnaryInterceptor`'s, then `WithChainUnaryInterceptor`'s, in
order), `dopts` the `WithDefaultCallOptions`. -/
axiom grpcConn {GF : BundledGFunctors} [GooseExts] (conn : Loc) (addrs : List GoString)
  (ics : List GoFunc) (dopts : List GoInterface) : IProp GF

axiom grpcConn_persistent {GF : BundledGFunctors} [GooseExts] (conn : Loc) (addrs : List GoString)
    (ics : List GoFunc) (dopts : List GoInterface) :
  Persistent (grpcConn (GF := GF) conn addrs ics dopts)

attribute [instance] grpcConn_persistent

/-- **`v` is grpc's call option `grpc.Peer(p)`** (an axiomatized property, introduced only by
`grpc.Peer`'s spec, `Spec/google_golang_org/grpc/Peer.lean`): after the call, the attempt's peer
is written to `*p`. -/
axiom grpcPeerOpt [GooseExts] (v : GoInterface) (p : Loc) : Prop

/-- **`pv` is a peer grpc's transport writes** for a call (an axiomatized property: its addresses
are `net`'s, its auth info grpc's credentials', so its `String()` returns). -/
axiom grpcWrotePeer [GooseExts] (pv : google_golang_org.grpc.peer.Peer) : Prop

section reg
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The method `name` of the server at `addr` meets the metadata-indexed `Spec`** (persistent;
the auth plan's E3zb; per-type stage B, B1b): the server listening at `addr` is some `γ`
(`grpcAddrIs`), and `γ`'s Go configuration registers `name` with a handler that meets `Spec` as a
run on a fork of grpc's (`isGrpcRpcAt`: the run contract `grpcRunOkMd`). -/
def isGrpcRpcMd {Req Rep : ProtoMsg GF} (addr name : GoString) (Spec : GrpcSpecMd Req Rep) :
    IProp GF :=
  iprop(∃ γ : GName, grpcAddrIs addr γ ∗ isGrpcRpcAt γ name Spec)

instance isGrpcRpcMd_persistent {Req Rep : ProtoMsg GF} (addr name : GoString)
    (Spec : GrpcSpecMd Req Rep) : Persistent (isGrpcRpcMd addr name Spec) := by
  unfold isGrpcRpcMd; infer_instance

/-- **The method `name` of the server at `addr` meets `Spec`** (persistent; see the file
header): `isGrpcRpcMd` at the plain spec (`GrpcSpec.md`). -/
def isGrpcRpc {Req Rep : ProtoMsg GF} (addr name : GoString) (Spec : GrpcSpec Req Rep) :
    IProp GF :=
  isGrpcRpcMd addr name (GrpcSpec.md Spec)

instance isGrpcRpc_persistent {Req Rep : ProtoMsg GF} (addr name : GoString)
    (Spec : GrpcSpec Req Rep) : Persistent (isGrpcRpc addr name Spec) := by
  unfold isGrpcRpc; infer_instance

theorem isGrpcRpc_md {Req Rep : ProtoMsg GF} (addr name : GoString) (Spec : GrpcSpec Req Rep) :
    isGrpcRpc addr name Spec ⊣⊢ isGrpcRpcMd addr name (GrpcSpec.md Spec) := .rfl

/-- **The method `name` of every server at `addrs` meets `Spec`** (persistent; D27): what a call
on a connection to `addrs` needs, wherever grpc's balancer sends the attempt. Reducible, by
recursion, so that at one address it is that address's `isGrpcRpc` (the one-endpoint clients' proofs
frame it as such). -/
@[reducible] def isGrpcRpcs {Req Rep : ProtoMsg GF} : List GoString → GoString → GrpcSpec Req Rep →
    IProp GF
  | [], _, _ => iprop(True)
  | [a], name, Spec => isGrpcRpc a name Spec
  | a :: b :: rest, name, Spec => iprop(isGrpcRpc a name Spec ∗ isGrpcRpcs (b :: rest) name Spec)

instance isGrpcRpcs_persistent {Req Rep : ProtoMsg GF} (addrs : List GoString) (name : GoString)
    (Spec : GrpcSpec Req Rep) : Persistent (isGrpcRpcs addrs name Spec) := by
  induction addrs with
  | nil => unfold isGrpcRpcs; infer_instance
  | cons a rest ih =>
    cases rest with
    | nil => unfold isGrpcRpcs; infer_instance
    | cons b bs => unfold isGrpcRpcs; infer_instance

/-- **The method `name` of every server at `addrs` meets the metadata-indexed `Spec`**
(persistent; as `isGrpcRpcs`). -/
@[reducible] def isGrpcRpcsMd {Req Rep : ProtoMsg GF} : List GoString → GoString →
    GrpcSpecMd Req Rep → IProp GF
  | [], _, _ => iprop(True)
  | [a], name, Spec => isGrpcRpcMd a name Spec
  | a :: b :: rest, name, Spec => iprop(isGrpcRpcMd a name Spec ∗ isGrpcRpcsMd (b :: rest) name Spec)

instance isGrpcRpcsMd_persistent {Req Rep : ProtoMsg GF} (addrs : List GoString) (name : GoString)
    (Spec : GrpcSpecMd Req Rep) : Persistent (isGrpcRpcsMd addrs name Spec) := by
  induction addrs with
  | nil => unfold isGrpcRpcsMd; infer_instance
  | cons a rest ih =>
    cases rest with
    | nil => unfold isGrpcRpcsMd; infer_instance
    | cons b bs => unfold isGrpcRpcsMd; infer_instance

theorem isGrpcRpcs_md {Req Rep : ProtoMsg GF} (addrs : List GoString) (name : GoString)
    (Spec : GrpcSpec Req Rep) :
    isGrpcRpcs addrs name Spec ⊣⊢ isGrpcRpcsMd addrs name (GrpcSpec.md Spec) := by
  induction addrs with
  | nil => exact .rfl
  | cons a rest ih =>
    cases rest with
    | nil => unfold isGrpcRpcs isGrpcRpcsMd; exact isGrpcRpc_md a name Spec
    | cons b bs =>
      unfold isGrpcRpcs isGrpcRpcsMd
      exact ⟨sep_mono (isGrpcRpc_md a name Spec).1 ih.1, sep_mono (isGrpcRpc_md a name Spec).2 ih.2⟩

/-- One address's registration is the registrations at the one-element list. -/
theorem isGrpcRpcs_singleton {Req Rep : ProtoMsg GF} (addr name : GoString)
    (Spec : GrpcSpec Req Rep) : isGrpcRpc addr name Spec ⊣⊢ isGrpcRpcs [addr] name Spec := by
  unfold isGrpcRpcs; exact .rfl

/-- The registrations at a list, from each address's. -/
theorem isGrpcRpcs_of_all {Req Rep : ProtoMsg GF} (addrs : List GoString) (name : GoString)
    (Spec : GrpcSpec Req Rep) :
    ([∗list] a ∈ addrs, isGrpcRpc a name Spec) ⊢ isGrpcRpcs addrs name Spec := by
  induction addrs with
  | nil => iintro -; unfold isGrpcRpcs; itrivial
  | cons a rest ih =>
    cases rest with
    | nil => iintro H; iapply (BigSepL.bigSepL_singleton (PROP := IProp GF)
        (Φ := fun _ a => isGrpcRpc a name Spec)).1 $$ H
    | cons b bs =>
      iintro H
      icases BigSepL.bigSepL_cons.1 $$ H with ⟨Ha, Hr⟩
      unfold isGrpcRpcs
      iframe Ha
      iapply ih $$ Hr

/-- A method meeting `Spec` meets a stronger request precondition `Spec'` (`Spec` occurs only in
the run's precondition). -/
theorem grpcMethodOk_mono {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface)
    (ics : List GoFunc) (S : IProp GF) (Spec Spec' : GrpcSpec Req Rep)
    (h : ∀ m Φ, Spec' m Φ ⊢ Spec m Φ) :
    grpcMethodOk mh srv ics S Spec ⊢ grpcMethodOk mh srv ics S Spec' := by
  iintro #Hm
  unfold grpcMethodOk
  iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨HS, Hctx, Hrc, Hd, Hch, HSpec⟩ HΨ
  iapply Hm $$ %m %Φ %ci %cd %dec %ui [HS Hctx Hrc Hd Hch HSpec] HΨ
  iframe
  iapply (h m Φ) $$ HSpec

/-- A method meeting the metadata-indexed `Spec` meets a stronger `Spec'`. -/
theorem grpcMethodOkMd_mono {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface)
    (ics : List GoFunc) (S : IProp GF) (Spec Spec' : GrpcSpecMd Req Rep)
    (h : ∀ md m Φ Ψe, Spec' md m Φ Ψe ⊢ Spec md m Φ Ψe) :
    grpcMethodOkMd mh srv ics S Spec ⊢ grpcMethodOkMd mh srv ics S Spec' := by
  iintro #Hm
  unfold grpcMethodOkMd
  iintro %m %Φ %Ψe %ci %cd %dec %ui !> %Ψ ⟨HS, Hctx, Hrc, Hd, Hch, HSpec⟩ HΨ
  iapply Hm $$ %m %Φ %Ψe %ci %cd %dec %ui [HS Hctx Hrc Hd Hch HSpec] HΨ
  iframe
  iapply (h _ m Φ Ψe) $$ HSpec

/-- A registration with the metadata-indexed `Spec` is one with a stronger `Spec'`. -/
theorem isGrpcRpcMd_mono {Req Rep : ProtoMsg GF} (addr name : GoString)
    (Spec Spec' : GrpcSpecMd Req Rep) (h : ∀ md m Φ Ψe, Spec' md m Φ Ψe ⊢ Spec md m Φ Ψe) :
    isGrpcRpcMd addr name Spec ⊢ isGrpcRpcMd addr name Spec' := by
  iintro #H
  iunfold isGrpcRpcMd at H
  icases H with ⟨%γ, #Ha, #H⟩
  iunfold isGrpcRpcAt at H
  icases H with ⟨%c, %mh, %srv, #Hc, %Hin, #Hm⟩
  unfold isGrpcRpcMd isGrpcRpcAt
  iexists γ
  iframe Ha
  iexists c, mh, srv
  iframe Hc
  isplitr
  · ipureintro; exact Hin
  imodintro
  iapply (grpcRunOkMd_mono #mh srv c.ics Spec Spec' h) $$ Hm

/-- A registration with `Spec` is one with a stronger request precondition `Spec'`. -/
theorem isGrpcRpc_mono {Req Rep : ProtoMsg GF} (addr name : GoString)
    (Spec Spec' : GrpcSpec Req Rep) (h : ∀ m Φ, Spec' m Φ ⊢ Spec m Φ) :
    isGrpcRpc addr name Spec ⊢ isGrpcRpc addr name Spec' := by
  unfold isGrpcRpc
  apply isGrpcRpcMd_mono
  intro md m Φ Ψe
  iintro ⟨H, #H'⟩
  isplitl [H]
  · iapply (h m Φ) $$ H
  iexact H'

/-- A method meeting the metadata-indexed `Spec` meets a `Spec'` that gives `Spec` after an update
(`Spec` is only the method triple's precondition, where an update is eliminated). -/
theorem grpcMethodOkMd_mono_upd {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface)
    (ics : List GoFunc) (S : IProp GF) (Spec Spec' : GrpcSpecMd Req Rep)
    (h : ∀ md m Φ Ψe, Spec' md m Φ Ψe ⊢ |==> Spec md m Φ Ψe) :
    grpcMethodOkMd mh srv ics S Spec ⊢ grpcMethodOkMd mh srv ics S Spec' := by
  iintro #Hm
  unfold grpcMethodOkMd
  iintro %m %Φ %Ψe %ci %cd %dec %ui !> %Ψ ⟨HS, Hctx, Hrc, Hd, Hch, HSpec⟩ HΨ
  ihave HSpec := (h _ m Φ Ψe) $$ HSpec
  imod HSpec
  iapply Hm $$ %m %Φ %Ψe %ci %cd %dec %ui [HS Hctx Hrc Hd Hch HSpec] HΨ
  iframe

/-- A registration with the metadata-indexed `Spec` is one with a `Spec'` that gives `Spec` after an
update. -/
theorem isGrpcRpcMd_mono_upd {Req Rep : ProtoMsg GF} (addr name : GoString)
    (Spec Spec' : GrpcSpecMd Req Rep) (h : ∀ md m Φ Ψe, Spec' md m Φ Ψe ⊢ |==> Spec md m Φ Ψe) :
    isGrpcRpcMd addr name Spec ⊢ isGrpcRpcMd addr name Spec' := by
  iintro #H
  iunfold isGrpcRpcMd at H
  icases H with ⟨%γ, #Ha, #H⟩
  iunfold isGrpcRpcAt at H
  icases H with ⟨%c, %mh, %srv, #Hc, %Hin, #Hm⟩
  unfold isGrpcRpcMd isGrpcRpcAt
  iexists γ
  iframe Ha
  iexists c, mh, srv
  iframe Hc
  isplitr
  · ipureintro; exact Hin
  imodintro
  iapply (grpcRunOkMd_mono_upd #mh srv c.ics Spec Spec' h) $$ Hm

/-- **Serving** (a theorem since per-type stage B, B1b; it was an axiom whose caller-chosen run
resource and count made every handler meet every spec, `axiom/grpc-serve-pool`): the methods `ms`
of the server at `addr` with the unary chain `ics` and the registrations `regs`
(`grpcServerAt`, made by `grpc.start'`), each registered with its handler and service and meeting
its run contract (`grpcRunOkMd`: a run on a fork of grpc's, given the fork's thread token and
later credit), are registered at `addr` (`isGrpcRpcMd`). What runs the handlers is `Server.Serve`
(its trusted model, `TrustedCode/google_golang_org/grpc.lean`). -/
theorem grpc.serve (addr : GoString) (ics : List GoFunc)
    (regs : List (GoString × GoFunc × GoInterface)) (ms : List (GrpcMethod GF)) (γ : GName) :
    (∀ m ∈ ms, (m.name, m.handler, m.srv) ∈ regs) →
    grpcServerAt addr ics regs γ ∗ □ ([∗list] m ∈ ms, grpcRunOkMd #m.handler m.srv ics m.spec) ⊢
    |={⊤}=> [∗list] m ∈ ms, isGrpcRpcMd addr m.name m.spec := by
  intro hreg
  iintro ⟨#Hs, #Hms⟩
  iunfold grpcServerAt at Hs
  icases Hs with ⟨#Ha, %sics, %sregs, #Hc⟩
  imodintro
  have Hm : iprop(□ (grpcAddrIs (GF := GF) addr γ ∗ grpcSrvCfg γ ({ ics := ics, sics := sics, regs := regs, sregs := sregs } : GrpcSrvCfg GF))) ⊢
      [∗list] m ∈ ms, (grpcRunOkMd #m.handler m.srv ics m.spec -∗ isGrpcRpcMd addr m.name m.spec) :=
    BigSepL.bigSepL_intro (fun _ m hk => by
      have hm : m ∈ ms := List.mem_of_getElem? hk
      iintro #⟨Ha, Hc⟩ #Hr
      unfold isGrpcRpcMd isGrpcRpcAt
      iexists γ
      iframe Ha
      iexists ({ ics := ics, sics := sics, regs := regs, sregs := sregs } : GrpcSrvCfg GF),
        m.handler, m.srv
      iframe Hc
      isplitr
      · ipureintro; exact hreg m hm
      imodintro
      iexact Hr)
  ihave Hw := Hm $$ []
  · imodintro; iframe #
  iapply BigSepL.bigSepL_wand $$ Hms Hw

/-! ## The client side: one attempt, the interceptor chain (unit P3a) -/

section client
variable [peer_sem : google_golang_org.grpc.peer.Assumptions]

/-- **The `*peer.Peer` `p`, owned, holding the zero peer or one grpc wrote** (what a `grpc.Peer(p)`
call option's attempt leaves there). -/
def grpcPeerBuf (p : Loc) : IProp GF :=
  iprop(∃ pv : google_golang_org.grpc.peer.Peer, p ↦ pv ∗
    ⌜pv = zero_val google_golang_org.grpc.peer.Peer ∨ grpcWrotePeer pv⌝)

theorem grpcPeerBuf_zero (p : Loc) :
    p ↦ zero_val google_golang_org.grpc.peer.Peer ⊢ grpcPeerBuf (GF := GF) p := by
  iintro Hp
  unfold grpcPeerBuf
  iexists _
  iframe
  ipureintro; left; rfl

/-- grpc's call options that hold only scalars (`StaticMethodCallOption`, `FailFastCallOption`,
`MaxSendMsgSizeCallOption`, `MaxRecvMsgSizeCallOption`: the generated stubs' and etcd's client's
`defaultCallOpts`; moved here from `client/v3/InvKVConn.lean`). -/
def grpcScalarOptTys : List go.GoType :=
  [google_golang_org.grpc.StaticMethodCallOption.ty, google_golang_org.grpc.FailFastCallOption.ty,
    google_golang_org.grpc.MaxSendMsgSizeCallOption.ty,
    google_golang_org.grpc.MaxRecvMsgSizeCallOption.ty]

/-- **A call option an attempt takes**, given the peer buffers `ps`: one holding only scalars, or
a `grpc.Peer(p)` option for a `p` of `ps` (whose buffer the attempt is given). -/
def grpcOptOk (ps : List Loc) (v : GoInterface) : Prop :=
  (∃ (t : go.GoType) (x : val), v = interface.mkOk t x ∧ t ∈ grpcScalarOptTys) ∨
    ∃ p ∈ ps, grpcPeerOpt v p

/-- An invoker's call `inv(ctx, method, req, reply, cc, opts...)` (`grpc.UnaryInvoker`). -/
abbrev invokerCall (inv : GoFunc) (ctx method req reply cc opts : val) : Expr :=
  App (App (App (App (App (App (Val #inv) (Val ctx)) (Val method)) (Val req)) (Val reply))
    (Val cc)) (Val opts)

/-- An interceptor's call `ic(ctx, method, req, reply, cc, inv, opts...)`
(`grpc.UnaryClientInterceptor`). -/
abbrev interceptorCall (ic : GoFunc) (ctx method req reply cc : val) (inv : GoFunc) (opts : val) :
    Expr :=
  App (App (App (App (App (App (App (Val #ic) (Val ctx)) (Val method)) (Val req)) (Val reply))
    (Val cc)) (Val #inv)) (Val opts)

/-- **A context's `Deadline()` returns** (persistent; premise fixes 8, N1, approved by
etcd-grove-81): some time and flag, without panicking. grpc's client calls it on every call
(`stream.go:520,586`), and its transport on the call's child context, which delegates to it
(`http2_client.go:573,619,1312`). Any value will do: grpc only compares it with the clock
(`time.Until`, `Time.After`), and a deadline in the past ends the attempt with a status error, as for
an `isContext` with a deadline. -/
def ctxDeadline (ci : GoInterfaceOk) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ (t : _root_.Perennial.time.Time) (b : Bool), Φ (PairV #t #b)) -∗
    WP (App (Val #(methods ci.ty go!"Deadline" ci.v)) (Val #())) {{ Φ }})

instance ctxDeadline_persistent (ci : GoInterfaceOk) : Persistent (ctxDeadline (GF := GF) ci) := by
  unfold ctxDeadline; infer_instance

/-- **A context `context.WithCancel` can take as a parent outside Perennial's model** (persistent;
premise fixes 8, N2 and N3, approved by etcd-grove-81). Go's `propagateCancel` (go1.27.3
`context.go`), once the parent's `Done()` is not nil, calls `parentCancelCtx(parent)`, which calls
`parent.Value(&cancelCtxKey)` and dereferences the result if it is a `*cancelCtx` (a nil one panics:
`TestClientCallCtxPanics`' `errsNilCancelCtx`), then type-asserts `parent.(afterFuncer)` and calls its
`AfterFunc` if that succeeds; `Cause(parent)` calls `Value(&cancelCtxKey)` too. So: `Value` at
`&cancelCtxKey` returns something that is not a `*cancelCtx` (`parentCancelCtx` and `Cause` find
none), and the dynamic type is not in `afterFuncer`'s type set (the assertion fails: Goose's
`type_assert2_interface_step` decides it by `typeSetContains`, which `go_type_set` evaluates from the
type's method set; Go's own rule, an `AfterFunc` of another signature does not satisfy it). Then
`propagateCancel` starts its goroutine, which only calls `Done()`, `Err()` and `Cause` (`ctxDone`,
`ctxErrsErr`, this). -/
def ctxWithCancelOk (ci : GoInterfaceOk) : IProp GF :=
  iprop(EtcdGrove.context.valueAt ci _root_.Perennial.context.cancelCtxKeyAny
      (fun v => ∀ vi : GoInterfaceOk, v = GoInterface.ok vi →
        vi.ty ≠ go.GoType.PointerType _root_.Perennial.context.cancelCtx.ty) ∗
    ⌜go.typeSetContains ci.ty _root_.Perennial.context.afterFuncer.ty = false⌝)

instance ctxWithCancelOk_persistent (ci : GoInterfaceOk) :
    Persistent (ctxWithCancelOk (GF := GF) ci) := by
  unfold ctxWithCancelOk; infer_instance

/-- **A context that is never done: its `Done()` returns the nil channel and its `Err()` returns
`nil`** (persistent; the vertical slice's unit V2): `context.TODO()` and `context.Background()` (an
`emptyCtx`: `Done()` is `nil`, `Err()` is `nil`), and value contexts over them (`valueCtx` delegates
`Done` and `Err` to its parent: `withVersion`'s metadata context). Not an `isContext` (whose `Done()`
is a channel). (Premise fixes 5, 2026-11-10, approved by etcd-grove-81) With `Done()`: until then
only `Err()` was stated, so the axioms taking `ctxOk` that select on `ctx.Done()`
(`waitRetryBackoff`, grpc's `Invoke` and `NewStream`) covered a context whose `Done()` panics or is
closed while `Err()` is `nil`, on which Go panics (`notes/axiom-review/ctxok-done.md`). (Premise
fixes 8, N1, approved by etcd-grove-81) With `Deadline()` (`ctxDeadline`), which grpc calls on every
call. No `Value`/`AfterFunc` clause: with a nil `Done()`, `propagateCancel` returns at once. -/
def ctxQuiet (ci : GoInterfaceOk) : IProp GF :=
  iprop((□ ∀ Φ : val → IProp GF, ▷ Φ #chan.nil -∗
      WP (App (Val #(methods ci.ty go!"Done" ci.v)) (Val #())) {{ Φ }}) ∗
    (□ ∀ Φ : val → IProp GF, ▷ Φ #(GoInterface.nil) -∗
      WP (App (Val #(methods ci.ty go!"Err" ci.v)) (Val #())) {{ Φ }}) ∗
    ctxDeadline ci)

instance ctxQuiet_persistent (ci : GoInterfaceOk) : Persistent (ctxQuiet (GF := GF) ci) := by
  unfold ctxQuiet; infer_instance

/-- **The `Err()` half of `ctxErrs`: Go's contract of `Err()`, with client errors** (persistent; 2026-11-04,
K4 of `notes/k8s-compactor-plan.md`, the user's approval): `Err()` returns `nil`, or, once the
context is done (`ContextClosed cd.Done_gn`), a non-nil error; a non-nil error means it is done, and
is a client error grpc's `status` accepts (`clientErr`, `statusErrOk`, `errCellOk`: true of
`context.Canceled` and `DeadlineExceeded`, the only errors Go lets `Err()` return), whose
description is not a handler's (`handlerDescs`; k8s etcd3 7c, HS-5 (a), approved by the user
2026-11-06 via etcd-grove-82: grpc returns `status.FromContextError(ctx.Err())`, which keeps the
message, so an attempt's error would carry it with no handler run). The client's `ctxErrClient` has this body (`ctxErrClient_eq_errs`); `ctxErrs` adds `Done()`'s (`ctxDone`, premise fixes 5). It is what a context
outside Perennial's model meets: k8s's `wait.ContextForChannel(stopCh)` (a `channelContext`, whose
`Done()` is `stopCh` and whose `Err()` is `Canceled` once `stopCh` is closed; not an `isContext`,
whose `parentCancelCtx` finds a `*cancelCtx`). -/
def ctxErrsErr (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) : IProp GF :=
  iprop(□ ∀ (cl : Broadcast) (Φ : val → IProp GF),
    (match cl with
     | .Done => context.ContextClosed cd.Done_gn
     | _ => iprop(True)) -∗
    ▷ (∀ err : GoInterface,
        (match cl with
         | .Done => iprop(⌜err ≠ interface.nil⌝)
         | _ => if err = interface.nil then iprop(True)
                else context.ContextClosed cd.Done_gn) -∗
        ⌜clientErr err⌝ -∗ go_etcd_io.etcd.cache.v3.statusErrOk err -∗
        go_etcd_io.etcd.cache.v3.errCellOk err -∗
        ⌜err = interface.nil ∨ go_etcd_io.etcd.cache.v3.errDesc err ∉ handlerDescs⌝ -∗ Φ #err) -∗
    WP (App (Val #(methods ci.ty go!"Err" ci.v)) (Val #())) {{ Φ }})

instance ctxErrsErr_persistent (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    Persistent (ctxErrsErr (GF := GF) ci cd) := by
  unfold ctxErrsErr; infer_instance

/-- **`ch` is a Done channel of a context described by `cd`** (persistent; premise fixes 5,
2026-11-10, approved by etcd-grove-81): the nil channel (a receive from it never proceeds), or a
broadcast channel (only ever closed; `isBroadcastChanInternal`, whose done flag holds once it is
closed) whose done flag means the context is done (`ContextClosed cd.Done_gn`; then `Err()` is not
`nil`, `ctxErrsErr`'s `.Done` case). Go's contract: "If Done is closed, Err returns a non-nil
error". -/
def ctxDoneCh (cd : context.ContextDesc (IProp GF)) (ch : GoChan) : IProp GF :=
  iprop(⌜ch = chan.nil⌝ ∨ ∃ (γ : ChanNames) (γi : BroadcastInternalNames) (Q : IProp GF),
    isBroadcastChanInternal ch γ γi Q ∗
    □ (dghostVar γi.doneGn DFrac.discard true -∗ context.ContextClosed cd.Done_gn))

instance ctxDoneCh_persistent (cd : context.ContextDesc (IProp GF)) (ch : GoChan) :
    Persistent (ctxDoneCh (GF := GF) cd ch) := by
  unfold ctxDoneCh; infer_instance

/-- **A context's `Done()` returns, without panicking, a Done channel** (`ctxDoneCh`; persistent;
premise fixes 5). -/
def ctxDone (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ ch : GoChan, ctxDoneCh cd ch -∗ Φ #ch) -∗
    WP (App (Val #(methods ci.ty go!"Done" ci.v)) (Val #())) {{ Φ }})

instance ctxDone_persistent (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    Persistent (ctxDone (GF := GF) ci cd) := by
  unfold ctxDone; infer_instance

/-- **A context that follows Go's contract, with client errors** (persistent; 2026-11-04, K4 of
`notes/k8s-compactor-plan.md`): its `Done()` returns a Done channel (`ctxDone`: nil, or one whose
closing means the context is done; premise fixes 5, 2026-11-10, approved by etcd-grove-81: until
then nothing about `Done()`, `notes/axiom-review/ctxok-done.md`), and its `Err()` follows Go's
contract with client errors (`ctxErrsErr`). It is what a context outside Perennial's model meets:
k8s's `wait.ContextForChannel(stopCh)` (`chanCtx_ok`). (Premise fixes 8, N1-N3, approved by
etcd-grove-81) And its `Deadline()` returns (`ctxDeadline`), and `WithCancel` can take it as a parent
(`ctxWithCancelOk`: `Value(&cancelCtxKey)` is no `*cancelCtx`, no `AfterFunc`). -/
def ctxErrs (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) : IProp GF :=
  iprop(ctxDone ci cd ∗ ctxErrsErr ci cd ∗ ctxDeadline ci ∗ ctxWithCancelOk ci)

instance ctxErrs_persistent (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    Persistent (ctxErrs (GF := GF) ci cd) := by
  unfold ctxErrs; infer_instance

/-- **A context a client call takes** (persistent; the vertical slice's unit V2): one with the
context model (`isContext`), a quiet one (`ctxQuiet`: `context.TODO()`, which the recipes pass
to every call), or (2026-11-04) one whose `Err()` follows Go's contract with client errors
(`ctxErrs`: k8s's `wait.ContextForChannel`, Kubernetes' compactor's). grpc's `invoke` and etcd's
client interceptor accept any: the trust boundary's contracts below (`grpcInvokerOk`; the
client's `withVersion`, `waitRetryBackoff`) are stated for `ctxOk`, true of Go's quiet contexts as
of the others (a `nil` `Done()` channel never fires; grpc turns a done context's error into a
status error, `status.FromContextError`, and `waitRetryBackoff` likewise, `contextErrToGRPCErr`;
since premise fixes 5 each case states `Done()`, which these select on);
the client's token fetch (`getToken`, `refreshToken`) also takes `ctxErrClient` (its
`ContextError`). (Premise fixes 8, approved by etcd-grove-81) In every case, its outgoing
metadata is grpc's (`metadata.outgoingCtxOkC`, the chain form, `Proof/context/LibKeysChain.lean`):
grpc reads it on every call (`stream.go:322,513`, `http2_client.go:579,940`), and etcd's
`withVersion` itself. -/
def ctxOk (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) : IProp GF :=
  iprop((context.isContext ci cd ∨ ctxQuiet ci ∨ ctxErrs ci cd) ∗ metadata.outgoingCtxOkC ci)

instance ctxOk_persistent (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    Persistent (ctxOk (GF := GF) ci cd) := by
  unfold ctxOk; infer_instance

theorem ctxOk_of_isContext (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    context.isContext (GF := GF) ci cd ∗ metadata.outgoingCtxOkC ci ⊢ ctxOk ci cd := by
  iintro ⟨#H, #Ho⟩; unfold ctxOk; iframe Ho; ileft; iexact H

theorem ctxOk_of_errs (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    ctxErrs (GF := GF) ci cd ∗ metadata.outgoingCtxOkC ci ⊢ ctxOk ci cd := by
  iintro ⟨#H, #Ho⟩; unfold ctxOk; iframe Ho; iright; iright; iexact H

theorem ctxOk_of_quiet (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    ctxQuiet (GF := GF) ci ∗ metadata.outgoingCtxOkC ci ⊢ ctxOk ci cd := by
  iintro ⟨#H, #Ho⟩; unfold ctxOk; iframe Ho; iright; ileft; iexact H

/-- `ctxOk`'s outgoing-metadata clause. -/
theorem ctxOk_outgoingC (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    ctxOk (GF := GF) ci cd ⊢ metadata.outgoingCtxOkC ci := by
  iintro #H; unfold ctxOk; icases H with ⟨-, #Ho⟩; iexact Ho

/-- **A method of etcd's KV service** (`/etcdserverpb.KV/Range`, `Put`, `DeleteRange`, `Txn`,
`Compact`: the full method names grpc sends; 2026-10-23). -/
def kvMethod (method : GoString) : Prop := go!"/etcdserverpb.KV/" <+: method

/-- **The server at `addr` never answers a unary call of etcd's KV service with a refusal**
(opaque; D29, 2026-10-21; narrowed to the KV service 2026-10-23): no status it sends in answer to a
`kvMethod` call has a description among `refusalDescs`. Established by the trust-boundary axiom of
etcd's members (`etcd_noRefusal`), carried by the network's relays (linkv3p's `forwards`), and read
by the attempt contract (`grpcInvokerOk`) for a `kvMethod` call only. Until 2026-10-23 it covered
every status the server sends, which is false of etcd: its Auth service answers `UserAdd` of an
empty name with `"etcdserver: user name is empty"` even with authentication off
(`authStore.UserAdd`). -/
opaque noRefusalAt : GoString → Prop

/-- **The non-auth refusals** (F-S2, 2026-10-29): the learner's (`isSafeRetry`) and the old
balancer's two (`isSafeRetryMutableRPC`), the members of `refusalDescs` that do not depend on
authentication. -/
def otherRefusalDescs : List GoString :=
  [go!"etcdserver: rpc not supported for learner",
    go!"there is no address available", go!"there is no connection available"]

theorem otherRefusalDescs_sub (d : GoString) (h : d ∈ otherRefusalDescs) :
    d ∈ go_etcd_io.etcd.cache.v3.refusalDescs := by
  simp [otherRefusalDescs] at h; rcases h with rfl | rfl | rfl <;>
    simp [go_etcd_io.etcd.cache.v3.refusalDescs]

/-- **The server at `addr` never answers a unary call of etcd's KV service with a non-auth
refusal** (opaque; F-S2, 2026-10-29): no status it sends in answer to a `kvMethod` call has a
description among `otherRefusalDescs`. Established in either auth mode by the trust-boundary axiom
`etcd_noOtherRefusal`; `noRefusalAt`'s half that does not depend on authentication. Not read yet:
the attempt contract (`grpcInvokerOk`) is to read it with the auth refusals' identity proved in the
server's error branches (`notes/auth-mode-merge-plan.md`, F-S2 part 2). -/
opaque noOtherRefusalAt : GoString → Prop

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

/-- **The per-RPC credentials of the connection `conn` returned the metadata `cm` to an attempt**
(opaque; the auth plan's C1, 2026-10-28): `none` if it has none or they returned none; what is
known of `cm` is the credentials' contract at the dial (`grpc.NewClient`'s `connCredsOk`). -/
opaque credsYield (conn : Loc) (cm : GrpcMd) : Prop

/-- **The handler of an attempt on the connection `conn` with the caller's context `ctx` sees the
metadata `md`** (the auth plan's E3zb; a definition since C1, 2026-10-28, until then opaque): on
every key grpc does not set itself, the values of the connection's per-RPC credentials' metadata
`cm` for the attempt (`credsYield`), then the context's outgoing metadata (`metadata.outgoingOf`);
and no key with no values (grpc writes one header field per value, so a key the context carries
with none is not sent; C1's review, F2). True of grpc-go v1.84 (`http2Client.createHeaderFields`,
to check in C1's phase 2); the attempt contract (`grpcInvokerOk`) gives the method's spec at such
an `md`. -/
def grpcAttemptMd [GooseExts] (conn : Loc) (ctx : GoInterface) (md : GrpcMd) : Prop :=
  ∃ cm, credsYield conn cm ∧
    (∀ k, ¬ grpcReservedKey k →
      metadata.mdVals md k = metadata.mdVals cm k ++ metadata.mdVals (metadata.outgoingOf ctx) k) ∧
    ∀ k, mdGet md k ≠ some []

/-- **One attempt** (persistent; the contract of grpc's `invoke`, the final invoker of a
connection's interceptor chain; unit P3a): a call of a method registered at every address `addrs`
of the connection with `Spec` (`isGrpcRpcs`; D27, 2026-10-21: the attempt goes to one of them),
for the request `inp` (`Req.send`, given back), into the reply `out` (owned, at any content:
`Rep.own`), with call options grpc can apply (`grpcOptOk ps`: scalar, or peer options writing the
buffers `ps`, owned and given back) and the caller's `▷ Spec md m Φ` for every metadata `md` the
attempt's handler may see (`grpcAttemptMd`; since 2026-10-28, the auth plan's E3zb, the spec is
metadata-indexed, `GrpcSpecMd`: a plain spec is `GrpcSpec.md`), returns
* `nil`: a run of the handler served for the method at one of `addrs` on a copy of the request
  answered, and `out` holds the reply's copy of its response (`Rep.recv out m'`) with the run's `Φ m'`;
* an error: a client error (`clientErr`: a leaf error, possibly an `EtcdError`; a gRPC status error)
  that grpc's `status` accepts (`statusErrOk`), and `out` back (`Rep.own`); nothing about whether
  the handler ran, except (k8s etcd3 7c-1) for an error whose description only a handler makes
  (`handlerDescs`): the caller's error outcome `Ψe` at it, which the handler's run gave.

Since 2026-10-19 (D21 M6, D21j, the user's choice) the request's precondition is ordinary (until
then `□ ▷ Spec m Φ`, persistent): an attempt delivers the request to at most one run of the
handler. True of grpc-go: an attempt is one HTTP/2 stream, its request written once; grpc's
transparent retry re-sends only a stream the server never handed to its application
(`REFUSED_STREAM`, a `GOAWAY` past the stream), and etcd's client configures no retry policy and
no hedging. This restates what the axiom `grpc.ClientConn.Invoke` promises (through this
definition); no axiom is added.

Since 2026-10-21 (D29, the user's choice) the error is not a refusal (`noRefusal`: its
description is none of `refusalDescs`, the descriptions after which etcd's client resends a write)
when every address of the connection is refusal-free (`noRefusalAt`) and (2026-10-23) the method is
one of etcd's KV service (`kvMethod`), the calls `noRefusalAt` speaks of. True of grpc-go: a status
the server sends is forwarded unchanged (`grpc-status`, `grpc-message`), and grpc's own errors
carry grpc's messages (neither of the old balancer's two strings occurs in grpc v1.84's sources;
the four etcd strings are etcd's). Again a restatement of `grpc.ClientConn.Invoke`'s promise.

Since 2026-10-23 (D37) the error is no caller's `errors.New` value (`errCellOk`: if it is an
`*errors.errorString`, its cell holds `"EOF"`). True of grpc-go v1.84: `invoke` returns what
`newClientStream`, `SendMsg`, `CloseSend` and `RecvMsg` return, each through `toRPCErr`
(`rpc_util.go`), which passes `nil` and `io.EOF` (io's `errors.New("EOF")`) through and turns
every other error into a status error (`*status.Error`), except one `status.FromError` already
accepts, whose dynamic type is then not `*errors.errorString` (an `errorString` has no
`GRPCStatus` method and no `Unwrap`); its own errors are status errors (`status.Error`).

Since 2026-10-30 (the axiom review `txn-nested-wire`) the request's encoding is below `grpcMsgMax`
(`Req.wireLen`): grpc marshals before it checks a size, and the codec's allocation panics above
Go's `maxAlloc`.

Since stage A of the per-type models (2026-11-07, `notes/per-type-blockers.md`) the request's and
the reply's models are the ones registered for their Go types (`grpcReqModelOf`,
`grpcRepModelOf`): a caller cannot choose a model of its own, and each registered model's
`ProtoMsgT.ReqSat`/`RepSat` is proved.

Since k8s 7e-1 (2026-11-10, approved by etcd-grove-81) the error's dynamic type is one of
`clientErrTys` (through `clientErr`): `*status.Error` (`toRPCErr`, `status.Error`,
`status.FromContextError`), `*errors.errorString` (`io.EOF`), and the two other types of the list,
which no attempt returns. True of grpc-go v1.84 under etcd's configuration only, the bounds of this
claim: no dial option beyond `GrpcDialOpt`'s (`dialOptsAt`), per-RPC credentials that return no
error (`perRPCCredsOk`: a credentials error carrying a status is returned unchanged, or wrapped with
`%w`, `http2_client.go:697-702`), and a service config without a retry policy (`grpcResolverAt`:
an exhausted retry policy wraps the last error, `stream.go:867`). The evidence for this
attempt-level claim is `examples/k8s7e1attack` (the axiom-skill attack programs): `invoker`'s
`TestTypes` calls the bare invoker the way etcd's interceptor gets it and requires `nil` or
`*status.Error` for a server status, a context canceled or expired before or during the attempt, a
closed and a refused connection (and prints the out-of-bounds cases: a credentials error carrying a
status, or wrapping one, and an exhausted retry policy, which `retrycx` shows for a stream);
`eof` shows `io.EOF`'s and `status.Error`'s types. `examples/k8s/etcd3`'s `TestClientErrorTypes` (gates
9c) observes only the client's results, after `ContextError` and `rpctypes.Error` have converted the
attempt's error: evidence for the post-processed types (`clientErr`), not for this claim.

Since k8s 7e-1 (2026-11-10, approved by etcd-grove-81) a success also gives the caller what the
reply's model says it owns of the decoded reply (`Rep.recvOwn out m'`; `RepSat` proves the store
gives it; for `RangeResponse` the `Kvs` slice's cells, which Kubernetes' store overwrites). True of
grpc-go v1.84 with protobuf-go v2 under these bounds only: `EnableTracing` is false (grpc's package
fact `grpcInit`, which `ClientConn.Invoke`'s `isPkgInit` carries; with tracing on, grpc keeps every
reply, `stream.go` `LazyLog(&payload{msg: m})`, and formats it later on `/debug/requests`: a data
race with the caller's writes, reproduced by the attack's `TestTracingRace`,
`notes/k8s-7e-1-handoff.md`); grpc's default proto codec (`proto.Unmarshal` resets the reply and
decodes a repeated message field into a fresh array, bytes fields copied out of the receive buffer);
no stats handler or interceptor keeping the reply (`InPayload.Payload`; `dialOptsAt` admits none,
etcd's interceptors keep nothing); reply types protobuf-go v2 generated code (no custom `Unmarshal`).
Checked by `examples/k8s/etcd3`'s `TestDefaultNoRace` (`-race`, in the gates). -/
def grpcInvokerOk (conn : Loc) (addrs : List GoString) (inv : GoFunc) : IProp GF :=
  iprop(□ ∀ (method : GoString) (Req Rep : ProtoMsgT GF)
      (_ : grpcReqModelOf GF Req.ty = some Req) (_ : grpcRepModelOf GF Rep.ty = some Rep)
      (Spec : GrpcSpecMd Req.toProtoMsg Rep.toProtoMsg) (m : Req.M)
      (Φ : Rep.M → IProp GF) (Ψe : GoString → IProp GF) (ctx : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF))
      (inp out : Loc) (opts : GoSlice) (vs : List GoInterface) (ps : List Loc),
    {{ isGrpcRpcsMd addrs method Spec ∗
        ▷ (∀ md, ⌜grpcAttemptMd conn (GoInterface.ok ctx) md⌝ -∗ Spec md m Φ Ψe) ∗
        ctxOk ctx cd ∗ Req.send inp m ∗ ⌜Req.wireLen m < grpcMsgMax⌝ ∗
        Rep.own out ∗ opts ↦*□ vs ∗ ⌜∀ v ∈ vs, grpcOptOk ps v⌝ ∗ ([∗list] p ∈ ps, grpcPeerBuf p) }}
      (invokerCall inv #(GoInterface.ok ctx) #method
        #(interface.mkOk (go.GoType.PointerType Req.ty) #inp : GoInterface)
        #(interface.mkOk (go.GoType.PointerType Rep.ty) #out : GoInterface) #conn #opts)
    {{ (err : GoInterface), RET #err; Req.send inp m ∗ ([∗list] p ∈ ps, grpcPeerBuf p) ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ m' : Rep.M, Rep.recv out m' ∗ Rep.recvOwn out m' ∗ Φ m') ∨
          (⌜err ≠ GoInterface.nil ∧ clientErr err⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk err ∗
            go_etcd_io.etcd.cache.v3.errCellOk err ∗ Rep.own out ∗
            ⌜(kvMethod method ∧ ∀ a ∈ addrs, noRefusalAt a) →
              go_etcd_io.etcd.cache.v3.noRefusal err⌝ ∗
            (⌜go_etcd_io.etcd.cache.v3.errDesc err ∈ handlerDescs⌝ -∗
              Ψe (go_etcd_io.etcd.cache.v3.errDesc err)))) }})

instance grpcInvokerOk_persistent (conn : Loc) (addrs : List GoString) (inv : GoFunc) :
    Persistent (grpcInvokerOk (GF := GF) conn addrs inv) := by
  unfold grpcInvokerOk; infer_instance

/-- **Per-RPC credentials' metadata**: `GetRequestMetadata`'s map `mp` (a `map[string]string`;
`nil` for none) as metadata `cm`, each key with its one value (the auth plan's C1), its keys
lower-case (grpc lower-cases them, `http2Client.getTrAuthData`; C1's review, F3: the metadata
grpc sends is then the map's). -/
def credsMapIs (mp : Loc) (cm : GrpcMd) : IProp GF :=
  iprop(⌜mp = null ∧ cm = none⌝ ∨ ∃ m : GMap GoString GoString,
    ownMap mp DFrac.discard m ∗
    ⌜cm = (some fun k => (m !! k).map fun v => [v]) ∧ ∀ k v, m !! k = some v → metadata.lowerKey k⌝)

/-- **The per-RPC credentials `pc` return metadata meeting `Q`** (persistent; the auth plan's C1,
2026-10-28): each call of `pc.GetRequestMetadata(ctx, uri...)` returns no error (k8s 7e-1,
2026-11-10, a soundness fix decided by etcd-grove-81: it allowed any error whose description is not a
handler's, but grpc-go v1.84 returns a credentials error that carries a status, or wraps one with
`%w`, unchanged as the attempt's (`http2_client.go:697-702`), a `*fmt.wrapError` or the caller's own
type: neither a leaf nor of `clientErrTys`, so `grpcInvokerOk`/`cliStreamErr` overclaimed under such
credentials; etcd's `perRPCCredential` returns `nil`), and, a map whose metadata `cm` has `□ Q cm` (what grpc sends with an attempt, `connCredsOk`); and
`pc.RequireTransportSecurity()` can be called (grpc calls it at the dial to refuse credentials that
need a secure transport on an insecure one; C1's review, F4). -/
def perRPCCredsOk (pc : GoInterface) (Q : GrpcMd → IProp GF) : IProp GF :=
  iprop((□ ∀ (ctx : GoInterface) (sl : GoSlice),
    {{ True }}
      (App (App (App (Val (GoInstruction (MethodResolve
          google_golang_org.grpc.credentials.PerRPCCredentials.ty go!"GetRequestMetadata")))
        (Val #pc)) (Val #ctx)) (Val #sl))
    {{ (mp : Loc) (err : GoInterface), RET (PairV #mp #err);
        ⌜err = GoInterface.nil⌝ ∗
        (⌜err = GoInterface.nil⌝ -∗ ∃ cm, credsMapIs mp cm ∗ □ Q cm) }}) ∗
    □ {{ True }}
      (App (App (Val (GoInstruction (MethodResolve
          google_golang_org.grpc.credentials.PerRPCCredentials.ty go!"RequireTransportSecurity")))
        (Val #pc)) (Val #()))
    {{ (b : Bool), RET #b; True }})

instance perRPCCredsOk_persistent (pc : GoInterface) (Q : GrpcMd → IProp GF) :
    Persistent (perRPCCredsOk pc Q) := by
  unfold perRPCCredsOk; infer_instance

/-- **What the per-RPC credentials `pcs` of the connection `conn` returned to its attempts**
(persistent; the auth plan's C1, 2026-10-28; `grpc.NewClient`'s post, from the credentials'
contract at the dial, `perRPCCredsOk`): with no credentials, nothing (`none`); with one, metadata
meeting `Q`; with more, nothing is stated. -/
def connCredsOk (conn : Loc) (pcs : List GoInterface) (Q : GrpcMd → IProp GF) : IProp GF :=
  match pcs with
  | [] => iprop(⌜∀ cm, credsYield conn cm → cm = none⌝)
  | [_] => iprop(□ ∀ cm, ⌜credsYield conn cm⌝ -∗ □ Q cm)
  | _ => iprop(True)

instance connCredsOk_persistent (conn : Loc) (pcs : List GoInterface) (Q : GrpcMd → IProp GF) :
    Persistent (connCredsOk conn pcs Q) := by
  unfold connCredsOk; split <;> infer_instance

/-- **The interceptor chain `ics` over the final invoker `inv`** (unit P3a; grpc's
`chainUnaryClientInterceptors`, `getChainUnaryInvoker`): with no interceptor, the call is `inv`'s;
otherwise the first interceptor is called with an invoker `inv'` of grpc's making, whose calls
(on the same connection) are the rest of the chain's. `Ψ` is the call's postcondition. -/
def chainWP (conn : Loc) : List GoFunc → GoFunc → val → val → val → val → val →
    (val → IProp GF) → IProp GF
  | [], inv, ctx, method, req, reply, opts, Ψ =>
    WP (invokerCall inv ctx method req reply #conn opts) {{ Ψ }}
  | ic :: ics, inv, ctx, method, req, reply, opts, Ψ =>
    iprop(∀ inv' : GoFunc,
      (□ ∀ (ctx' method' req' reply' opts' : val) (Ψ' : val → IProp GF),
        chainWP conn ics inv ctx' method' req' reply' opts' Ψ' -∗
        WP (invokerCall inv' ctx' method' req' reply' #conn opts') {{ Ψ' }}) -∗
      WP (interceptorCall ic ctx method req reply #conn inv' opts) {{ Ψ }})

/-- An invoker that behaves as one meeting the attempt contract meets it. -/
theorem grpcInvokerOk_of_wp (conn : Loc) (addr : List GoString) (inv inv' : GoFunc) :
    grpcInvokerOk (GF := GF) conn addr inv ∗
      (□ ∀ (ctx' method' req' reply' opts' : val) (Ψ' : val → IProp GF),
        WP (invokerCall inv ctx' method' req' reply' #conn opts') {{ Ψ' }} -∗
        WP (invokerCall inv' ctx' method' req' reply' #conn opts') {{ Ψ' }}) ⊢
    grpcInvokerOk conn addr inv' := by
  iintro ⟨#Hinv, #Hw⟩
  unfold grpcInvokerOk
  iintro !> %method %Req %Rep %hreq %hrep %Spec %m %Φ %Ψe %ctx %cd %inp %out %opts %vs %ps
  iintro %Ψ !> Hpre HΨ
  iapply Hw
  iapply Hinv $$ %method %Req %Rep %hreq %hrep %Spec %m %Φ %Ψe %ctx %cd %inp %out %opts %vs %ps %Ψ
    Hpre HΨ

end client

end reg

end EtcdGrove
end Perennial
