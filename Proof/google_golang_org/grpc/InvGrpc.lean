/-
**A generic gRPC specification** (2026-10-14; replaces unit C1's `Put`/`Range`-specific
transport contract): the vocabulary of grpc's trust boundary, for any service, method and message
type, in the predicate-transformer style of Grove's urpc (`is_urpc_spec_pred`,
`is_urpc_handler_pred`, `wp_Client__Call_pred`). Lean-first (no Rocq counterpart); the design:
`notes/decisions.md`, "A generic gRPC specification".

**Messages** (`ProtoMsg`): a protobuf message type `T` (passed as `*T`) with the model `M` of its
wire content; `send l m`: the sender's `*T` holding `m`, what the codec needs to marshal it (it
comes back); `recv l m` (persistent): a decoded `*T` holding `m`, read-only, and `recvOwn l m` what else of it
the receiver owns (nothing but for a request its handler writes); `blank l`: a zero `*T`
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
such a run must meet. A server gets its methods served at its address by `grpc.serve` (an axiom),
handing the runtime its server object (`grpcServerAt addr ics regs`, exclusive: built with the
chain `ics`, the methods `regs` registered) and `n` copies of `S` (a run holds one: at most `n`
runs at a time); it obtains `grpcServes addr name mh srv ics S` (persistent, opaque) for each.
Interceptors are specified as transparent (`srvInterceptorOk`, `srvChainWP_of_ok`).

**Registration** (`isGrpcRpc addr name Spec`, persistent, a definition): some method handler
served at `addr` under `name` meets `Spec` as grpc runs it (`grpcMethodOk`). Several specs of one
method may hold (each a fact about the one handler); a client needs one.

**The client side** (unit P3a, 2026-10-14: the boundary below the interceptors).
`grpcConn conn addr ics dopts` (persistent, opaque): the client's `*ClientConn` `conn` reaches the
server at `addr`, with the unary interceptor chain `ics` and the default call options `dopts`.
`ClientConn.Invoke` (the one client-side axiom, `Spec/google_golang_org/grpc/
ClientConn__Invoke.lean`) of any method is the chain (`chainWP`, as grpc composes it) over grpc's
`invoke`, which makes one attempt (`grpcInvokerOk`: a run of the handler served for a registered
method, or an error); an attempt's call options are scalar or `grpc.Peer(p)` options
(`grpcOptOk`, `grpcPeerOpt`), whose buffers `*p` (`grpcPeerBuf`) the attempt writes.
-/
module

public import Perennial.Proof.context
public import Proof.go_etcd_io.etcd.client.v3.ClientErr
public import GeneratedProof.google_golang_org.grpc.peer
public import Proof.google_golang_org.grpc.metadata.Outgoing
public import Code.google_golang_org.grpc.credentials

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
  messages `send` holds field by field (inside `txnReqAt`, `createReqSend`, `userOptsAt`,
  `ownPermW`) are not pinned; translated code never sets unknown fields (`SetUnknown` is not
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
  hash). Nothing by default. -/
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

/-- **A method's spec at the call's metadata** (the auth plan's E3zb): `Spec md m Φ` is what a
caller asking `m` with an attempt whose handler sees the metadata `md` must give. A plain spec
(`GrpcSpec`) is one for every metadata (`GrpcSpec.md`). -/
abbrev GrpcSpecMd (Req Rep : ProtoMsg GF) : Type := GrpcMd → GrpcSpec Req Rep

/-- A plain spec, at every metadata. -/
abbrev GrpcSpec.md {Req Rep : ProtoMsg GF} (Spec : GrpcSpec Req Rep) : GrpcSpecMd Req Rep :=
  fun _ => Spec

/-- **The prefix of etcd's Go package paths** (`go.etcd.io/etcd/`). -/
def etcdPkgPrefix : GoString := go!"go.etcd.io/etcd/"

/-- **The context a server's runtime makes for a run** (persistent; part of the trusted server
runtime, unit P3a with unit P1b's traces): its `Value(k)` of a key whose type is a named type of
etcd's own packages (`go.etcd.io/etcd/...`, e.g. `traceutil.TraceKey`) returns `nil`: grpc's
server context carries grpc's values (metadata, peer, stream) and those of the stats handlers
and interceptors in front of the handler (etcd's `v3rpc` interceptors, otelgrpc's), none under
such a key. What the server's handlers rely on: a request's context carries no trace
(`traceutil.ctxTraceIs ci none`, `v3rpc.srvCall`). -/
def grpcRunCtx (ci : GoInterfaceOk) : IProp GF :=
  iprop(□ ∀ (n : GoString) (x : val) (Φ : val → IProp GF), ⌜etcdPkgPrefix <+: n⌝ →
    ▷ Φ #GoInterface.nil -∗
    WP (App (Val #(methods ci.ty go!"Value" ci.v))
      (Val #(interface.mkOk (go.GoType.Named n []) x : GoInterface))) {{ Φ }})

instance grpcRunCtx_persistent (ci : GoInterfaceOk) : Persistent (grpcRunCtx (GF := GF) ci) := by
  unfold grpcRunCtx; infer_instance

/-- **A service method `h` meets `Spec` with the per-run resource `S`** (persistent; see the file
header; unit P3b: the registered service's method, which the generated handler calls below the
interceptors, `grpcMethodOk`; until P3b it was what grpc ran): a call, given `S`, the context the
runtime made for the run (`isContext`, `grpcRunCtx`), the decoded request `r` at `m` and
`Spec m Φ`, returns `S` and, on success, a response at some `m'` with `Φ m'`. -/
def grpcHandlerOk {Req Rep : ProtoMsg GF} (h : val) (S : IProp GF) (Spec : GrpcSpec Req Rep) :
    IProp GF :=
  iprop(∀ (m : Req.M) (Φ : Rep.M → IProp GF) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (r : Loc),
    {{ S ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ Req.recv r m ∗ Spec m Φ }}
      (App (App (Val h) (Val #(GoInterface.ok ci))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        S ∗ (⌜err = GoInterface.nil⌝ -∗ ∃ m' : Rep.M, Rep.send resp m' ∗ Φ m') }})

instance grpcHandlerOk_persistent {Req Rep : ProtoMsg GF} (h : val) (S : IProp GF)
    (Spec : GrpcSpec Req Rep) : Persistent (grpcHandlerOk h S Spec) := by
  unfold grpcHandlerOk; infer_instance

/-- **A service method `h` meets the metadata-indexed `Spec` with `S`** (persistent; the auth plan's
E3zb): as `grpcHandlerOk`, the run's request precondition at its context's incoming metadata
(`metadata.incomingOf`). A plain spec's is `grpcHandlerOk` (`grpcHandlerOk_md`). -/
def grpcHandlerOkMd {Req Rep : ProtoMsg GF} (h : val) (S : IProp GF) (Spec : GrpcSpecMd Req Rep) :
    IProp GF :=
  iprop(∀ (m : Req.M) (Φ : Rep.M → IProp GF) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (r : Loc),
    {{ S ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ Req.recv r m ∗
        Spec (metadata.incomingOf (GoInterface.ok ci)) m Φ }}
      (App (App (Val h) (Val #(GoInterface.ok ci))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        S ∗ (⌜err = GoInterface.nil⌝ -∗ ∃ m' : Rep.M, Rep.send resp m' ∗ Φ m') }})

instance grpcHandlerOkMd_persistent {Req Rep : ProtoMsg GF} (h : val) (S : IProp GF)
    (Spec : GrpcSpecMd Req Rep) : Persistent (grpcHandlerOkMd h S Spec) := by
  unfold grpcHandlerOkMd; infer_instance

theorem grpcHandlerOk_md {Req Rep : ProtoMsg GF} (h : val) (S : IProp GF)
    (Spec : GrpcSpec Req Rep) : grpcHandlerOk h S Spec ⊣⊢ grpcHandlerOkMd h S (GrpcSpec.md Spec) :=
  .rfl

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
        S ∗ (⌜err = GoInterface.nil⌝ -∗ ∃ m' : Rep.M, Rep.send resp m' ∗ Φ m') }})

instance grpcHandlerOwnOk_persistent {Req Rep : ProtoMsg GF} (h : val) (S : IProp GF)
    (Spec : GrpcSpec Req Rep) : Persistent (grpcHandlerOwnOk h S Spec) := by
  unfold grpcHandlerOwnOk; infer_instance

/-- **A service method `h` that writes its request meets the metadata-indexed `Spec` with `S`**
(persistent): as `grpcHandlerOwnOk`, at the run's metadata. -/
def grpcHandlerOwnOkMd {Req Rep : ProtoMsg GF} (h : val) (S : IProp GF)
    (Spec : GrpcSpecMd Req Rep) : IProp GF :=
  iprop(∀ (m : Req.M) (Φ : Rep.M → IProp GF) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (r : Loc),
    {{ S ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ Req.recv r m ∗ Req.recvOwn r m ∗
        Spec (metadata.incomingOf (GoInterface.ok ci)) m Φ }}
      (App (App (Val h) (Val #(GoInterface.ok ci))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        S ∗ (⌜err = GoInterface.nil⌝ -∗ ∃ m' : Rep.M, Rep.send resp m' ∗ Φ m') }})

instance grpcHandlerOwnOkMd_persistent {Req Rep : ProtoMsg GF} (h : val) (S : IProp GF)
    (Spec : GrpcSpecMd Req Rep) : Persistent (grpcHandlerOwnOkMd h S Spec) := by
  unfold grpcHandlerOwnOkMd; infer_instance

/-- A method that does not write its request meets the metadata-indexed spec of one that may. -/
theorem grpcHandlerOkMd_own {Req Rep : ProtoMsg GF} (h : val) (S : IProp GF)
    (Spec : GrpcSpecMd Req Rep) :
    grpcHandlerOkMd h S Spec ⊢ grpcHandlerOwnOkMd h S Spec := by
  iintro #Hh
  unfold grpcHandlerOwnOkMd
  iintro %m %Φ %ci %cd %r !> %Ψ ⟨HS, #Hctx, #Hrc, #Hr, -, HSpec⟩ HΨ
  iunfold grpcHandlerOkMd at Hh
  iapply Hh $$ %m %Φ %ci %cd %r [HS HSpec] HΨ
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
  iintro %m %Φ %ci %cd %r !> %Ψ ⟨⟨HS, HR⟩, #Hctx, #Hrc, #Hr, HSpec⟩ HΨ
  iapply Hh $$ %m %Φ %ci %cd %r [HS HSpec]
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
decoded copy, read-only; `Req.recvOwn l m`: what the caller still owns of it) or fails. -/
def grpcDecOk (dec : GoFunc) (Req : ProtoMsg GF) (m : Req.M) : IProp GF :=
  iprop(∀ l : Loc, {{ Req.blank l }}
      (App (Val #dec) (Val #(interface.mkOk (go.GoType.PointerType Req.ty) #l : GoInterface)))
    {{ (err : GoInterface), RET #err;
        (⌜err = GoInterface.nil⌝ ∗ Req.recv l m ∗ Req.recvOwn l m) ∨ ⌜err ≠ GoInterface.nil⌝ }})

instance grpcDecOk_persistent (dec : GoFunc) (Req : ProtoMsg GF) (m : Req.M) :
    Persistent (grpcDecOk dec Req m) := by
  unfold grpcDecOk; infer_instance

/-- grpc's `dec`, at the Go type `T` of the request (`Req.ty = T`). -/
theorem grpcDecOk_ty (dec : GoFunc) (Req : ProtoMsg GF) (m : Req.M) (T : go.GoType)
    (hT : Req.ty = T) :
    grpcDecOk (GF := GF) dec Req m ⊢ iprop(∀ l : Loc, {{ Req.blank l }}
      (App (Val #dec) (Val #(interface.mkOk (go.GoType.PointerType T) #l : GoInterface)))
    {{ (err : GoInterface), RET #err;
        (⌜err = GoInterface.nil⌝ ∗ Req.recv l m ∗ Req.recvOwn l m) ∨ ⌜err ≠ GoInterface.nil⌝ }}) := by
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
          ⌜resp = interface.mkOk (go.GoType.PointerType Rep.ty) #l⌝ ∗ Rep.send l m' ∗ Φ m') }})

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
  iprop(∀ (m : Req.M) (Φ : Rep.M → IProp GF) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (dec ui : GoFunc),
    {{ S ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ grpcDecOk dec Req m ∗ grpcSrvChain ics ui ∗
        Spec (metadata.incomingOf (GoInterface.ok ci)) m Φ }}
      (methodHandlerCall mh #srv #(GoInterface.ok ci) dec ui)
    {{ (resp err : GoInterface), RET (PairV #resp #err); S ∗
        (⌜err = GoInterface.nil⌝ -∗ ∃ (l : Loc) (m' : Rep.M),
          ⌜resp = interface.mkOk (go.GoType.PointerType Rep.ty) #l⌝ ∗ Rep.send l m' ∗ Φ m') }})

instance grpcMethodOkMd_persistent {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface)
    (ics : List GoFunc) (S : IProp GF) (Spec : GrpcSpecMd Req Rep) :
    Persistent (grpcMethodOkMd mh srv ics S Spec) := by
  unfold grpcMethodOkMd; infer_instance

theorem grpcMethodOk_md {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface) (ics : List GoFunc)
    (S : IProp GF) (Spec : GrpcSpec Req Rep) :
    grpcMethodOk mh srv ics S Spec ⊣⊢ grpcMethodOkMd mh srv ics S (GrpcSpec.md Spec) :=
  .rfl

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
        {{ v, ∃ resp err : GoInterface, ⌜v = PairV #resp #err⌝ ∗ (R -∗ Ψ v) }} ∧
      (R -∗ ∀ err : GoInterface, ⌜err ≠ GoInterface.nil⌝ -∗
        Ψ (PairV #GoInterface.nil #err))) -∗
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
          {{ v, ∃ resp err : GoInterface, ⌜v = PairV #resp #err⌝ ∗
            (([∗list] R ∈ Rs, R) -∗ Ψ v) }} ∧
        (([∗list] R ∈ Rs, R) -∗ ∀ err : GoInterface, ⌜err ≠ GoInterface.nil⌝ -∗
          Ψ (PairV #GoInterface.nil #err))) ⊢
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
        (([∗list] R ∈ ([] : List (IProp GF)), R) -∗ Ψ v)))) $$ H
      iintro %v ⟨%resp, %err, -, HΨ⟩
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
          (R -∗ Ψ v))))
        iframe #
        iframe
        isplit
        · icases H with ⟨H, -⟩
          iapply (wp_mono (Φ := fun v => iprop(∃ resp err : GoInterface, ⌜v = PairV #resp #err⌝ ∗
            (([∗list] R ∈ R :: Rs, R) -∗ Ψ v)))) $$ H
          iintro %v ⟨%resp, %err, %Hv, HΨ⟩
          iexists resp, err
          isplitr
          · ipureintro; exact Hv
          iintro HRs'
          iexists resp, err
          isplitr
          · ipureintro; exact Hv
          iintro HR'
          iapply HΨ
          iapply (BigSepL.bigSepL_cons (PROP := IProp GF) (Φ := fun _ R => R) (x := R) (xs := Rs)).2
          iframe
        · icases H with ⟨-, H⟩
          iintro HRs' %err %Herr
          iexists GoInterface.nil, err
          isplitr
          · ipureintro; rfl
          iintro HR'
          iapply H $$ [HR' HRs'] %err %Herr
          iapply (BigSepL.bigSepL_cons (PROP := IProp GF) (Φ := fun _ R => R) (x := R) (xs := Rs)).2
          iframe
      · icases H with ⟨-, H⟩
        iintro HR' %err %Herr
        iapply H $$ [HR' HRs] %err %Herr
        iapply (BigSepL.bigSepL_cons (PROP := IProp GF) (Φ := fun _ R => R) (x := R) (xs := Rs)).2
        iframe

/-- **A method a server registers**: its full name (`"/etcdserverpb.KV/Put"`), its message
types, its spec, the generated handler its `ServiceDesc`'s `MethodDesc` holds
(`etcdserverpb._KV_Put_Handler`), and the service value registered with the `ServiceDesc`
(`RegisterKVServer(s, srv)`'s `srv`, as `any`). -/
structure GrpcMethod (GF : BundledGFunctors) where
  name : GoString
  Req : ProtoMsg GF
  Rep : ProtoMsg GF
  spec : GrpcSpecMd Req Rep
  handler : val
  srv : GoInterface

end defs

/-! ## The opaque facts about grpc's runtime -/

/-- **The gRPC server listening at `addr`, built with the unary interceptor chain `ics`, its
services' methods `regs` registered** (exclusive; an axiomatized predicate, unit P3b; it was
`grpcListener addr`): one registration per address (urpc's `host c↦ ∅`); `ics` the interceptors
`grpc.NewServer`'s options chain (`UnaryInterceptor`'s, then `ChainUnaryInterceptor`'s, in
order), `regs` the `(full method name, MethodDesc.Handler, service value)` of every unary method
of the `ServiceDesc`s registered with `RegisterService`. Established by the server's unverified
construction (etcd's `v3rpc.Server`, `grpc.NewServer`, the `Register*Server` calls, `Serve`): a
premise of the server's results. -/
axiom grpcServerAt {GF : BundledGFunctors} [GooseExts] (addr : GoString) (ics : List GoFunc)
  (regs : List (GoString × val × GoInterface)) : IProp GF

/-- **The server at `addr` runs the method handler `mh` with the service `srv` and the chain
`ics` for the method `name`, with the per-run resource `S`** (persistent; an axiomatized
predicate, introduced only by `grpc.serve`). -/
axiom grpcServes {GF : BundledGFunctors} [GooseExts] (addr name : GoString) (mh : val)
  (srv : GoInterface) (ics : List GoFunc) (S : IProp GF) : IProp GF

axiom grpcServes_persistent {GF : BundledGFunctors} [GooseExts] (addr name : GoString) (mh : val)
  (srv : GoInterface) (ics : List GoFunc) (S : IProp GF) :
  Persistent (grpcServes addr name mh srv ics S)

attribute [instance] grpcServes_persistent

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

/-- **The method `name` of the server at `addr` meets `Spec`** (persistent; see the file
header): grpc's runtime at `addr` runs, for `name`, a method handler with a service and the
server's chain that meet it (`grpcMethodOk`), with the resource it was served with. -/
def isGrpcRpc {Req Rep : ProtoMsg GF} (addr name : GoString) (Spec : GrpcSpec Req Rep) :
    IProp GF :=
  iprop(∃ (mh : val) (srv : GoInterface) (ics : List GoFunc) (S : IProp GF),
    grpcServes addr name mh srv ics S ∗ grpcMethodOk mh srv ics S Spec)

instance isGrpcRpc_persistent {Req Rep : ProtoMsg GF} (addr name : GoString)
    (Spec : GrpcSpec Req Rep) : Persistent (isGrpcRpc addr name Spec) := by
  unfold isGrpcRpc; infer_instance

/-- **The method `name` of the server at `addr` meets the metadata-indexed `Spec`** (persistent;
the auth plan's E3zb): as `isGrpcRpc`, with `grpcMethodOkMd`. A plain spec's is `isGrpcRpc`
(`isGrpcRpc_md`). -/
def isGrpcRpcMd {Req Rep : ProtoMsg GF} (addr name : GoString) (Spec : GrpcSpecMd Req Rep) :
    IProp GF :=
  iprop(∃ (mh : val) (srv : GoInterface) (ics : List GoFunc) (S : IProp GF),
    grpcServes addr name mh srv ics S ∗ grpcMethodOkMd mh srv ics S Spec)

instance isGrpcRpcMd_persistent {Req Rep : ProtoMsg GF} (addr name : GoString)
    (Spec : GrpcSpecMd Req Rep) : Persistent (isGrpcRpcMd addr name Spec) := by
  unfold isGrpcRpcMd; infer_instance

theorem isGrpcRpc_md {Req Rep : ProtoMsg GF} (addr name : GoString) (Spec : GrpcSpec Req Rep) :
    isGrpcRpc addr name Spec ⊣⊢ isGrpcRpcMd addr name (GrpcSpec.md Spec) :=
  .rfl

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
    | nil => exact .rfl
    | cons b bs =>
      unfold isGrpcRpcs isGrpcRpcsMd
      exact ⟨sep_mono .rfl ih.1, sep_mono .rfl ih.2⟩

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

/-- A registration with `Spec` is one with a stronger request precondition `Spec'`. -/
theorem isGrpcRpc_mono {Req Rep : ProtoMsg GF} (addr name : GoString)
    (Spec Spec' : GrpcSpec Req Rep) (h : ∀ m Φ, Spec' m Φ ⊢ Spec m Φ) :
    isGrpcRpc addr name Spec ⊢ isGrpcRpc addr name Spec' := by
  iintro #H
  iunfold isGrpcRpc at H
  icases H with ⟨%mh, %srv, %ics, %S, #Hs, #Hm⟩
  unfold isGrpcRpc
  iexists mh, srv, ics, S
  iframe Hs
  iapply (grpcMethodOk_mono mh srv ics S Spec Spec' h) $$ Hm

/-- A method meeting the metadata-indexed `Spec` meets a stronger `Spec'`. -/
theorem grpcMethodOkMd_mono {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface)
    (ics : List GoFunc) (S : IProp GF) (Spec Spec' : GrpcSpecMd Req Rep)
    (h : ∀ md m Φ, Spec' md m Φ ⊢ Spec md m Φ) :
    grpcMethodOkMd mh srv ics S Spec ⊢ grpcMethodOkMd mh srv ics S Spec' := by
  iintro #Hm
  unfold grpcMethodOkMd
  iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨HS, Hctx, Hrc, Hd, Hch, HSpec⟩ HΨ
  iapply Hm $$ %m %Φ %ci %cd %dec %ui [HS Hctx Hrc Hd Hch HSpec] HΨ
  iframe
  iapply (h _ m Φ) $$ HSpec

/-- A registration with the metadata-indexed `Spec` is one with a stronger `Spec'`. -/
theorem isGrpcRpcMd_mono {Req Rep : ProtoMsg GF} (addr name : GoString)
    (Spec Spec' : GrpcSpecMd Req Rep) (h : ∀ md m Φ, Spec' md m Φ ⊢ Spec md m Φ) :
    isGrpcRpcMd addr name Spec ⊢ isGrpcRpcMd addr name Spec' := by
  iintro #H
  iunfold isGrpcRpcMd at H
  icases H with ⟨%mh, %srv, %ics, %S, #Hs, #Hm⟩
  unfold isGrpcRpcMd
  iexists mh, srv, ics, S
  iframe Hs
  iapply (grpcMethodOkMd_mono mh srv ics S Spec Spec' h) $$ Hm

/-- A served method handler that meets the metadata-indexed `Spec` registers it. -/
theorem isGrpcRpcMd_intro {Req Rep : ProtoMsg GF} (addr name : GoString) (mh : val)
    (srv : GoInterface) (ics : List GoFunc) (S : IProp GF) (Spec : GrpcSpecMd Req Rep) :
    grpcServes addr name mh srv ics S ∗ grpcMethodOkMd mh srv ics S Spec ⊢
      isGrpcRpcMd addr name Spec := by
  iintro ⟨#H1, #H2⟩
  unfold isGrpcRpcMd
  iexists mh, srv, ics, S
  iframe #

/-- A served method handler that meets `Spec` registers it. -/
theorem isGrpcRpc_intro {Req Rep : ProtoMsg GF} (addr name : GoString) (mh : val)
    (srv : GoInterface) (ics : List GoFunc) (S : IProp GF) (Spec : GrpcSpec Req Rep) :
    grpcServes addr name mh srv ics S ∗ grpcMethodOk mh srv ics S Spec ⊢
      isGrpcRpc addr name Spec := by
  iintro ⟨#H1, #H2⟩
  unfold isGrpcRpc
  iexists mh, srv, ics, S
  iframe #

/-- **Serving** (an axiom, the server side of the trust boundary; see the file header and
`notes/decisions.md`, "The server end of the gRPC boundary"; unit P3b): a gRPC server at `addr`,
built with the chain `ics`, with the methods `regs` registered (`grpcServerAt`), of which the
methods `ms` (distinct names), each meeting its spec with the per-run resource `S` as grpc runs
it (`grpcMethodOk`: its `MethodDesc.Handler` on the registered service value, the call's context
(`isContext`, and `grpcRunCtx`: no value under etcd's keys), grpc's `dec` for the request, the
interceptor for `ics`), and that hands the runtime `n` copies of `S`, is served at `addr`: a run
holds one copy of `S` (taken from the `n` and given back: at most `n` runs at a time). -/
axiom grpc.serve (addr : GoString) (ics : List GoFunc) (regs : List (GoString × val × GoInterface))
    (ms : List (GrpcMethod GF)) (S : IProp GF) (n : Nat) :
  (ms.map GrpcMethod.name).Nodup → (∀ m ∈ ms, (m.name, m.handler, m.srv) ∈ regs) →
  (grpcServerAt addr ics regs ∗ ([∗list] _x ∈ List.replicate n (), S) ∗
    [∗list] m ∈ ms, grpcMethodOkMd m.handler m.srv ics S m.spec) ⊢
  |={⊤}=> [∗list] m ∈ ms, grpcServes addr m.name m.handler m.srv ics S

/-- **The methods of a served server are registered** (`grpc.serve`, `isGrpcRpc_intro`). -/
theorem grpc_serve_rpcs (addr : GoString) (ics : List GoFunc)
    (regs : List (GoString × val × GoInterface)) (ms : List (GrpcMethod GF)) (S : IProp GF)
    (n : Nat) (hnd : (ms.map GrpcMethod.name).Nodup)
    (hreg : ∀ m ∈ ms, (m.name, m.handler, m.srv) ∈ regs) :
    (grpcServerAt addr ics regs ∗ ([∗list] _x ∈ List.replicate n (), S) ∗
      □ [∗list] m ∈ ms, grpcMethodOkMd m.handler m.srv ics S m.spec) ⊢
    |={⊤}=> [∗list] m ∈ ms, isGrpcRpcMd addr m.name m.spec := by
  iintro ⟨Hl, Hs, #Hh⟩
  imod (grpc.serve addr ics regs ms S n hnd hreg) $$ [Hl Hs] with Hsv
  · iframe
    iexact Hh
  imodintro
  have Hm := BigSepL.bigSepL_mono_of_forall (PROP := IProp GF) (l := ms)
    (Φ := fun _ m => iprop(grpcServes addr m.name m.handler m.srv ics S ∗
      grpcMethodOkMd m.handler m.srv ics S m.spec))
    (Ψ := fun _ m => isGrpcRpcMd addr m.name m.spec)
    (fun {_ m} => isGrpcRpcMd_intro (GF := GF) addr m.name m.handler m.srv ics S m.spec)
  iapply Hm
  iapply BigSepL.bigSepL_sep_eqv.2
  isplitl [Hsv]
  · iexact Hsv
  · iexact Hh

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

/-- **A context that is never done and whose `Err()` returns `nil`** (persistent; the vertical
slice's unit V2): `context.TODO()` and `context.Background()` (an `emptyCtx`: `Done()` is `nil`,
`Err()` is `nil`), and value contexts over them (`valueCtx` delegates `Done` and `Err` to its
parent: `withVersion`'s metadata context). Not an `isContext` (whose `Done()` is a channel). -/
def ctxQuiet (ci : GoInterfaceOk) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ Φ #(GoInterface.nil) -∗
    WP (App (Val #(methods ci.ty go!"Err" ci.v)) (Val #())) {{ Φ }})

instance ctxQuiet_persistent (ci : GoInterfaceOk) : Persistent (ctxQuiet (GF := GF) ci) := by
  unfold ctxQuiet; infer_instance

/-- **A context a client call takes** (persistent; the vertical slice's unit V2): one with the
context model (`isContext`), or a quiet one (`ctxQuiet`: `context.TODO()`, which the recipes pass
to every call). grpc's `invoke` and etcd's client interceptor accept either: the trust boundary's
contracts below (`grpcInvokerOk`; the client's `withVersion`, `waitRetryBackoff`) are stated for
`ctxOk`, true of Go's quiet contexts as of the others (a `nil` `Done()` channel never fires); the
client's token fetch (`getToken`, `refreshToken`) also takes `ctxErrClient` (its `ContextError`). -/
def ctxOk (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) : IProp GF :=
  iprop(context.isContext ci cd ∨ ctxQuiet ci)

instance ctxOk_persistent (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    Persistent (ctxOk (GF := GF) ci cd) := by
  unfold ctxOk; infer_instance

theorem ctxOk_of_isContext (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    context.isContext (GF := GF) ci cd ⊢ ctxOk ci cd := by
  iintro #H; unfold ctxOk; ileft; iexact H

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
  the handler ran.

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
Go's `maxAlloc`. -/
def grpcInvokerOk (conn : Loc) (addrs : List GoString) (inv : GoFunc) : IProp GF :=
  iprop(□ ∀ (method : GoString) (Req Rep : ProtoMsg GF) (Spec : GrpcSpecMd Req Rep) (m : Req.M)
      (Φ : Rep.M → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
      (inp out : Loc) (opts : GoSlice) (vs : List GoInterface) (ps : List Loc),
    {{ isGrpcRpcsMd addrs method Spec ∗
        ▷ (∀ md, ⌜grpcAttemptMd conn (GoInterface.ok ctx) md⌝ -∗ Spec md m Φ) ∗
        ctxOk ctx cd ∗ Req.send inp m ∗ ⌜Req.wireLen m < grpcMsgMax⌝ ∗
        Rep.own out ∗ opts ↦*□ vs ∗ ⌜∀ v ∈ vs, grpcOptOk ps v⌝ ∗ ([∗list] p ∈ ps, grpcPeerBuf p) }}
      (invokerCall inv #(GoInterface.ok ctx) #method
        #(interface.mkOk (go.GoType.PointerType Req.ty) #inp : GoInterface)
        #(interface.mkOk (go.GoType.PointerType Rep.ty) #out : GoInterface) #conn #opts)
    {{ (err : GoInterface), RET #err; Req.send inp m ∗ ([∗list] p ∈ ps, grpcPeerBuf p) ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ m' : Rep.M, Rep.recv out m' ∗ Φ m') ∨
          (⌜err ≠ GoInterface.nil ∧ clientErr err⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk err ∗
            go_etcd_io.etcd.cache.v3.errCellOk err ∗ Rep.own out ∗
            ⌜(kvMethod method ∧ ∀ a ∈ addrs, noRefusalAt a) →
              go_etcd_io.etcd.cache.v3.noRefusal err⌝)) }})

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
2026-10-28): each call of `pc.GetRequestMetadata(ctx, uri...)` that returns no error returns a map
whose metadata `cm` has `□ Q cm` (what grpc sends with an attempt, `connCredsOk`); and
`pc.RequireTransportSecurity()` can be called (grpc calls it at the dial to refuse credentials that
need a secure transport on an insecure one; C1's review, F4). -/
def perRPCCredsOk (pc : GoInterface) (Q : GrpcMd → IProp GF) : IProp GF :=
  iprop((□ ∀ (ctx : GoInterface) (sl : GoSlice),
    {{ True }}
      (App (App (App (Val (GoInstruction (MethodResolve
          google_golang_org.grpc.credentials.PerRPCCredentials.ty go!"GetRequestMetadata")))
        (Val #pc)) (Val #ctx)) (Val #sl))
    {{ (mp : Loc) (err : GoInterface), RET (PairV #mp #err);
        ⌜err = GoInterface.nil⌝ -∗ ∃ cm, credsMapIs mp cm ∗ □ Q cm }}) ∗
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
  iintro !> %method %Req %Rep %Spec %m %Φ %ctx %cd %inp %out %opts %vs %ps
  iintro %Ψ !> Hpre HΨ
  iapply Hw
  iapply Hinv $$ Hpre HΨ

end client

end reg

end EtcdGrove
end Perennial
