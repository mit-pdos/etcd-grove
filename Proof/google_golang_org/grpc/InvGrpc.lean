/-
**A generic gRPC specification** (2026-10-14; replaces unit C1's `Put`/`Range`-specific
transport contract): the vocabulary of grpc's trust boundary, for any service, method and message
type, in the predicate-transformer style of Grove's urpc (`is_urpc_spec_pred`,
`is_urpc_handler_pred`, `wp_Client__Call_pred`). Lean-first (no Rocq counterpart); the design:
`notes/decisions.md`, "A generic gRPC specification".

**Messages** (`ProtoMsg`): a protobuf message type `T` (passed as `*T`) with the model `M` of its
wire content; `send l m`: the sender's `*T` holding `m`, what the codec needs to marshal it (it
comes back); `recv l m` (persistent): a decoded `*T` holding `m`, read-only; `blank l`: a zero `*T`
the receiver owns, into which a reply is decoded. That the codec's copy of a message `send` holds
at `m` is one `recv` holds at `m` is what an instance asserts: each instance is a trusted wire
model of its Go type (read it against the type's fields).

**A method's spec** (`Spec : Req.M → (Rep.M → IProp) → IProp`): a predicate transformer over the
request's and reply's models (urpc's saved spec): `Spec m Φ` is what a caller asking `m` must give
for the handler to answer some `m'` with `Φ m'`.

**The server side.** A handler `h` (a unary method of the registered service: `h ctx req`
returns `(resp, err)`) meets `Spec` with the per-run resource `S` (`grpcHandlerOk h S Spec`,
persistent): given `S`, the run's context, a decoded request at `m` and `Spec m Φ`, it returns `S`
and, on success, a response at some `m'` with `Φ m'`. A server gets its methods served at its
address by `grpc.serve` (an axiom: `Proof/google_golang_org/grpc/Server__serve.lean`), handing the
runtime its listener (`grpcListener addr`, exclusive: one registration per address) and `n`
copies of `S` (a run holds one: at most `n` runs at a time); it obtains `grpcServes addr name h S`
(persistent, opaque) for each method.

**Registration** (`isGrpcRpc addr name Spec`, persistent, a definition): some handler served at
`addr` under `name` meets `Spec` (with the resource it was served with). Several specs of one
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

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A protobuf message type** (see the file header). -/
structure ProtoMsg (GF : BundledGFunctors) where
  /-- The message's Go type `T` (the message is passed as `*T`). -/
  ty : go.GoType
  /-- The model of the message's wire content. -/
  M : Type
  /-- The sender's `*T` holding `m` (what marshaling needs; it comes back). -/
  send : Loc → M → IProp GF
  /-- A decoded `*T` holding `m` (read-only). -/
  recv : Loc → M → IProp GF
  recv_persistent : ∀ l m, Persistent (recv l m)
  /-- A zero `*T` the receiver owns. -/
  blank : Loc → IProp GF
  /-- A `*T` the receiver owns, at any content (unit P3a: what a failed attempt leaves of the
  reply, into which the next attempt decodes; grpc's codec resets the message first). -/
  own : Loc → IProp GF
  blank_own : ∀ l, blank l ⊢ own l

attribute [instance] ProtoMsg.recv_persistent

/-- **A gRPC method's spec** over the request's and reply's models (a predicate transformer). -/
abbrev GrpcSpec (Req Rep : ProtoMsg GF) : Type := Req.M → (Rep.M → IProp GF) → IProp GF

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

/-- **The handler `h` meets `Spec` with the per-run resource `S`** (persistent; see the file
header): a run, given `S`, the context the runtime made for it (`isContext`, `grpcRunCtx`), the
decoded request `r` at `m` and `Spec m Φ`, returns `S` and, on success, a response at some `m'`
with `Φ m'`. -/
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

/-- **A method a server registers**: its full name (`"/etcdserverpb.KV/Put"`), its message
types, its spec, its handler. -/
structure GrpcMethod (GF : BundledGFunctors) where
  name : GoString
  Req : ProtoMsg GF
  Rep : ProtoMsg GF
  spec : GrpcSpec Req Rep
  handler : val

end defs

/-! ## The opaque facts about grpc's runtime -/

/-- **The right to serve at `addr`** (exclusive; an axiomatized predicate): a gRPC server's
listener at the address `addr` (urpc's `host c↦ ∅`). -/
axiom grpcListener {GF : BundledGFunctors} (addr : GoString) : IProp GF

/-- **The server at `addr` runs `h` for the method `name`, with the per-run resource `S`**
(persistent; an axiomatized predicate, introduced only by `grpc.serve`). -/
axiom grpcServes {GF : BundledGFunctors} [FfiSyntax] (addr name : GoString) (h : val)
  (S : IProp GF) : IProp GF

axiom grpcServes_persistent {GF : BundledGFunctors} [FfiSyntax] (addr name : GoString) (h : val)
  (S : IProp GF) : Persistent (grpcServes addr name h S)

attribute [instance] grpcServes_persistent

/-- **The client's connection `conn` reaches the server at `addr`, with the unary interceptors
`ics` and the default call options `dopts`** (persistent; an axiomatized predicate: a fact about
grpc's `*ClientConn` dialed to `addr`; unit P3a, it was `isGrpcConn conn addr`, the interceptors
inside the boundary). `ics` is the chain `grpc.NewClient`/`Dial` compose
(`chainUnaryClientInterceptors`: `WithUnaryInterceptor`'s, then `WithChainUnaryInterceptor`'s, in
order), `dopts` the `WithDefaultCallOptions`. -/
axiom grpcConn {GF : BundledGFunctors} [FfiSyntax] (conn : Loc) (addr : GoString)
  (ics : List GoFunc) (dopts : List GoInterface) : IProp GF

axiom grpcConn_persistent {GF : BundledGFunctors} [FfiSyntax] (conn : Loc) (addr : GoString)
    (ics : List GoFunc) (dopts : List GoInterface) :
  Persistent (grpcConn (GF := GF) conn addr ics dopts)

attribute [instance] grpcConn_persistent

/-- **`v` is grpc's call option `grpc.Peer(p)`** (an axiomatized property, introduced only by
`grpc.Peer`'s spec, `Spec/google_golang_org/grpc/Peer.lean`): after the call, the attempt's peer
is written to `*p`. -/
axiom grpcPeerOpt [FfiSyntax] (v : GoInterface) (p : Loc) : Prop

/-- **`pv` is a peer grpc's transport writes** for a call (an axiomatized property: its addresses
are `net`'s, its auth info grpc's credentials', so its `String()` returns). -/
axiom grpcWrotePeer [FfiSyntax] (pv : google_golang_org.grpc.peer.Peer) : Prop

section reg
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The method `name` of the server at `addr` meets `Spec`** (persistent; see the file
header): a handler served there under `name` meets it, with the resource it was served with. -/
def isGrpcRpc {Req Rep : ProtoMsg GF} (addr name : GoString) (Spec : GrpcSpec Req Rep) :
    IProp GF :=
  iprop(∃ (h : val) (S : IProp GF), grpcServes addr name h S ∗ grpcHandlerOk h S Spec)

instance isGrpcRpc_persistent {Req Rep : ProtoMsg GF} (addr name : GoString)
    (Spec : GrpcSpec Req Rep) : Persistent (isGrpcRpc addr name Spec) := by
  unfold isGrpcRpc; infer_instance

/-- A served handler that meets `Spec` registers it. -/
theorem isGrpcRpc_intro {Req Rep : ProtoMsg GF} (addr name : GoString) (h : val) (S : IProp GF)
    (Spec : GrpcSpec Req Rep) :
    grpcServes addr name h S ∗ grpcHandlerOk h S Spec ⊢ isGrpcRpc addr name Spec := by
  iintro ⟨#H1, #H2⟩
  unfold isGrpcRpc
  iexists h, S
  iframe #

/-- **Serving** (an axiom, the server side of the trust boundary; see the file header and
`notes/decisions.md`, "A generic gRPC specification"): a server with the listener at `addr` that
registers the methods `ms` (distinct names), each handler meeting its spec with the per-run
resource `S`, and hands the runtime `n` copies of `S`, is served at `addr`: grpc's runtime runs,
for a call of `m.name`, `m.handler` on the call's context (`isContext`, and `grpcRunCtx`: no value
under etcd's keys; unit P3a) and a decoded copy of the request, a run holding one copy of `S`
(taken from the `n` and given back: at most `n` runs at a time). -/
axiom grpc.serve (addr : GoString) (ms : List (GrpcMethod GF)) (S : IProp GF) (n : Nat) :
  (ms.map GrpcMethod.name).Nodup →
  (grpcListener addr ∗ ([∗list] _x ∈ List.replicate n (), S) ∗
    [∗list] m ∈ ms, grpcHandlerOk m.handler S m.spec) ⊢
  |={⊤}=> [∗list] m ∈ ms, grpcServes addr m.name m.handler S

/-- **The methods of a served server are registered** (`grpc.serve`, `isGrpcRpc_intro`). -/
theorem grpc_serve_rpcs (addr : GoString) (ms : List (GrpcMethod GF)) (S : IProp GF) (n : Nat)
    (hnd : (ms.map GrpcMethod.name).Nodup) :
    (grpcListener addr ∗ ([∗list] _x ∈ List.replicate n (), S) ∗
      □ [∗list] m ∈ ms, grpcHandlerOk m.handler S m.spec) ⊢
    |={⊤}=> [∗list] m ∈ ms, isGrpcRpc addr m.name m.spec := by
  iintro ⟨Hl, Hs, #Hh⟩
  imod (grpc.serve addr ms S n hnd) $$ [Hl Hs] with Hsv
  · iframe
    iexact Hh
  imodintro
  have Hm := BigSepL.bigSepL_mono_of_forall (PROP := IProp GF) (l := ms)
    (Φ := fun _ m => iprop(grpcServes addr m.name m.handler S ∗ grpcHandlerOk m.handler S m.spec))
    (Ψ := fun _ m => isGrpcRpc addr m.name m.spec)
    (fun {_ m} => isGrpcRpc_intro (GF := GF) addr m.name m.handler S m.spec)
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

/-- **One attempt** (persistent; the contract of grpc's `invoke`, the final invoker of a
connection's interceptor chain; unit P3a): a call of a method registered at `addr` with `Spec`,
for the request `inp` (`Req.send`, given back), into the reply `out` (owned, at any content:
`Rep.own`), with call options grpc can apply (`grpcOptOk ps`: scalar, or peer options writing the
buffers `ps`, owned and given back) and the caller's `□ ▷ Spec m Φ` (persistent: grpc's own transparent retries may deliver
the request again), returns
* `nil`: a run of the handler served for the method on a copy of the request answered, and `out`
  holds the reply's copy of its response (`Rep.recv out m'`) with the run's `Φ m'`;
* an error: a client error (`clientErr`: a leaf error, not an `EtcdError`; a gRPC status error)
  that grpc's `status` accepts (`statusErrOk`), and `out` back (`Rep.own`); nothing about whether
  the handler ran. -/
def grpcInvokerOk (conn : Loc) (addr : GoString) (inv : GoFunc) : IProp GF :=
  iprop(□ ∀ (method : GoString) (Req Rep : ProtoMsg GF) (Spec : GrpcSpec Req Rep) (m : Req.M)
      (Φ : Rep.M → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
      (inp out : Loc) (opts : GoSlice) (vs : List GoInterface) (ps : List Loc),
    {{ isGrpcRpc addr method Spec ∗ □ ▷ Spec m Φ ∗ context.isContext ctx cd ∗ Req.send inp m ∗
        Rep.own out ∗ opts ↦*□ vs ∗ ⌜∀ v ∈ vs, grpcOptOk ps v⌝ ∗ ([∗list] p ∈ ps, grpcPeerBuf p) }}
      (invokerCall inv #(GoInterface.ok ctx) #method
        #(interface.mkOk (go.GoType.PointerType Req.ty) #inp : GoInterface)
        #(interface.mkOk (go.GoType.PointerType Rep.ty) #out : GoInterface) #conn #opts)
    {{ (err : GoInterface), RET #err; Req.send inp m ∗ ([∗list] p ∈ ps, grpcPeerBuf p) ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ m' : Rep.M, Rep.recv out m' ∗ Φ m') ∨
          (⌜err ≠ GoInterface.nil ∧ clientErr err⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk err ∗
            Rep.own out)) }})

instance grpcInvokerOk_persistent (conn : Loc) (addr : GoString) (inv : GoFunc) :
    Persistent (grpcInvokerOk (GF := GF) conn addr inv) := by
  unfold grpcInvokerOk; infer_instance

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
theorem grpcInvokerOk_of_wp (conn : Loc) (addr : GoString) (inv inv' : GoFunc) :
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
