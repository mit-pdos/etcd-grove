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
decoded copy, read-only) or fails. -/
def grpcDecOk (dec : GoFunc) (Req : ProtoMsg GF) (m : Req.M) : IProp GF :=
  iprop(∀ l : Loc, {{ Req.blank l }}
      (App (Val #dec) (Val #(interface.mkOk (go.GoType.PointerType Req.ty) #l : GoInterface)))
    {{ (err : GoInterface), RET #err;
        (⌜err = GoInterface.nil⌝ ∗ Req.recv l m) ∨ ⌜err ≠ GoInterface.nil⌝ }})

instance grpcDecOk_persistent (dec : GoFunc) (Req : ProtoMsg GF) (m : Req.M) :
    Persistent (grpcDecOk dec Req m) := by
  unfold grpcDecOk; infer_instance

/-- grpc's `dec`, at the Go type `T` of the request (`Req.ty = T`). -/
theorem grpcDecOk_ty (dec : GoFunc) (Req : ProtoMsg GF) (m : Req.M) (T : go.GoType)
    (hT : Req.ty = T) :
    grpcDecOk (GF := GF) dec Req m ⊢ iprop(∀ l : Loc, {{ Req.blank l }}
      (App (Val #dec) (Val #(interface.mkOk (go.GoType.PointerType T) #l : GoInterface)))
    {{ (err : GoInterface), RET #err;
        (⌜err = GoInterface.nil⌝ ∗ Req.recv l m) ∨ ⌜err ≠ GoInterface.nil⌝ }}) := by
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
  spec : GrpcSpec Req Rep
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
axiom grpcServerAt {GF : BundledGFunctors} [FfiSyntax] (addr : GoString) (ics : List GoFunc)
  (regs : List (GoString × val × GoInterface)) : IProp GF

/-- **The server at `addr` runs the method handler `mh` with the service `srv` and the chain
`ics` for the method `name`, with the per-run resource `S`** (persistent; an axiomatized
predicate, introduced only by `grpc.serve`). -/
axiom grpcServes {GF : BundledGFunctors} [FfiSyntax] (addr name : GoString) (mh : val)
  (srv : GoInterface) (ics : List GoFunc) (S : IProp GF) : IProp GF

axiom grpcServes_persistent {GF : BundledGFunctors} [FfiSyntax] (addr name : GoString) (mh : val)
  (srv : GoInterface) (ics : List GoFunc) (S : IProp GF) :
  Persistent (grpcServes addr name mh srv ics S)

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
header): grpc's runtime at `addr` runs, for `name`, a method handler with a service and the
server's chain that meet it (`grpcMethodOk`), with the resource it was served with. -/
def isGrpcRpc {Req Rep : ProtoMsg GF} (addr name : GoString) (Spec : GrpcSpec Req Rep) :
    IProp GF :=
  iprop(∃ (mh : val) (srv : GoInterface) (ics : List GoFunc) (S : IProp GF),
    grpcServes addr name mh srv ics S ∗ grpcMethodOk mh srv ics S Spec)

instance isGrpcRpc_persistent {Req Rep : ProtoMsg GF} (addr name : GoString)
    (Spec : GrpcSpec Req Rep) : Persistent (isGrpcRpc addr name Spec) := by
  unfold isGrpcRpc; infer_instance

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
    [∗list] m ∈ ms, grpcMethodOk m.handler m.srv ics S m.spec) ⊢
  |={⊤}=> [∗list] m ∈ ms, grpcServes addr m.name m.handler m.srv ics S

/-- **The methods of a served server are registered** (`grpc.serve`, `isGrpcRpc_intro`). -/
theorem grpc_serve_rpcs (addr : GoString) (ics : List GoFunc)
    (regs : List (GoString × val × GoInterface)) (ms : List (GrpcMethod GF)) (S : IProp GF)
    (n : Nat) (hnd : (ms.map GrpcMethod.name).Nodup)
    (hreg : ∀ m ∈ ms, (m.name, m.handler, m.srv) ∈ regs) :
    (grpcServerAt addr ics regs ∗ ([∗list] _x ∈ List.replicate n (), S) ∗
      □ [∗list] m ∈ ms, grpcMethodOk m.handler m.srv ics S m.spec) ⊢
    |={⊤}=> [∗list] m ∈ ms, isGrpcRpc addr m.name m.spec := by
  iintro ⟨Hl, Hs, #Hh⟩
  imod (grpc.serve addr ics regs ms S n hnd hreg) $$ [Hl Hs] with Hsv
  · iframe
    iexact Hh
  imodintro
  have Hm := BigSepL.bigSepL_mono_of_forall (PROP := IProp GF) (l := ms)
    (Φ := fun _ m => iprop(grpcServes addr m.name m.handler m.srv ics S ∗
      grpcMethodOk m.handler m.srv ics S m.spec))
    (Ψ := fun _ m => isGrpcRpc addr m.name m.spec)
    (fun {_ m} => isGrpcRpc_intro (GF := GF) addr m.name m.handler m.srv ics S m.spec)
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
