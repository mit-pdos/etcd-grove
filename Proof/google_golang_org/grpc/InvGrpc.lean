/-
**gRPC's registrations and its client attempt** (split from `InvGrpcBase.lean`, so that the
registration can name `InvGrpcWire.lean`'s service table; the file header of `InvGrpcBase.lean`
describes both). A registration `isGrpcRpcMd addr name Spec` is heap-free: `addr`'s service table,
fixed when its protocols were set, has an entry for `name` that a caller of `Spec` meets
(`grpcSvcAt`). A bridge's address serves its target's table (`bridge.New`), so a registration is read
off the dialed address's own table, as at any address. The single-process start sets the address's table to Go's
configuration (`grpcGoSvc`, `InvGrpcRun.lean`), so `grpc.serve` stays a theorem.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcWire

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Net

section reg
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The method `name` at `addr` meets `Spec`** (persistent): `addr`'s service table, fixed when
its protocols were set, has an entry for `name` at the messages' wire parts that a caller of `Spec`
meets after an update (`grpcSvcAt`, no heap). -/
def isGrpcRpcMd {Req Rep : ProtoMsg GF} (addr name : GoString) (Spec : GrpcSpecMd Req Rep) :
    IProp GF :=
  iprop(∃ (_ : HasExt netExt) (π : NetProtoGS) (σ : NetSlotGS),
    grpcSvcAt (Gg := hG.goose_globalGS) (π := π) (σ := σ) addr name Req.wire Rep.wire Spec)

instance isGrpcRpcMd_persistent {Req Rep : ProtoMsg GF} (addr name : GoString)
    (Spec : GrpcSpecMd Req Rep) : Persistent (isGrpcRpcMd addr name Spec) := by
  unfold isGrpcRpcMd; infer_instance

/-- An entry of the table `a` serves registers its method. -/
theorem isGrpcRpcMd_of_addr {Req Rep : ProtoMsg GF} (a name : GoString) (Svc : GrpcSvc GF)
    [hX : HasExt netExt] [π : NetProtoGS] [σ : NetSlotGS] (Spec : GrpcSpecMd Req Rep)
    (h : Svc name = some (.unary ⟨Req.wire, Rep.wire, Spec⟩)) :
    grpcAddrAt (Gg := hG.goose_globalGS) a Svc ⊢ isGrpcRpcMd a name Spec := by
  iintro #Ha
  unfold isGrpcRpcMd
  iexists hX, π, σ
  iapply (grpcSvcAt_of_addr (Gg := hG.goose_globalGS) a name Svc ⟨Req.wire, Rep.wire, Spec⟩ h) $$ Ha

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
  iapply (grpcSpecAt_mono Spec Spec' h ci m Φ Ψe) $$ HSpec

/-- A registration with the metadata-indexed `Spec` is one with a `Spec'` that gives `Spec` after an
update (through `grpcSvcAt_mono_upd`). -/
theorem isGrpcRpcMd_mono_upd {Req Rep : ProtoMsg GF} (addr name : GoString)
    (Spec Spec' : GrpcSpecMd Req Rep) (h : ∀ md m Φ Ψe, Spec' md m Φ Ψe ⊢ |==> Spec md m Φ Ψe) :
    isGrpcRpcMd addr name Spec ⊢ isGrpcRpcMd addr name Spec' := by
  iintro #H
  iunfold isGrpcRpcMd at H
  icases H with ⟨%hX, %π, %σ, #Hs⟩
  unfold isGrpcRpcMd
  iexists hX, π, σ
  iapply (grpcSvcAt_mono_upd (Gg := hG.goose_globalGS) addr name Req.wire Rep.wire Spec Spec') $$ [] Hs
  imodintro
  iintro %md %m %Φ %Ψe HS
  iapply (h md m Φ Ψe) $$ HS

/-- A registration with the metadata-indexed `Spec` is one with a stronger `Spec'`. -/
theorem isGrpcRpcMd_mono {Req Rep : ProtoMsg GF} (addr name : GoString)
    (Spec Spec' : GrpcSpecMd Req Rep) (h : ∀ md m Φ Ψe, Spec' md m Φ Ψe ⊢ Spec md m Φ Ψe) :
    isGrpcRpcMd addr name Spec ⊢ isGrpcRpcMd addr name Spec' :=
  isGrpcRpcMd_mono_upd addr name Spec Spec' (fun md m Φ Ψe => (h md m Φ Ψe).trans BIUpdate.intro)

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
  ihave HSpec := (grpcSpecAt_mono_upd Spec Spec' h ci m Φ Ψe) $$ HSpec
  imod HSpec
  iapply Hm $$ %m %Φ %Ψe %ci %cd %dec %ui [HS Hctx Hrc Hd Hch HSpec] HΨ
  iframe

/-! ## The single-process table: Go's configuration -/

/-- **The entry of Go's configuration for `name` at the message models `Req`, `Rep`** (heap-dependent:
for one process, whose start sets the table): a caller's
precondition is some spec `S` that a handler registered under `name` meets as a run
(`grpcRunOkMd`), with `S`'s precondition. -/
def grpcGoEntry (ics : List GoFunc) (regs : List (GoString × GoFunc × GoInterface)) (name : GoString)
    (Req Rep : ProtoMsgT GF) : GrpcEntry GF :=
  ⟨Req.toProtoMsg.wire, Rep.toProtoMsg.wire, fun md m Φ Ψe =>
    iprop(∃ (mh : GoFunc) (srv : GoInterface) (S : GrpcSpecMd Req.toProtoMsg Rep.toProtoMsg),
      ⌜(name, mh, srv) ∈ regs⌝ ∗ □ grpcRunOkMd #mh srv ics S ∗ S md m Φ Ψe)⟩

/-- **Go's configuration as a service table** (one process): an entry for each
registered unary method `tys` gives message models for (`tys`: the program's unary methods by full
name, with their registered models), none for a stream or an unregistered name. -/
def grpcGoSvc (ics : List GoFunc) (regs : List (GoString × GoFunc × GoInterface))
    (tys : GoString → Option (ProtoMsgT GF × ProtoMsgT GF)) : GrpcSvc GF := fun name =>
  if name ∈ regs.map Prod.fst then (tys name).map (fun p => .unary (grpcGoEntry ics regs name p.1 p.2))
  else none

theorem grpcGoSvc_some (ics : List GoFunc) (regs : List (GoString × GoFunc × GoInterface))
    (tys : GoString → Option (ProtoMsgT GF × ProtoMsgT GF)) (name : GoString) (mh : GoFunc)
    (srv : GoInterface) (Req Rep : ProtoMsgT GF) (hin : (name, mh, srv) ∈ regs)
    (hty : tys name = some (Req, Rep)) :
    grpcGoSvc ics regs tys name = some (.unary (grpcGoEntry ics regs name Req Rep)) := by
  have hm : name ∈ regs.map Prod.fst := List.mem_map.2 ⟨_, hin, rfl⟩
  simp [grpcGoSvc, hm, hty]

/-! `grpcServerAt` and `grpc.serve` are in `InvGrpcRun.lean`: the table they read (`grpcStartSvc`) holds the streams too. -/

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
`Error()` stably returns one of Go's two context messages (`errorMsgIs e m`, `ctxErrMsg m`, hence no
handler's description, `ctxErrMsg_not_handler`; narrowed from `m ∉ handlerDescs` by incomingof Part B
option (a), decided by etcd-grove-03 2026-11-18). This is proved per producer, not claimed of every Go
context: Perennial's context model (`context.ErrAny`: `Canceled` or `DeadlineExceeded`), k8s's
`channelContext` (`chanCtx_ok`), value contexts over those (`withVersion`, `tracing.Start`); etcd's
`v3rpc.cancellableContext`, whose `Err()` may be a `*status.Error` ("etcdserver: no leader"), is excluded
(modelled separately, `InvCancellable`/`SrvCtxWeak`), and any producer for it must fail by `ctxErrMsg`
(`notes/axiom-review/incomingof-b.md`, T2'). (k8s etcd3 7c, HS-5 (a), approved by the user 2026-11-06 via
etcd-grove-82; restated in message form by incomingof Part B, approved by the user 2026-11-17 via
etcd-grove-03: the former
`errDesc err ∉ handlerDescs`, a pure fact about a pointer's description, had no per-run source; grpc
returns `status.FromContextError(ctx.Err())`, which keeps `m`, or prefixes it for an error other than
the two context errors (`transport.ContextErr`: `"Unexpected error from context packet: " + m`), so an
attempt's error would carry a non-handler description with no handler run), and whose shape is a
context error's (`ctxErrShape`: not an `EtcdError`, no `Is` method; `examples/axiomcx/incomingof-real`). The client's `ctxErrClient` has this body (`ctxErrClient_eq_errs`); `ctxErrs` adds `Done()`'s (`ctxDone`, premise fixes 5). It is what a context
outside Perennial's model meets: k8s's `wait.ContextForChannel(stopCh)` (a `channelContext`, whose
`Done()` is `stopCh` and whose `Err()` is `Canceled` once `stopCh` is closed; not an `isContext`,
whose `parentCancelCtx` finds a `*cancelCtx`). (errors-is-deadline, 2026-11-23, approved by the user)
An error of dynamic type `deadlineExceededError` holds `deadlineExceededError{}`. Go guarantees this
by typing (the type's only value), but the model has no typing of interface values. It is what
`errors.Is(err, context.DeadlineExceeded)` needs to compare the error with its target
(`errors.IsDeadlineExceeded`, the client's `contextErrToGRPCErr`). -/
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
        (⌜err = interface.nil⌝ ∨ ∃ (e : GoInterfaceOk) (m : GoString),
          ⌜err = GoInterface.ok e ∧ go_etcd_io.etcd.cache.v3.ctxErrMsg m ∧
            go_etcd_io.etcd.cache.v3.ctxErrShape e ∧
            (e.ty = _root_.Perennial.context.deadlineExceededError.ty →
              e.v = #(zero_val _root_.Perennial.context.deadlineExceededError))⌝ ∗
          go_etcd_io.etcd.cache.v3.errorMsgIs e m) -∗ Φ #err) -∗
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
`Compact`: the full method names grpc sends; 2026-10-23): exactly these five names (2026-11-24, the
second review of `notes/axiom-review/norefusal-link.md`; until then the prefix `/etcdserverpb.KV/`, which
also matched a service a program registers as `etcdserverpb.KV/Evil` beside etcd's: grpc-go dispatches
`/etcdserverpb.KV/Evil/Put` at its last `/`, to that service, so the members' axiom spoke of a method
that is not etcd's; `examples/axiomcx/norefusal/`, `TestMainSlashPanics`). -/
def kvMethod (method : GoString) : Prop :=
  method ∈ [go!"/etcdserverpb.KV/Range", go!"/etcdserverpb.KV/Put", go!"/etcdserverpb.KV/DeleteRange",
    go!"/etcdserverpb.KV/Txn", go!"/etcdserverpb.KV/Compact"]

theorem kvMethod_range : kvMethod go!"/etcdserverpb.KV/Range" := List.Mem.head _
theorem kvMethod_put : kvMethod go!"/etcdserverpb.KV/Put" := .tail _ (.head _)
theorem kvMethod_deleteRange : kvMethod go!"/etcdserverpb.KV/DeleteRange" := .tail _ (.tail _ (.head _))
theorem kvMethod_txn : kvMethod go!"/etcdserverpb.KV/Txn" := .tail _ (.tail _ (.tail _ (.head _)))
theorem kvMethod_compact : kvMethod go!"/etcdserverpb.KV/Compact" :=
  .tail _ (.tail _ (.tail _ (.tail _ (.head _))))

/-- **The server at `addr` never answers a unary call of etcd's KV service with a refusal**
(opaque; D29, 2026-10-21; narrowed to the KV service 2026-10-23, to its five exact method names
2026-11-24): no status it sends in answer to a `kvMethod` call has a description among `refusalDescs`. Established by the trust-boundary axiom of
etcd's members (`etcd_noRefusal`), carried by the network's relays (linkv3p's `forwards`), and read
by the attempt contract (`grpcInvokerOk`) for a `kvMethod` call only. Until 2026-10-23 it covered
every status the server sends, which is false of etcd: its Auth service answers `UserAdd` of an
empty name with `"etcdserver: user name is empty"` even with authentication off
(`authStore.UserAdd`). -/
opaque noRefusalAt : GoString → Prop

/-- **An error that is not `rpctypes.ErrGRPCNotSupportedForLearner`'s value** (persistent; errdesc
stage 2b, 2026-11-21): what grpc's invoker returns is never etcd's package variable (grpc builds its
status errors from the status the server sends, `status.FromProto(...).Err()`, a fresh `*status.Error`,
or returns `io.EOF` or the context's error; it imports no etcd package). What the retry interceptor's
`isSafeRetry` needs: Go's `errors.Is(err, ErrGRPCNotSupportedForLearner)` is `true` of that very value
by `==`, which reads no description, and with no agreement law between two `descIs` of one value the
caller's description of `err` would say nothing of the variable's. -/
def notLearnerErr (err : GoInterface) : IProp GF :=
  iprop(□ ∀ v : GoInterface,
    globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNotSupportedForLearner ↦□ v -∗ ⌜err ≠ v⌝)

instance notLearnerErr_persistent (err : GoInterface) : Persistent (notLearnerErr (GF := GF) err) := by
  unfold notLearnerErr; infer_instance

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

include hG in
/-- **The per-RPC credentials of the connection `conn` returned the metadata `cm` to an attempt**
(raw, opaque; in the end state a definition over `grpcConn`'s ghost record of the credentials'
outputs): `none` if it has none or they returned none; what is known of `cm` is the
credentials' contract at the dial (`grpc.NewClient`'s `connCredsOk`). Trusted text with no law. Its
signature carries the heap's instance (`hG`), which its definition over `grpcConn`'s ghost state will
need. -/
opaque credsYieldRaw (conn : Loc) (cm : GrpcMd) : IProp GF := iprop(True)

/-- **The per-RPC credentials of `conn` returned `cm` to an attempt** (persistent by construction). -/
def credsYield (conn : Loc) (cm : GrpcMd) : IProp GF := iprop(□ credsYieldRaw conn cm)

instance credsYield_persistent (conn : Loc) (cm : GrpcMd) :
    Persistent (credsYield (GF := GF) conn cm) := by
  unfold credsYield; infer_instance

/-- **The handler of an attempt on the connection `conn` with a caller's context whose outgoing
metadata is `om` sees the metadata `md`** (persistent): on every key grpc does not set itself, the values of the connection's per-RPC credentials'
metadata `cm` for the attempt (`credsYield`), then the context's outgoing metadata `om`; and no key with
no values (grpc writes one header field per value, so a key the context carries with none is not sent;
C1's review, F2). True of grpc-go v1.84 (`http2Client.createHeaderFields`, to check in C1's phase 2); the
attempt contract (`grpcInvokerOk`) gives the method's spec at such an `md`. `om` is the context's
metadata value, which the attempt contract's precondition relates to the context
(`metadata.outMD ctx om`). -/
def grpcAttemptMd (conn : Loc) (om md : GrpcMd) : IProp GF :=
  iprop(∃ cm, credsYield conn cm ∗ ⌜(∀ k, ¬ grpcReservedKey k →
      metadata.mdVals md k = metadata.mdVals cm k ++ metadata.mdVals om k) ∧ ∀ k, mdGet md k ≠ some []⌝)

instance grpcAttemptMd_persistent (conn : Loc) (om md : GrpcMd) :
    Persistent (grpcAttemptMd (GF := GF) conn om md) := by
  unfold grpcAttemptMd; infer_instance

/-- **What a stream's attempt delivers on the connection `conn`, whose stream interceptor relates
outgoing metadata by `F`, for a caller's outgoing metadata `om`** (persistent; grpc-trusted-T, T7,
2026-11-24): the handler sees `md`, an attempt's metadata (`grpcAttemptMd`) for some `om'` the
interceptor passed on (`F om om'`). -/
def streamAttemptMd (conn : Loc) (F : GrpcMd → GrpcMd → Prop) (om md : GrpcMd) : IProp GF :=
  iprop(∃ om' : GrpcMd, ⌜F om om'⌝ ∗ grpcAttemptMd conn om' md)

instance streamAttemptMd_persistent (conn : Loc) (F : GrpcMd → GrpcMd → Prop) (om md : GrpcMd) :
    Persistent (streamAttemptMd (GF := GF) conn F om md) := by
  unfold streamAttemptMd; infer_instance

/-- The raw fact behind `grpcConnClosed` (opaque, interim: made only by `ClientConn.Close`'s axiom,
`Spec/google_golang_org/grpc/ClientConn__Close.lean`; S2d's proof of `Close` over the model defines it
from the connection's state). -/
opaque grpcConnClosedRaw (conn : Loc) : IProp GF

/-- **The connection `conn` is closed** (persistent; grpc-trusted-T, T8, 2026-11-24): a
`conn.Close()` returned. Closing is for good: grpc-go v1.84 `ClientConn.Close` cancels `cc.ctx` and
sets `cc.conns` to `nil` (the model's `model_clientconn.go`: `cc.streams = nil`), and nothing reopens
the connection. -/
def grpcConnClosed (conn : Loc) : IProp GF := iprop(□ grpcConnClosedRaw conn)

instance grpcConnClosed_persistent (conn : Loc) : Persistent (grpcConnClosed (GF := GF) conn) := by
  unfold grpcConnClosed; infer_instance

/-- **The context `ctx` is canceled with `context.Canceled`** (persistent; grpc-trusted-T, T4,
2026-11-24): a `*cancelCtx` (`isCancelCtxCtx`, Perennial's: one `WithCancel` made) whose `Err()`
returns `Canceled`'s value, on every call from now on. A `*cancelCtx`'s `Err()` returns its `err`
field, which is set once, so the context is done for good and its error is `Canceled`, not
`DeadlineExceeded` (which `ContextClosed` alone does not say: a context is done for either). -/
def ctxCanceledIs (ctx : GoInterfaceOk) : IProp GF :=
  iprop(∃ (cd : context.ContextDesc (IProp GF)) (e : GoInterface),
    context.isCancelCtxCtx ctx cd ∗ globalAddr _root_.Perennial.context.Canceled ↦□ e ∗
    □ ∀ Φ : val → IProp GF, ▷ Φ #e -∗ WP (App (Val #(methods ctx.ty go!"Err" ctx.v)) (Val #())) {{ Φ }})

instance ctxCanceledIs_persistent (ctx : GoInterfaceOk) :
    Persistent (ctxCanceledIs (GF := GF) ctx) := by
  unfold ctxCanceledIs; infer_instance

/-- **A call grpc's `invoke` fails at once, with `codes.Canceled`** (persistent; grpc-trusted-T, T4,
2026-11-24; interim, retired with `grpcInvokerOk` by S3's proof of `invoke` over the model; what
`ClientConn.Invoke`'s axiom promises of its final invoker beside `grpcInvokerOk`): a call of `inv` on
the connection `conn` when the connection is closed (`grpcConnClosed`), or when its context is
canceled with `Canceled` (`ctxCanceledIs`) and carries no outgoing metadata (`metadata.outMD ctx
none`), with a context grpc can use (`ctxOk`) and call options grpc can apply (as `grpcInvokerOk`'s),
returns a non-nil status error of code `Canceled` (`statusCodeIs err 1`), the peer buffers back; the
request and the reply are not touched. True of grpc-go v1.84 and the model (`models/grpc`):
`newClientStream` first starts the call (`onCallBegin`, the idleness manager's `OnCallBegin`), which
fails with `ErrClientConnClosing` (`status.Error(codes.Canceled, …)`, `clientconn.go:62`) on a closed
connection; then it checks the outgoing metadata (an `Internal` status for an invalid one: none here)
and the call options (`before`, which no `grpcOptOk` option fails), makes `cs.ctx := WithCancel(ctx)`,
which is canceled at once with `ctx.Err()` (`propagateCancel`: `ctx`'s `Done()` channel is closed, its
`Err()` is `Canceled`), and its first attempt (`newAttemptLocked`, `stream.go`) returns
`toRPCErr(cs.ctx.Err())`, `errContextCanceled` (`Canceled`), or `ErrClientConnClosing`, before any
transport is picked; `invoke` returns it. The gRPC driver's `ctx-canceled` and `close` sections. -/
def grpcInvokerDone (conn : Loc) (inv : GoFunc) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (method : GoString)
      (req reply : GoInterface) (opts : GoSlice) (vs : List GoInterface) (ps : List Loc),
    {{ (grpcConnClosed conn ∨ ctxCanceledIs ctx ∗ metadata.outMD ctx none) ∗ ctxOk ctx cd ∗
        opts ↦*□ vs ∗ ⌜∀ v ∈ vs, grpcOptOk ps v⌝ ∗ ([∗list] p ∈ ps, grpcPeerBuf p) }}
      (invokerCall inv #(GoInterface.ok ctx) #method #req #reply #conn #opts)
    {{ (err : GoInterface), RET #err; ([∗list] p ∈ ps, grpcPeerBuf p) ∗
        ⌜err ≠ GoInterface.nil ∧ go_etcd_io.etcd.cache.v3.hasGRPCStatus err⌝ ∗
        go_etcd_io.etcd.cache.v3.statusErrOk err ∗ go_etcd_io.etcd.cache.v3.statusCodeIs err (W32 1) }})

instance grpcInvokerDone_persistent (conn : Loc) (inv : GoFunc) :
    Persistent (grpcInvokerDone (GF := GF) conn inv) := by
  unfold grpcInvokerDone; infer_instance

/-- **One attempt** (persistent; the contract of grpc's `invoke`, the final invoker of a
connection's interceptor chain; unit P3a): a call of a method registered at every address `addrs`
of the connection with `Spec` (`isGrpcRpcs`; D27, 2026-10-21: the attempt goes to one of them),
for the request `inp` (`Req.send`, given back), into the reply `out` (owned, at any content:
`Rep.own`), with call options grpc can apply (`grpcOptOk ps`: scalar, or peer options writing the
buffers `ps`, owned and given back) and the caller's `▷ Spec md m Φ` for every metadata `md` the
attempt's handler may see (`grpcAttemptMd`, at the context's outgoing metadata `om`, `metadata.outMD ctx
om`: errdesc stage 1, 2026-11-20; since 2026-10-28, the auth plan's E3zb, the spec is
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

Since 2026-10-21 (D29, the user's choice) the error is not a refusal (its
description `d`, `descIs err d` since errdesc stage 2b, is none of `refusalDescs`, the descriptions after which etcd's client resends a write)
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
Checked by `examples/k8s/etcd3`'s `TestDefaultNoRace` (`-race`, in the gates).

Since 2026-11-23 (#24's S2 signatures, the resource parameter) the attempt is given a resource `R`
of the connection's family (`Ok R`, `grpcConn`'s) by its caller and gives it back: grpc lends it to
the per-RPC credentials (`perRPCCredsOk pc Ok Q`). True of grpc-go v1.84: `invoke` runs
`newClientStream`, `SendMsg`, `CloseSend` and `RecvMsg` on the caller's goroutine, and the
credentials are called only from there, by `http2Client.createHeaderFields` → `getTrAuthData`
(`internal/transport/http2_client.go:542-549,689-735`) when an attempt's transport stream is made
(`csAttempt.newStream`, `stream.go:495-508`), again for each transparent retry, which
`clientStream.withRetry` (`stream.go:930`) makes synchronously inside the same call; the program's
clients make no calls of their own on the connection (D7). So the credentials run only while the
caller holds `R`, one call at a time. The model of this transport that the network part runs is
`models/grpc/model_transport.go:242,277-345` (`createHeaderFields`'s credential calls).

Since grpc-trusted-T (T4, 2026-11-24; interim, retired with this contract by S3's proof of `invoke` over
the model) the error is a status error (`hasGRPCStatus`: grpc's `*status.Error`) or `io.EOF`'s value
(`eofIs`): the bound the clauses above already give (`clientErr`'s types, `errCellOk`) less the two
types no attempt returns and the `errors.New("context canceled")` value, which `toRPCErr` turns into a
status (`rpc_util.go:1132-1156`: it passes only `nil` and `io.EOF` through; every attempt error goes
through it, `withRetry`, `models/grpc/stream.go:668`, or is a status error grpc makes, `getTransportConn`'s,
`ErrClientConnClosing`, the metadata check's). What a caller that tells grpc's errors apart needs (the
gRPC driver's `errOk`). And it meets the contract of a call that fails at once (`grpcInvokerDone`: a
closed connection, a context canceled with `Canceled`). -/
def grpcInvokerOk (conn : Loc) (addrs : List GoString) (Ok : IProp GF → Prop) (inv : GoFunc) :
    IProp GF :=
  iprop((□ ∀ (method : GoString) (Req Rep : ProtoMsgT GF)
      (_ : grpcReqModelOf GF Req.ty = some Req) (_ : grpcRepModelOf GF Rep.ty = some Rep)
      (Spec : GrpcSpecMd Req.toProtoMsg Rep.toProtoMsg) (m : Req.M)
      (Φ : Rep.M → IProp GF) (Ψe : GoString → IProp GF) (ctx : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (om : GrpcMd)
      (inp out : Loc) (opts : GoSlice) (vs : List GoInterface) (ps : List Loc) (R : IProp GF),
    {{ ⌜Ok R⌝ ∗ R ∗ isGrpcRpcsMd addrs method Spec ∗ metadata.outMD ctx om ∗
        ▷ (∀ md, grpcAttemptMd conn om md -∗ Spec md m Φ Ψe) ∗
        ctxOk ctx cd ∗ Req.send inp m ∗ ⌜Req.wireLen m < grpcMsgMax⌝ ∗
        Rep.own out ∗ opts ↦*□ vs ∗ ⌜∀ v ∈ vs, grpcOptOk ps v⌝ ∗ ([∗list] p ∈ ps, grpcPeerBuf p) }}
      (invokerCall inv #(GoInterface.ok ctx) #method
        #(interface.mkOk (go.GoType.PointerType Req.ty) #inp : GoInterface)
        #(interface.mkOk (go.GoType.PointerType Rep.ty) #out : GoInterface) #conn #opts)
    {{ (err : GoInterface), RET #err; R ∗ Req.send inp m ∗ ([∗list] p ∈ ps, grpcPeerBuf p) ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ m' : Rep.M, Rep.recv out m' ∗ Rep.recvOwn out m' ∗ Φ m') ∨
          (⌜err ≠ GoInterface.nil ∧ clientErr err⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk err ∗
            go_etcd_io.etcd.cache.v3.errCellOk err ∗ Rep.own out ∗ notLearnerErr err ∗
            (⌜go_etcd_io.etcd.cache.v3.hasGRPCStatus err⌝ ∨ eofIs err) ∗
            ∃ d : GoString, go_etcd_io.etcd.cache.v3.descIs err d ∗
            ⌜(kvMethod method ∧ ∀ a ∈ addrs, noRefusalAt a) →
              d ∉ go_etcd_io.etcd.cache.v3.refusalDescs⌝ ∗
            (⌜d ∈ handlerDescs⌝ -∗ Ψe d))) }}) ∗
    grpcInvokerDone conn inv)

instance grpcInvokerOk_persistent (conn : Loc) (addrs : List GoString) (Ok : IProp GF → Prop)
    (inv : GoFunc) : Persistent (grpcInvokerOk (GF := GF) conn addrs Ok inv) := by
  unfold grpcInvokerOk; infer_instance


/-- **No key of the credentials' metadata `cm` is a pseudo-header** (grpc's `createHeaderFields` appends the credentials' fields after the
real `:path`, and a key starting with `:` would be read by the server as the method's path, as
`metadata.ValidateKey`, which grpc does not call on them, would refuse). -/
def credKeysOk (cm : GrpcMd) : Prop :=
  ∀ (k : GoString) (vs : List GoString), mdGet cm k = some vs → k.head? ≠ some (58 : w8)

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
credentials; etcd's `perRPCCredential` returns `nil`), and, a map whose metadata `cm` has `□ Q cm` (what grpc sends with an attempt, `connCredsOk`) and no pseudo-header key (`credKeysOk`); and
`pc.RequireTransportSecurity()` can be called (grpc calls it at the dial to refuse credentials that
need a secure transport on an insecure one; C1's review, F4). Since 2026-11-23 (#24's S2
signatures) `GetRequestMetadata` is called with a resource `R` of the family `Ok` fixed at the dial,
which it gives back (a reader slot of the credentials' lock, for etcd's): grpc calls it only from a
call on the connection, on that call's goroutine, while the call's caller holds such an `R`
(`grpcInvokerOk`, `cliStreamIs`); `RequireTransportSecurity` takes none (grpc-go v1.84 calls it at the
dial and at every transport creation, `http2_client.go:300`; its triple is `{{ True }}`). -/
def perRPCCredsOk (pc : GoInterface) (Ok : IProp GF → Prop) (Q : GrpcMd → IProp GF) : IProp GF :=
  iprop((□ ∀ (ctx : GoInterface) (sl : GoSlice) (R : IProp GF),
    {{ ⌜Ok R⌝ ∗ R }}
      (App (App (App (Val (GoInstruction (MethodResolve
          google_golang_org.grpc.credentials.PerRPCCredentials.ty go!"GetRequestMetadata")))
        (Val #pc)) (Val #ctx)) (Val #sl))
    {{ (mp : Loc) (err : GoInterface), RET (PairV #mp #err); R ∗
        ⌜err = GoInterface.nil⌝ ∗
        (⌜err = GoInterface.nil⌝ -∗ ∃ cm, credsMapIs mp cm ∗ ⌜credKeysOk cm⌝ ∗ □ Q cm) }}) ∗
    □ {{ True }}
      (App (App (Val (GoInstruction (MethodResolve
          google_golang_org.grpc.credentials.PerRPCCredentials.ty go!"RequireTransportSecurity")))
        (Val #pc)) (Val #()))
    {{ (b : Bool), RET #b; True }})

instance perRPCCredsOk_persistent (pc : GoInterface) (Ok : IProp GF → Prop) (Q : GrpcMd → IProp GF) :
    Persistent (perRPCCredsOk pc Ok Q) := by
  unfold perRPCCredsOk; infer_instance

/-- **What the per-RPC credentials `pcs` of the connection `conn` returned to its attempts**
(persistent; the auth plan's C1, 2026-10-28; `grpc.NewClient`'s post, from the credentials'
contract at the dial, `perRPCCredsOk`): with no credentials, nothing (`none`); with one, metadata
meeting `Q`; with more, nothing is stated. -/
def connCredsOk (conn : Loc) (pcs : List GoInterface) (Q : GrpcMd → IProp GF) : IProp GF :=
  match pcs with
  | [] => iprop(□ ∀ cm, credsYield conn cm -∗ ⌜cm = none⌝)
  | [_] => iprop(□ ∀ cm, credsYield conn cm -∗ □ Q cm)
  | _ => iprop(True)

instance connCredsOk_persistent (conn : Loc) (pcs : List GoInterface) (Q : GrpcMd → IProp GF) :
    Persistent (connCredsOk conn pcs Q) := by
  unfold connCredsOk; split <;> infer_instance

/-- **The interceptor chain `ics` over the final invoker `inv`, with the resource `R`** (unit P3a;
grpc's `chainUnaryClientInterceptors`, `getChainUnaryInvoker`; the resource parameter since
2026-11-23, #24's S2 signatures): each call is given `R` and gives it back with its result
(`R -∗ WP … {{ v, R ∗ Ψ v }}`). With no interceptor, the call is `inv`'s; otherwise the first
interceptor is called with an invoker `inv'` of grpc's making, whose calls (on the same connection,
with the same `R`) are the rest of the chain's. `Ψ` is the call's postcondition. True of grpc-go
v1.84: `chainUnaryInterceptors` and `getChainUnaryInvoker` (`clientconn.go`/`dialoptions.go`'s
chaining) are closures calling the next interceptor or `invoke` synchronously on the caller's
goroutine. -/
def chainWP (R : IProp GF) (conn : Loc) : List GoFunc → GoFunc → val → val → val → val → val →
    (val → IProp GF) → IProp GF
  | [], inv, ctx, method, req, reply, opts, Ψ =>
    iprop(R -∗ WP (invokerCall inv ctx method req reply #conn opts) {{ v, R ∗ Ψ v }})
  | ic :: ics, inv, ctx, method, req, reply, opts, Ψ =>
    iprop(∀ inv' : GoFunc,
      (□ ∀ (ctx' method' req' reply' opts' : val) (Ψ' : val → IProp GF),
        chainWP R conn ics inv ctx' method' req' reply' opts' Ψ' -∗
        R -∗ WP (invokerCall inv' ctx' method' req' reply' #conn opts') {{ v, R ∗ Ψ' v }}) -∗
      R -∗ WP (interceptorCall ic ctx method req reply #conn inv' opts) {{ v, R ∗ Ψ v }})

/-- An invoker that behaves as one meeting the attempt contract meets it. -/
theorem grpcInvokerOk_of_wp (conn : Loc) (addr : List GoString) (Ok : IProp GF → Prop)
    (inv inv' : GoFunc) :
    grpcInvokerOk (GF := GF) conn addr Ok inv ∗
      (□ ∀ (ctx' method' req' reply' opts' : val) (Ψ' : val → IProp GF),
        WP (invokerCall inv ctx' method' req' reply' #conn opts') {{ Ψ' }} -∗
        WP (invokerCall inv' ctx' method' req' reply' #conn opts') {{ Ψ' }}) ⊢
    grpcInvokerOk conn addr Ok inv' := by
  iintro ⟨#Hinv, #Hw⟩
  unfold grpcInvokerOk
  icases Hinv with ⟨#Hinv, #Hdone⟩
  isplitl []
  · iintro !> %method %Req %Rep %hreq %hrep %Spec %m %Φ %Ψe %ctx %cd %om %inp %out %opts %vs %ps %R
    iintro %Ψ !> Hpre HΨ
    iapply Hw
    iapply Hinv $$ %method %Req %Rep %hreq %hrep %Spec %m %Φ %Ψe %ctx %cd %om %inp %out %opts %vs %ps
      %R %Ψ Hpre HΨ
  · unfold grpcInvokerDone
    iintro !> %ctx %cd %method %req %reply %opts %vs %ps %Ψ !> Hpre HΨ
    iapply Hw
    iapply Hdone $$ %ctx %cd %method %req %reply %opts %vs %ps %Ψ Hpre HΨ

/-- An invoker that behaves as one meeting the attempt contract, through a chain's invoker at the
trivial resource (`chainWP iprop(True)`'s `inv'`), meets it. -/
theorem grpcInvokerOk_of_chainTrue (conn : Loc) (addr : List GoString) (Ok : IProp GF → Prop)
    (inv inv' : GoFunc) :
    grpcInvokerOk (GF := GF) conn addr Ok inv ∗
      (□ ∀ (ctx' method' req' reply' opts' : val) (Ψ' : val → IProp GF),
        (iprop(True) -∗ WP (invokerCall inv ctx' method' req' reply' #conn opts')
          {{ v, iprop(True) ∗ Ψ' v }}) -∗
        iprop(True) -∗ WP (invokerCall inv' ctx' method' req' reply' #conn opts')
          {{ v, iprop(True) ∗ Ψ' v }}) ⊢
    grpcInvokerOk conn addr Ok inv' := by
  iintro ⟨#Hinv, #Hw⟩
  iapply grpcInvokerOk_of_wp conn addr Ok inv inv'
  iframe Hinv
  iintro !> %ctx' %method' %req' %reply' %opts' %Ψ' Hwp
  iapply wp_true_sep
  iapply Hw $$ [Hwp] []
  · iintro -
    iapply wp_wand_r
    isplitl [Hwp]
    · iexact Hwp
    iintro %v Hv
    iframe
  · itrivial

end client

end reg

end EtcdGrove
end Perennial
