/-
**The KV service's generated unary handlers, once** (`_KV_Range_Handler`, `_KV_Put_Handler`,
`_KV_DeleteRange_Handler`, `_KV_Txn_Handler`, `api/etcdserverpb/rpc_grpc.pb.go`). protoc-gen-go-grpc
emits the same body for every unary method, up to the method's name and its request and response
types; `unaryHandlerImpl` is that body as Goose translates it, with those as parameters, and
`wp_unaryHandler` proves it once. Each handler's proof (`Proof/.../_KV_<M>_Handler.lean`) applies
the lemma at its method; the build checks that the handler's translation is `unaryHandlerImpl` at
those parameters (the `FuncUnfold` instance's type, by unfolding), so a regenerated handler of a
different shape breaks the build, not soundness. Lean-first (no Rocq counterpart).
-/
module

public import Proof.google_golang_org.grpc.InvGrpc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

/-- **A generated unary handler's body** (`func _S_M_Handler(srv any, ctx context.Context,
dec func(any) error, interceptor grpc.UnaryServerInterceptor) (any, error)`, as Goose translates
it): decode a new `*Req` (`reqTy`) with `dec`; with no interceptor, call `srv.(S).M(ctx, in)`
(`srvTy`, `meth`); otherwise call the interceptor with an `info` naming `fullMethod` and a
closure making that call. The response is returned as `any` (from `*Rep`, `repTy`). -/
def unaryHandlerImpl [GooseExts] [GoGlobalContext] (srvTy reqTy repTy : go.GoType)
    (meth fullMethod : GoString) : val :=
    (LamV "srv"
    (Lam "ctx"
    (Lam "dec"
    (Lam "interceptor"
    (App (Val exceptionDo)
    (Let "interceptor" (App (Val (GoInstruction (GoAlloc _root_.Perennial.google_golang_org.grpc.UnaryServerInterceptor.ty))) (Var "interceptor"))
    (Let "dec" (App (Val (GoInstruction (GoAlloc (go.GoType.FunctionType (go.signature.Signature [(go.GoType.InterfaceType [])] false [go.error]))))) (Var "dec"))
    (Let "ctx" (App (Val (GoInstruction (GoAlloc _root_.Perennial.context.Context.ty))) (Var "ctx"))
    (Let "srv" (App (Val (GoInstruction (GoAlloc (go.GoType.InterfaceType [])))) (Var "srv"))
    (Let "$r0" (App (Val (GoInstruction (GoAlloc reqTy))) (App (Val (GoInstruction (GoZeroVal reqTy))) (Val #())))
    (Let "in" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType reqTy)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType reqTy)))) (Val #())))
    (App (App (Val exceptionSeq) (Lam BAnon
    (App (App (Val exceptionSeq) (Lam BAnon
    (App (App (Val exceptionSeq) (Lam BAnon
    (Let "$r0" (App (Val (GoInstruction (GoAlloc _root_.Perennial.google_golang_org.grpc.UnaryServerInfo.ty))) (Let "$v0" (App (Val (GoInstruction (GoLoad (go.GoType.InterfaceType [])))) (Var "srv"))
    (Let "$v1" (App (Val (GoInstruction (Convert go.untypedString go.string))) (Val #fullMethod))
    (App (Val (GoInstruction (CompositeLiteral _root_.Perennial.google_golang_org.grpc.UnaryServerInfo.ty))) (LiteralValue [(KeyedElement (some (KeyField go!"Server")) (ElementExpression (go.GoType.InterfaceType []) (Var "$v0"))), (KeyedElement (some (KeyField go!"FullMethod")) (ElementExpression go.string (Var "$v1")))])))))
    (Let "info" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.google_golang_org.grpc.UnaryServerInfo.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType _root_.Perennial.google_golang_org.grpc.UnaryServerInfo.ty)))) (Val #())))
    (App (App (Val exceptionSeq) (Lam BAnon
    (Let "$r0" (Lam "ctx"
    (Lam "req"
    (App (Val exceptionDo)
    (Let "req" (App (Val (GoInstruction (GoAlloc (go.GoType.InterfaceType [])))) (Var "req"))
    (Let "ctx" (App (Val (GoInstruction (GoAlloc _root_.Perennial.context.Context.ty))) (Var "ctx"))
    (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.context.Context.ty))) (Var "ctx"))
    (Let "$a1" (App (Val (GoInstruction (TypeAssert (go.GoType.PointerType reqTy)))) (App (Val (GoInstruction (GoLoad (go.GoType.InterfaceType [])))) (Var "req")))
    (App (App (App (Val (GoInstruction (MethodResolve srvTy meth))) (App (Val (GoInstruction (TypeAssert srvTy))) (App (Val (GoInstruction (GoLoad (go.GoType.InterfaceType [])))) (Var "srv")))) (Var "$a0")) (Var "$a1"))))
    (Let "$ret0" (Fst (Var "__p"))
    (Let "$ret1" (Snd (Var "__p"))
    (App (Val doReturn)
    (Pair (App (Val (GoInstruction (Convert (go.GoType.PointerType repTy) (go.GoType.InterfaceType [])))) (Var "$ret0")) (Var "$ret1")))))))))))
    (Let "handler" (App (Val (GoInstruction (GoAlloc (go.GoType.FunctionType (go.signature.Signature [_root_.Perennial.context.Context.ty, (go.GoType.InterfaceType [])] false [(go.GoType.InterfaceType []), go.error]))))) (App (Val (GoInstruction (GoZeroVal (go.GoType.FunctionType (go.signature.Signature [_root_.Perennial.context.Context.ty, (go.GoType.InterfaceType [])] false [(go.GoType.InterfaceType []), go.error]))))) (Val #())))
    (App (App (Val exceptionSeq) (Lam BAnon
    (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.context.Context.ty))) (Var "ctx"))
    (Let "$a1" (App (Val (GoInstruction (Convert (go.GoType.PointerType reqTy) go.any))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType reqTy)))) (Var "in")))
    (Let "$a2" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.google_golang_org.grpc.UnaryServerInfo.ty)))) (Var "info"))
    (Let "$a3" (App (Val (GoInstruction (GoLoad (go.GoType.FunctionType (go.signature.Signature [_root_.Perennial.context.Context.ty, (go.GoType.InterfaceType [])] false [(go.GoType.InterfaceType []), go.error]))))) (Var "handler"))
    (App (App (App (App (App (Val (GoInstruction (GoLoad _root_.Perennial.google_golang_org.grpc.UnaryServerInterceptor.ty))) (Var "interceptor")) (Var "$a0")) (Var "$a1")) (Var "$a2")) (Var "$a3"))))))
    (Let "$ret0" (Fst (Var "__p"))
    (Let "$ret1" (Snd (Var "__p"))
    (App (Val doReturn)
    (Pair (Var "$ret0") (Var "$ret1"))))))))
    (App (Val doExecute)
    (App (Val (GoInstruction (GoStore (go.GoType.FunctionType (go.signature.Signature [_root_.Perennial.context.Context.ty, (go.GoType.InterfaceType [])] false [(go.GoType.InterfaceType []), go.error]))))) (Pair (Var "handler") (Var "$r0")))))))))
    (App (Val doExecute)
    (App (Val (GoInstruction (GoStore (go.GoType.PointerType _root_.Perennial.google_golang_org.grpc.UnaryServerInfo.ty)))) (Pair (Var "info") (Var "$r0")))))))))
    (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals _root_.Perennial.google_golang_org.grpc.UnaryServerInterceptor.ty))) (Pair (App (Val (GoInstruction (GoLoad _root_.Perennial.google_golang_org.grpc.UnaryServerInterceptor.ty))) (Var "interceptor")) (App (Val (GoInstruction (Convert go.untypedNil _root_.Perennial.google_golang_org.grpc.UnaryServerInterceptor.ty))) (Val UntypedNil)))))
    (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.context.Context.ty))) (Var "ctx"))
    (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType reqTy)))) (Var "in"))
    (App (App (App (Val (GoInstruction (MethodResolve srvTy meth))) (App (Val (GoInstruction (TypeAssert srvTy))) (App (Val (GoInstruction (GoLoad (go.GoType.InterfaceType [])))) (Var "srv")))) (Var "$a0")) (Var "$a1"))))
    (Let "$ret0" (Fst (Var "__p"))
    (Let "$ret1" (Snd (Var "__p"))
    (App (Val doReturn)
    (Pair (App (Val (GoInstruction (Convert (go.GoType.PointerType repTy) (go.GoType.InterfaceType [])))) (Var "$ret0")) (Var "$ret1"))))))
    (App (Val doExecute)
    (Val #()))))))
    (Let "$r0" (Let "$a0" (App (Val (GoInstruction (Convert (go.GoType.PointerType reqTy) (go.GoType.InterfaceType [])))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType reqTy)))) (Var "in")))
    (App (App (Val (GoInstruction (GoLoad (go.GoType.FunctionType (go.signature.Signature [(go.GoType.InterfaceType [])] false [go.error]))))) (Var "dec")) (Var "$a0")))
    (Let "err" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
    (App (App (Val exceptionSeq) (Lam BAnon
    (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
    (App (Val doReturn)
    (Pair (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.InterfaceType [])))) (Val UntypedNil)) (App (Val (GoInstruction (GoLoad go.error))) (Var "err"))))
    (App (Val doExecute)
    (Val #())))))
    (App (Val doExecute)
    (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r0"))))))))))
    (App (Val doExecute)
    (App (Val (GoInstruction (GoStore (go.GoType.PointerType reqTy)))) (Pair (Var "in") (Var "$r0"))))))))))))))))


section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- **A generated unary handler `h` (body `unaryHandlerImpl srvTy reqTy repTy meth fullMethod`)
meets the metadata-indexed handler spec (`grpcHandlerOwnOkMd`; the auth plan's E3zb), for a method that may write its request** (`grpcHandlerOwnOk`; the auth
plan's E3za) (the statement of `_KV_Put_Handler.spec`, at any method): for a service
value whose type implements `srvTy` and whose method `meth` meets `Spec` with `S`, it decodes a
new `*Req` (`V`, Go type `reqTy`; a zero one is the request's blank) and runs `srv.meth`, directly
or through the chain `ics` of transparent interceptors (with `info` naming its `FullMethod`); the
resources come back, and on success the response is at some `m'` with `Φ m'`.

The proof: `dec` gives the decoded request or an error (returned). With no interceptor
(`ui = nil`, so `ics = []`), the call of `srv.meth` is the result. Otherwise the chain
(`grpcSrvChain`) runs over the generated closure (`srvChainWP_of_ok`): it calls `srv.meth` and
returns its result, or the chain returns an error without calling it. -/
theorem wp_unaryHandlerOwnMd (h : GoString) (srvTy reqTy repTy : go.GoType) (meth fullMethod : GoString)
    {elems : List go.InterfaceElem} [go.UnderlyingDirectedEq srvTy (go.InterfaceType elems)]
    {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V reqTy]
    [FuncUnfold h [] (unaryHandlerImpl srvTy reqTy repTy meth fullMethod)] :
  ∀ (Req Rep : ProtoMsg GF) (Spec : GrpcSpecMd Req Rep) (srv : GoInterfaceOk) (S : IProp GF)
    (ics : List GoFunc) (Rs : List (IProp GF)) (Q : GoInterface → IProp GF) (m : Req.M)
    (Φ : Rep.M → IProp GF)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (dec ui : GoFunc),
  Req.ty = reqTy → Rep.ty = repTy →
  go.typeSetContains srv.ty srvTy = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      (□ ∀ l : Loc, l ↦ (zero_val V) -∗ Req.blank l) ∗
      grpcHandlerOwnOkMd #(methods srv.ty meth srv.v) S Spec ∗ srvInterceptorsOk Q ics Rs ∗
      (□ ∀ l : Loc, Req.recv l m -∗
        Q (interface.mkOk (go.GoType.PointerType reqTy) #l)) ∗
      S ∗ ([∗list] R ∈ Rs, R) ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ grpcDecOk dec Req m ∗
      grpcSrvChain ics ui ∗ Spec (metadata.incomingOf (GoInterface.ok ci)) m Φ }}
    (methodHandlerCall (@! h) #(GoInterface.ok srv) #(GoInterface.ok ci) dec ui)
  {{ (resp err : GoInterface), RET (PairV #resp #err); S ∗ ([∗list] R ∈ Rs, R) ∗
      (⌜err = GoInterface.nil⌝ -∗ ∃ (l : Loc) (m' : Rep.M),
        ⌜resp = interface.mkOk (go.GoType.PointerType Rep.ty) #l⌝ ∗ Rep.send l m' ∗ Φ m') }} := by
  intro Req Rep Spec srv S ics Rs Q m Φ' ci cd dec ui hReq hRep hsrv
  wp_start as ⟨#Hblank, #Hh, #Hics, #HQ, HS, HRs, #Hctx, #Hrc, #Hdec, #Hchain, HSpec⟩
  wp_auto
  ihave Hb := Hblank $$ %«$r0_ptr» «$r0»
  ihave #Hdec' := grpcDecOk_ty dec Req m _ hReq $$ Hdec
  ihave #Hd2 := Hdec' $$ %«$r0_ptr»
  wp_bind (App (Val #dec) _)
  iapply Hd2 $$ Hb
  inext
  iintro %err Herr
  icases Herr with (⟨%Herr, #Hr, Ho⟩ | %Herr)
  · subst Herr
    wp_auto
    wp_if_destruct
    · simp only [hsrv]
      wp_auto
      iunfold grpcHandlerOwnOkMd at Hh
      wp_bind (App (App (Val _) (Val #(GoInterface.ok ci))) (Val #«$r0_ptr»))
      iapply Hh $$ %m %Φ' %ci %cd %«$r0_ptr» [HS HSpec Ho]
      · iframe; iframe #
      inext
      iintro %resp %err' ⟨HS, Hres⟩
      wp_auto
      iapply HΦ
      iframe
      iintro %Hnil
      ihave ⟨%m', Hm', HΦ'⟩ := Hres $$ %Hnil
      iexists resp, m'
      iframe
      ipureintro; rw [hRep]
    · cases ics with
      | nil =>
        iunfold grpcSrvChain at Hchain
        icases Hchain with %Hc
        exact absurd Hc Hif
      | cons ic ics' =>
        iunfold grpcSrvChain at Hchain
        icases Hchain with ⟨-, #Hchain⟩
        iStructNamed «$r0»
        ipersist FullMethod
        ipersist srv
        ihave #HQr := HQ $$ Hr
        ihave #Hinfo : srvInfoIs (GF := GF) «$r0_ptr» $$ []
        · iunfold srvInfoIs
          iexists _
          iexact FullMethod
        wp_bind (App (App (App (App (Val #ui) _) _) _) _)
        iapply Hchain
        iapply srvChainWP_of_ok
        iframe #
        iframe
        isplit
        · iunfold srvHandlerCall
          wp_auto
          simp only [hsrv]
          wp_auto
          iunfold grpcHandlerOwnOkMd at Hh
          wp_bind (App (App (Val _) (Val #(GoInterface.ok ci))) (Val _))
          iapply Hh $$ %m %Φ' %ci %cd %_ [HS HSpec Ho]
          · iframe; iframe #
          inext
          iintro %resp %err' ⟨HS, Hres⟩
          wp_auto
          iexists _, _
          isplitr
          · ipureintro; rfl
          iintro HRs
          wp_auto
          iapply HΦ
          iframe
          iintro %Hnil
          ihave ⟨%m', Hm', HΦ'⟩ := Hres $$ %Hnil
          iexists resp, m'
          iframe
          ipureintro; rw [hRep]
        · iintro HRs %err' %Herr'
          wp_auto
          iapply HΦ
          iframe
          iintro %Hc
          exact absurd Hc Herr'
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei =>
      wp_auto
      iapply HΦ
      iframe
      iintro %Hc
      cases Hc

/-- **A generated unary handler `h` (body `unaryHandlerImpl srvTy reqTy repTy meth fullMethod`)
meets the metadata-indexed handler spec** (from `wp_unaryHandlerOwnMd`) (the statement of `_KV_Put_Handler.spec`, at any method): for a service
value whose type implements `srvTy` and whose method `meth` meets `Spec` with `S`, it decodes a
new `*Req` (`V`, Go type `reqTy`; a zero one is the request's blank) and runs `srv.meth`, directly
or through the chain `ics` of transparent interceptors (with `info` naming its `FullMethod`); the
resources come back, and on success the response is at some `m'` with `Φ m'`. -/
theorem wp_unaryHandlerMd (h : GoString) (srvTy reqTy repTy : go.GoType) (meth fullMethod : GoString)
    {elems : List go.InterfaceElem} [go.UnderlyingDirectedEq srvTy (go.InterfaceType elems)]
    {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V reqTy]
    [FuncUnfold h [] (unaryHandlerImpl srvTy reqTy repTy meth fullMethod)] :
  ∀ (Req Rep : ProtoMsg GF) (Spec : GrpcSpecMd Req Rep) (srv : GoInterfaceOk) (S : IProp GF)
    (ics : List GoFunc) (Rs : List (IProp GF)) (Q : GoInterface → IProp GF) (m : Req.M)
    (Φ : Rep.M → IProp GF)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (dec ui : GoFunc),
  Req.ty = reqTy → Rep.ty = repTy →
  go.typeSetContains srv.ty srvTy = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      (□ ∀ l : Loc, l ↦ (zero_val V) -∗ Req.blank l) ∗
      grpcHandlerOkMd #(methods srv.ty meth srv.v) S Spec ∗ srvInterceptorsOk Q ics Rs ∗
      (□ ∀ l : Loc, Req.recv l m -∗
        Q (interface.mkOk (go.GoType.PointerType reqTy) #l)) ∗
      S ∗ ([∗list] R ∈ Rs, R) ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ grpcDecOk dec Req m ∗
      grpcSrvChain ics ui ∗ Spec (metadata.incomingOf (GoInterface.ok ci)) m Φ }}
    (methodHandlerCall (@! h) #(GoInterface.ok srv) #(GoInterface.ok ci) dec ui)
  {{ (resp err : GoInterface), RET (PairV #resp #err); S ∗ ([∗list] R ∈ Rs, R) ∗
      (⌜err = GoInterface.nil⌝ -∗ ∃ (l : Loc) (m' : Rep.M),
        ⌜resp = interface.mkOk (go.GoType.PointerType Rep.ty) #l⌝ ∗ Rep.send l m' ∗ Φ m') }} := by
  intro Req Rep Spec srv S ics Rs Q m Φ' ci cd dec ui hReq hRep hsrv
  iintro %Φ ⟨#Pk, #Hb, #Hh, #Hics, #HQ, HS, HRs, #Hctx, #Hrc, #Hdec, #Hch, HSpec⟩ HΦ
  ihave #Hh' := grpcHandlerOkMd_own _ S Spec $$ Hh
  iapply (wp_unaryHandlerOwnMd (V := V) h srvTy reqTy repTy meth fullMethod Req Rep Spec srv S ics Rs Q
    m Φ' ci cd dec ui hReq hRep hsrv) $$ [HS HRs HSpec] HΦ
  iframe; iframe #

/-- **A generated unary handler `h` (body `unaryHandlerImpl srvTy reqTy repTy meth fullMethod`)
meets the handler spec, for a method that may write its request** (`grpcHandlerOwnOk`; the auth
plan's E3za) (the statement of `_KV_Put_Handler.spec`, at any method): for a service
value whose type implements `srvTy` and whose method `meth` meets `Spec` with `S`, it decodes a
new `*Req` (`V`, Go type `reqTy`; a zero one is the request's blank) and runs `srv.meth`, directly
or through the chain `ics` of transparent interceptors (with `info` naming its `FullMethod`); the
resources come back, and on success the response is at some `m'` with `Φ m'`.

The proof: `dec` gives the decoded request or an error (returned). With no interceptor
(`ui = nil`, so `ics = []`), the call of `srv.meth` is the result. Otherwise the chain
(`grpcSrvChain`) runs over the generated closure (`srvChainWP_of_ok`): it calls `srv.meth` and
returns its result, or the chain returns an error without calling it. -/
theorem wp_unaryHandlerOwn (h : GoString) (srvTy reqTy repTy : go.GoType) (meth fullMethod : GoString)
    {elems : List go.InterfaceElem} [go.UnderlyingDirectedEq srvTy (go.InterfaceType elems)]
    {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V reqTy]
    [FuncUnfold h [] (unaryHandlerImpl srvTy reqTy repTy meth fullMethod)] :
  ∀ (Req Rep : ProtoMsg GF) (Spec : GrpcSpec Req Rep) (srv : GoInterfaceOk) (S : IProp GF)
    (ics : List GoFunc) (Rs : List (IProp GF)) (Q : GoInterface → IProp GF) (m : Req.M)
    (Φ : Rep.M → IProp GF)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (dec ui : GoFunc),
  Req.ty = reqTy → Rep.ty = repTy →
  go.typeSetContains srv.ty srvTy = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      (□ ∀ l : Loc, l ↦ (zero_val V) -∗ Req.blank l) ∗
      grpcHandlerOwnOk #(methods srv.ty meth srv.v) S Spec ∗ srvInterceptorsOk Q ics Rs ∗
      (□ ∀ l : Loc, Req.recv l m -∗
        Q (interface.mkOk (go.GoType.PointerType reqTy) #l)) ∗
      S ∗ ([∗list] R ∈ Rs, R) ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ grpcDecOk dec Req m ∗
      grpcSrvChain ics ui ∗ Spec m Φ }}
    (methodHandlerCall (@! h) #(GoInterface.ok srv) #(GoInterface.ok ci) dec ui)
  {{ (resp err : GoInterface), RET (PairV #resp #err); S ∗ ([∗list] R ∈ Rs, R) ∗
      (⌜err = GoInterface.nil⌝ -∗ ∃ (l : Loc) (m' : Rep.M),
        ⌜resp = interface.mkOk (go.GoType.PointerType Rep.ty) #l⌝ ∗ Rep.send l m' ∗ Φ m') }} :=
  fun Req Rep Spec => wp_unaryHandlerOwnMd (V := V) h srvTy reqTy repTy meth fullMethod Req Rep
    (GrpcSpec.md Spec)

/-- **A generated unary handler `h` (body `unaryHandlerImpl srvTy reqTy repTy meth fullMethod`)
meets the handler spec** (from `wp_unaryHandlerOwn`) (the statement of `_KV_Put_Handler.spec`, at any method): for a service
value whose type implements `srvTy` and whose method `meth` meets `Spec` with `S`, it decodes a
new `*Req` (`V`, Go type `reqTy`; a zero one is the request's blank) and runs `srv.meth`, directly
or through the chain `ics` of transparent interceptors (with `info` naming its `FullMethod`); the
resources come back, and on success the response is at some `m'` with `Φ m'`. -/
theorem wp_unaryHandler (h : GoString) (srvTy reqTy repTy : go.GoType) (meth fullMethod : GoString)
    {elems : List go.InterfaceElem} [go.UnderlyingDirectedEq srvTy (go.InterfaceType elems)]
    {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V reqTy]
    [FuncUnfold h [] (unaryHandlerImpl srvTy reqTy repTy meth fullMethod)] :
  ∀ (Req Rep : ProtoMsg GF) (Spec : GrpcSpec Req Rep) (srv : GoInterfaceOk) (S : IProp GF)
    (ics : List GoFunc) (Rs : List (IProp GF)) (Q : GoInterface → IProp GF) (m : Req.M)
    (Φ : Rep.M → IProp GF)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (dec ui : GoFunc),
  Req.ty = reqTy → Rep.ty = repTy →
  go.typeSetContains srv.ty srvTy = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      (□ ∀ l : Loc, l ↦ (zero_val V) -∗ Req.blank l) ∗
      grpcHandlerOk #(methods srv.ty meth srv.v) S Spec ∗ srvInterceptorsOk Q ics Rs ∗
      (□ ∀ l : Loc, Req.recv l m -∗
        Q (interface.mkOk (go.GoType.PointerType reqTy) #l)) ∗
      S ∗ ([∗list] R ∈ Rs, R) ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ grpcDecOk dec Req m ∗
      grpcSrvChain ics ui ∗ Spec m Φ }}
    (methodHandlerCall (@! h) #(GoInterface.ok srv) #(GoInterface.ok ci) dec ui)
  {{ (resp err : GoInterface), RET (PairV #resp #err); S ∗ ([∗list] R ∈ Rs, R) ∗
      (⌜err = GoInterface.nil⌝ -∗ ∃ (l : Loc) (m' : Rep.M),
        ⌜resp = interface.mkOk (go.GoType.PointerType Rep.ty) #l⌝ ∗ Rep.send l m' ∗ Φ m') }} :=
  fun Req Rep Spec => wp_unaryHandlerMd (V := V) h srvTy reqTy repTy meth fullMethod Req Rep
    (GrpcSpec.md Spec)

end proof

end EtcdGrove
end Perennial
