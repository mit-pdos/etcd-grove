/- Lean-first (no Rocq counterpart).

`svc._Driver_Fail_Handler(srv, ctx, dec, interceptor)` (`svc/svc.go`, the generated server-side
handler of the driver's `Fail`), as etcd's generated handlers' (`etcdserverpb._Auth_AuthEnable_Handler`):
for a service value `srv` whose type implements `DriverServer` and whose `Fail` meets `Spec` with
the resource `S` and the interceptors' resources `Rs`, for messages of type `*StringValue`, under
the chain `ics` of transparent interceptors, with grpc's `dec` for the request at `m` and `Spec` at
the run's incoming metadata: decodes a new `*StringValue` and runs `srv.Fail` through the chain; the
resources come back, and on success the response (as `any`) is at some `m'` with `Φ m'`.
-/
module

public import Proof.google_golang_org.grpc.InvGrpc
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI EtcdGrove google_golang_org.protobuf.types.known

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

/-- See the file header. -/
abbrev _Driver_Fail_Handler.spec : Prop :=
  ∀ (Req Rep : ProtoMsg GF) (Spec : GrpcSpecMd Req Rep) (srv : GoInterfaceOk) (S : IProp GF)
    (ics : List GoFunc) (Rs : List (IProp GF)) (Q : GoInterface → IProp GF) (m : Req.M)
    (Φ : Rep.M → IProp GF) (Ψe : GoString → IProp GF)
    (ci : GoInterfaceOk) (cd : _root_.Perennial.context.ContextDesc (IProp GF)) (dec ui : GoFunc),
  Req.ty = wrapperspb.StringValue.ty → Rep.ty = wrapperspb.StringValue.ty →
  go.typeSetContains srv.ty DriverServer.ty = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc ∗
      (□ ∀ l : Loc, l ↦ (zero_val wrapperspb.StringValue) -∗ Req.blank l) ∗
      grpcHandlerOwnOkMd #(methods srv.ty go!"Fail" srv.v) iprop(S ∗ [∗list] R ∈ Rs, R) Spec ∗
      srvInterceptorsOk Q ics Rs ∗
      (□ ∀ l : Loc, Req.recv l m -∗
        Q (interface.mkOk (go.GoType.PointerType wrapperspb.StringValue.ty) #l)) ∗
      S ∗ ([∗list] R ∈ Rs, R) ∗ _root_.Perennial.context.isContext ci cd ∗ grpcRunCtx ci ∗
      grpcDecOk dec Req m ∗ grpcSrvChainAll ics ui ∗ grpcSpecAt Spec ci m Φ Ψe }}
    (methodHandlerCall (@! _Driver_Fail_Handler) #(GoInterface.ok srv)
      #(GoInterface.ok ci) dec ui)
  {{ (resp err : GoInterface), RET (PairV #resp #err); S ∗ ([∗list] R ∈ Rs, R) ∗
      (⌜err = GoInterface.nil⌝ -∗ ∃ (l : Loc) (m' : Rep.M),
        ⌜resp = interface.mkOk (go.GoType.PointerType Rep.ty) #l⌝ ∗ Rep.send l m' ∗ Φ m') ∗
      handlerErrOut Ψe err ∗ go_etcd_io.etcd.cache.v3.srvErrOk err }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc
end Perennial
