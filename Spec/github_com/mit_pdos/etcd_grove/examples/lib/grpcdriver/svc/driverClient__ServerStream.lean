/- Lean-first (no Rocq counterpart).

`(*driverClient).ServerStream(ctx, in)` (svc.go, no call options): a stream of the driver's
`ServerStream` on the stub's connection (no stream interceptor), its one request `in` (at `v`, with the
client's content `Up 0 v`) sent and the up queue closed: on success, the wrapped client end
(`cliBidiStreamIs`), the request first up (`upLb γ [v]`, `upClosed γ [v]`), the receiver's token at
`[]` and the stream's specification; otherwise the error (`cliStreamErr`, of grpc's own shape).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.ClientStreamDefs
public import Proof.go_etcd_io.etcd.client.v3.InvRetry

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

/-- See the file header. -/
abbrev driverClient.ServerStream.spec : Prop :=
  ∀ (dc conn : Loc) (addrs : List GoString) (d : GrpcConnOpts) (Up : Nat → (strmT (GF := GF)).M → IProp GF)
    (Spec : GoString → GrpcMd → StreamSpec (strmT (GF := GF)))
    (ctx : GoInterfaceOk) (cd : _root_.Perennial.context.ContextDesc (IProp GF)) (om : GrpcMd) (inp : Loc) (v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc ∗
      structFieldRef driverClient go!"cc" dc ↦□
        (interface.mkOk (go.GoType.PointerType google_golang_org.grpc.ClientConn.ty) #conn : GoInterface) ∗
      grpcConn conn addrs [] [] anyRes ∗ grpcConnOpts conn d ∗ ⌜d.streamIc = none⌝ ∗
      isGrpcStreamsMd (Req := (strmT (GF := GF)))
        (Rep := (strmT (GF := GF))) addrs go!"/grpcdriver.Driver/ServerStream"
        (fun _ => Up) Spec ∗
      ctxOk ctx cd ∗ metadata.outMD ctx om ∗
      stringValueSend inp v ∗ Up 0 v }}
    (App (App (App (Val (dc @!! go.GoType.PointerType driverClient.ty @!! go!"ServerStream"))
      (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #slice.nil))
  {{ (cs err : GoInterface), RET (PairV #cs #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (γ : StreamNames)
          (Dn : GoString → GrpcMd → Nat → (strmT (GF := GF)).M → IProp GF)
          (cd' : _root_.Perennial.context.ContextDesc (IProp GF)),
        cliBidiStreamIs cs γ (strmT (GF := GF))
          (strmT (GF := GF)) Up
          (fun a md => iprop(⌜a ∈ addrs⌝ ∗ streamAttemptMd conn (fun om om' => om' = om) om md)) Dn
          cd' anyRes (streamErrShape d) ∗
        upLb (Req := (strmT (GF := GF))) γ [v] ∗
        upClosed (Req := (strmT (GF := GF))) γ [v] ∗
        cliRecvTok (Rep := (strmT (GF := GF))) γ [] ∗
        □ (∀ a md, ⌜a ∈ addrs⌝ -∗ streamAttemptMd conn (fun om om' => om' = om) om md -∗
          Spec a md γ (Dn a md))) ∨
      (⌜cs = GoInterface.nil⌝ ∗ cliStreamErr err (streamErrShape d)) }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc
end Perennial
