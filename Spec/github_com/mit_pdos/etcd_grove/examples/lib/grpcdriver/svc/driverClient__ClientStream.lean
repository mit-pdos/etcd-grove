/- Lean-first (no Rocq counterpart).

`(*driverClient).ClientStream(ctx)` (svc.go, no call options): a stream of the driver's
`ClientStream` on the stub's connection (no stream interceptor): on success, the wrapped client end
(`cliBidiStreamIs`) with its `CloseAndRecv` (`carOk`), both tokens at `[]` and the stream's
specification; otherwise the error (`cliStreamErr`, of grpc's own shape).
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
abbrev driverClient.ClientStream.spec : Prop :=
  ∀ (dc conn : Loc) (addrs : List GoString) (d : GrpcConnOpts) (Up : Nat → (pbStringValueST (GF := GF)).M → IProp GF)
    (Spec : GoString → GrpcMd → StreamSpec (pbStringValueST (GF := GF)).toStreamMsg)
    (ctx : GoInterfaceOk) (cd : _root_.Perennial.context.ContextDesc (IProp GF)) (om : GrpcMd),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc ∗
      structFieldRef driverClient go!"cc" dc ↦□
        (interface.mkOk (go.GoType.PointerType google_golang_org.grpc.ClientConn.ty) #conn : GoInterface) ∗
      grpcConn conn addrs [] [] anyRes ∗ grpcConnOpts conn d ∗ ⌜d.streamIc = none⌝ ∗
      isGrpcStreamsMd (Req := (pbStringValueST (GF := GF)).toStreamMsg)
        (Rep := (pbStringValueST (GF := GF)).toStreamMsg) addrs go!"/grpcdriver.Driver/ClientStream"
        (fun _ => Up) Spec ∗
      ctxOk ctx cd ∗ metadata.outMD ctx om }}
    (App (App (Val (dc @!! go.GoType.PointerType driverClient.ty @!! go!"ClientStream"))
      (Val #(GoInterface.ok ctx))) (Val #slice.nil))
  {{ (cs err : GoInterface), RET (PairV #cs #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (γ : StreamNames)
          (Dn : GoString → GrpcMd → Nat → (pbStringValueST (GF := GF)).M → IProp GF)
          (cd' : _root_.Perennial.context.ContextDesc (IProp GF)),
        cliBidiStreamIs cs γ (pbStringValueST (GF := GF)).toStreamMsg
          (pbStringValueST (GF := GF)).toStreamMsg Up
          (fun a md => iprop(⌜a ∈ addrs⌝ ∗ streamAttemptMd conn (fun om om' => om' = om) om md)) Dn
          cd' anyRes (streamErrShape d) ∗
        carOk (Req := (pbStringValueST (GF := GF)).toStreamMsg)
          (Rep := (pbStringValueST (GF := GF)).toStreamMsg) cs γ
          (fun a md => iprop(⌜a ∈ addrs⌝ ∗ streamAttemptMd conn (fun om om' => om' = om) om md)) Dn
          (streamErrShape d) ∗
        cliSendTok (Req := (pbStringValueST (GF := GF)).toStreamMsg) γ [] ∗
        cliRecvTok (Rep := (pbStringValueST (GF := GF)).toStreamMsg) γ [] ∗
        □ (∀ a md, ⌜a ∈ addrs⌝ -∗ streamAttemptMd conn (fun om om' => om' = om) om md -∗
          Spec a md γ (Dn a md))) ∨
      (⌜cs = GoInterface.nil⌝ ∗ cliStreamErr err (streamErrShape d)) }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc
end Perennial
