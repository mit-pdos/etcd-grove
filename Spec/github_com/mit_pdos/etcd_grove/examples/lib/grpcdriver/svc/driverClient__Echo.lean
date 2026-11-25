/- Lean-first (no Rocq counterpart).

`(*driverClient).Echo(ctx, in, opts...)` (svc.go): `unary` of `Echo`'s full name.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.PlainInvoke

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.Assumptions]
variable [pkg_wr : google_golang_org.protobuf.types.known.wrapperspb.Assumptions]

/-- See the file header. -/
abbrev driverClient.Echo.spec : Prop :=
  ∀ (dc conn : Loc) (addrs : List GoString) (Spec : GrpcSpecMd (GF := GF)
      (pbStringValueT (GF := GF)).toProtoMsg (pbStringValueRT (GF := GF)).toProtoMsg)
    (m : GoString) (Φ : GoString → IProp GF) (Ψe : GoString → IProp GF) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (om : GrpcMd) (inp : Loc) (opts : GoSlice)
    (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc ∗
      structFieldRef svc.driverClient go!"cc" dc ↦□
        (interface.mkOk (go.GoType.PointerType google_golang_org.grpc.ClientConn.ty) #conn : GoInterface) ∗
      grpcConn conn addrs [] [] anyRes ∗
      isGrpcRpcsMd (Req := (pbStringValueT (GF := GF)).toProtoMsg)
        (Rep := (pbStringValueRT (GF := GF)).toProtoMsg) addrs echoName Spec ∗
      metadata.outMD ctx om ∗ ▷ (∀ md, grpcAttemptMd conn om md -∗ Spec md m Φ Ψe) ∗ ctxOk ctx cd ∗
      (pbStringValueT (GF := GF)).send inp m ∗ opts ↦*□ vs ∗ ⌜∀ v ∈ vs, grpcOptOk [] v⌝ }}
    (App (App (App (Val (dc @!! go.GoType.PointerType svc.driverClient.ty @!! go!"Echo"))
      (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); ∃ out : Loc,
      invokeOut echoName addrs (pbStringValueRT (GF := GF)) out Φ Ψe err ∗
      ⌜err = GoInterface.nil → resp = out⌝ }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc
end Perennial
