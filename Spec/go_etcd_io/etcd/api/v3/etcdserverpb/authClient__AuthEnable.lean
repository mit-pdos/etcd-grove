/-
`(*etcdserverpb.authClient).AuthEnable(ctx, in, opts...)` (`api/etcdserverpb/rpc_grpc.pb.go`, the generated
Auth stub; translated for the auth plan's E2h). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvAuthConn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.AuthEnable(ctx, in, opts...)` on a stub on a connection to the server at `addr` (`authStubAt`),
for a spec `Spec` the server registered for the method and the caller's persistent `□ ▷ Spec m Φ`:
`Invoke` of `"/etcdserverpb.Auth/AuthEnable"` with `grpc.StaticMethod()` before the options, into a new
response: the call's answer (`authCallOut`, the run's `Φ`); the request comes back. -/
abbrev etcdserverpb.authClient.AuthEnable.spec : Prop :=
  ∀ (ac conn : Loc) (addr : List GoString)
    (Spec : GrpcSpec (GF := GF) pbAuthEnableRequest pbAuthEnableResponse) (Φ : Unit → IProp GF) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (inp : Loc) (m : (pbAuthEnableRequest (GF := GF)).M)
    (opts : GoSlice) (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ authStubAt ac conn ∗
      isEtcdConn conn addr ∗ isGrpcRpcs addr go!"/etcdserverpb.Auth/AuthEnable" Spec ∗ □ ▷ Spec m Φ ∗ ctxOk ctx cd ∗
      (pbAuthEnableRequest (GF := GF)).send inp m ∗ opts ↦*□ vs ∗ callOptsOk vs }}
    (App (App (App (Val (ac @!! go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.authClient.ty @!! go!"AuthEnable"))
      (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (pbAuthEnableRequest (GF := GF)).send inp m ∗ authCallOut Φ resp err }}

end spec

end EtcdGrove
end Perennial
