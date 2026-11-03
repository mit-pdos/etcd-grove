/-
`(*etcdserverpb.authClient).RoleGrantPermission(ctx, in, opts...)` (`api/etcdserverpb/rpc_grpc.pb.go`, the generated
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.RoleGrantPermission(ctx, in, opts...)` on a stub on a connection to the server at `addr` (`authStubAt`),
for a metadata-indexed spec `Spec` the server registered for the method (since the auth-mode
merge's 5b, 2026-10-29) and the caller's persistent `Φ` at every metadata an attempt may deliver
(`□ ▷ attemptPre`):
`Invoke` of `"/etcdserverpb.Auth/RoleGrantPermission"` with `grpc.StaticMethod()` before the options, into a new
response: the call's answer (`authCallOut`, the run's `Φ`); the request comes back. Its
encoding is below `grpcMsgMax` (2026-10-30: grpc marshals before it checks a size,
`grpcInvokerOk`). -/
abbrev etcdserverpb.authClient.RoleGrantPermission.spec : Prop :=
  ∀ (ac conn : Loc) (addr : List GoString)
    (Spec : GrpcSpecMd (GF := GF) pbAuthRoleGrantPermissionRequest pbAuthRoleGrantPermissionResponse) (Φ : Unit → IProp GF) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (inp : Loc) (m : (pbAuthRoleGrantPermissionRequest (GF := GF)).M)
    (opts : GoSlice) (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ authStubAt ac conn ∗
      isEtcdConn conn addr ∗ isGrpcRpcsMd addr go!"/etcdserverpb.Auth/RoleGrantPermission" Spec ∗
      □ ▷ attemptPre conn (GoInterface.ok ctx) Spec m Φ ∗ ctxOk ctx cd ∗
      (pbAuthRoleGrantPermissionRequest (GF := GF)).send inp m ∗ opts ↦*□ vs ∗ callOptsOk vs ∗
      ⌜(pbAuthRoleGrantPermissionRequest (GF := GF)).wireLen m < grpcMsgMax⌝ }}
    (App (App (App (Val (ac @!! go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.authClient.ty @!! go!"RoleGrantPermission"))
      (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (pbAuthRoleGrantPermissionRequest (GF := GF)).send inp m ∗ authCallOut Φ resp err }}

end spec

end EtcdGrove
end Perennial
