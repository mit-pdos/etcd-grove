/-
`(*clientv3.retryAuthClient).RoleAdd(ctx, in, opts...)` (`client/v3/retry.go`; translated for the auth
plan's E2h). Lean-first (no Rocq counterpart).
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

/-- `rac.RoleAdd(ctx, in, opts...)` on a `*retryAuthClient` over a stub on a connection to `addr`:
`rac.ac.RoleAdd(ctx, in, opts...)` (no retry option added: an admin call): the call's answer
(`authCallOut`). -/
abbrev retryAuthClient.RoleAdd.spec : Prop :=
  ∀ (rac conn : Loc) (addr : List GoString)
    (Spec : GrpcSpec (GF := GF) pbAuthRoleAddRequest pbAuthRoleAddResponse) (Φ : Unit → IProp GF) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (inp : Loc) (m : (pbAuthRoleAddRequest (GF := GF)).M)
    (opts : GoSlice) (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryAuthAt rac conn ∗
      isEtcdConn conn addr ∗ isGrpcRpcs addr go!"/etcdserverpb.Auth/RoleAdd" Spec ∗ □ ▷ Spec m Φ ∗ ctxOk ctx cd ∗
      (pbAuthRoleAddRequest (GF := GF)).send inp m ∗ opts ↦*□ vs ∗ callOptsOk vs }}
    (App (App (App (Val (rac @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.retryAuthClient.ty @!!
        go!"RoleAdd")) (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (pbAuthRoleAddRequest (GF := GF)).send inp m ∗ authCallOut Φ resp err }}

end spec

end EtcdGrove
end Perennial
