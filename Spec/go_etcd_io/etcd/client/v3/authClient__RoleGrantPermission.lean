/-
`(*clientv3.authClient).RoleGrantPermission` (`client/v3/auth.go`; translated for the auth plan's E2h). Lean-first
(no Rocq counterpart).
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

/-- `auth.RoleGrantPermission(ctx, ...)` on the client's `*authClient` over a connection to `addr`
(`authObjAt`): `auth.remote.RoleGrantPermission(ctx, &pb.AuthRoleGrantPermissionRequest{Name: name, Perm:
perm}, auth.callOpts...)` of a new permission `perm` holding `permType`, `[]byte(key)` and
`[]byte(rangeEnd)` (a key shorter than a slice's bound, as the auth store's permission predicate
records, `auth.ownPermW`), the error through `ContextError`: the call's answer (`authCallOut`), for
a spec `Spec` the server registered for the method and the caller's persistent
`□ ▷ Spec m Q` at the request's model `m`. -/
abbrev authClient.RoleGrantPermission.spec : Prop :=
  ∀ (api : Loc) (addr : List GoString) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (name key rangeEnd : GoString) (permType : w32)
    (Spec : GrpcSpec (GF := GF) pbAuthRoleGrantPermissionRequest pbAuthRoleGrantPermissionResponse) (Q : Unit → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ authObjAt api addr ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ ⌜key.length < 2 ^ 63 - 1⌝ ∗ isGrpcRpcs addr go!"/etcdserverpb.Auth/RoleGrantPermission" Spec ∗
      □ ▷ Spec (name, (⟨permType, key, rangeEnd⟩ : auth.PermW)) Q }}
    (App (App (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.authClient.ty @!! go!"RoleGrantPermission")) (Val #(GoInterface.ok ci))) (Val #name)) (Val #key)) (Val #rangeEnd)) (Val #permType))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); authCallOut Q resp err }}

end spec

end EtcdGrove
end Perennial
