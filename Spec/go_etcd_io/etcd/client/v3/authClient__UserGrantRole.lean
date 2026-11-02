/-
`(*clientv3.authClient).UserGrantRole` (`client/v3/auth.go`; translated for the auth plan's E2h). Lean-first
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

/-- `auth.UserGrantRole(ctx, ...)` on the client's `*authClient` over a connection to `addr`
(`authObjAtC`): `auth.remote.UserGrantRole(ctx, &pb.AuthUserGrantRoleRequest{User: user, Role: role},
auth.callOpts...)`, the error through `ContextError`: the call's answer (`authCallOut`), for
a spec `Spec` the server registered for the method and the caller's persistent
`□ ▷ attemptPre conn (GoInterface.ok ci) Spec m Q` at the request's model `m`. The strings it sends total at most `2 ^ 30`
bytes (`strsSizeOk`; 2026-10-30: the request's encoding is below `grpcMsgMax`). -/
abbrev authClient.UserGrantRole.spec : Prop :=
  ∀ (api conn : Loc) (addr : List GoString) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (user role : GoString)
    (Spec : GrpcSpecMd (GF := GF) pbAuthUserGrantRoleRequest pbAuthUserGrantRoleResponse) (Q : Unit → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ authObjAtC api conn addr ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ isGrpcRpcsMd addr go!"/etcdserverpb.Auth/UserGrantRole" Spec ∗
      □ ▷ attemptPre conn (GoInterface.ok ci) Spec (user, role) Q ∗
      ⌜strsSizeOk [user, role]⌝ }}
    (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.authClient.ty @!! go!"UserGrantRole")) (Val #(GoInterface.ok ci))) (Val #user)) (Val #role))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); authCallOut Q resp err }}

end spec

end EtcdGrove
end Perennial
