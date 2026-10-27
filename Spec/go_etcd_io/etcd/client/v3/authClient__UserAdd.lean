/-
`(*clientv3.authClient).UserAdd` (`client/v3/auth.go`; translated for the auth plan's E2h). Lean-first
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

/-- `auth.UserAdd(ctx, ...)` on the client's `*authClient` over a connection to `addr`
(`authObjAt`): `auth.remote.UserAdd(ctx, &pb.AuthUserAddRequest{Name: name, Password: password, Options:
&authpb.UserAddOptions{NoPassword: false}}, auth.callOpts...)`, the error through `ContextError`: the call's answer (`authCallOut`), for
a spec `Spec` the server registered for the method and the caller's persistent
`□ ▷ Spec m Q` at the request's model `m`. -/
abbrev authClient.UserAdd.spec : Prop :=
  ∀ (api : Loc) (addr : List GoString) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (name pw : GoString)
    (Spec : GrpcSpec (GF := GF) pbAuthUserAddRequest pbAuthUserAddResponse) (Q : Unit → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ authObjAt api addr ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ isGrpcRpcs addr go!"/etcdserverpb.Auth/UserAdd" Spec ∗
      □ ▷ Spec (⟨name, pw⟩ : UserAddW) Q }}
    (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.authClient.ty @!! go!"UserAdd")) (Val #(GoInterface.ok ci))) (Val #name)) (Val #pw))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); authCallOut Q resp err }}

end spec

end EtcdGrove
end Perennial
