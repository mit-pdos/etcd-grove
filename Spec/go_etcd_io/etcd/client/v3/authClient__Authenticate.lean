/-
`(*clientv3.authClient).Authenticate` (`client/v3/auth.go`; the auth plan's C1, 2026-10-28, `getToken`'s
call). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientAuth

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

/-- `auth.Authenticate(ctx, name, password)` on the client's `*authClient` over a connection to
`addr` (`authObjAt`): `auth.remote.Authenticate(ctx, &pb.AuthenticateRequest{Name: name, Password:
password}, auth.callOpts...)`, the error through `ContextError`: the call's answer (`authnCallOut`:
the reply's token `t` with `Q t`), for a spec `Spec` the server registered for the method and the
caller's persistent `□ ▷ Spec (name, password) Q`. -/
abbrev authClient.Authenticate.spec : Prop :=
  ∀ (api : Loc) (addr : List GoString) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (name pw : GoString)
    (Spec : GrpcSpec (GF := GF) pbAuthenticateRequest pbAuthenticateResponse)
    (Q : GoString → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ authObjAt api addr ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ isGrpcRpcs addr authnMethod Spec ∗
      □ ▷ Spec (name, pw) Q }}
    (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.authClient.ty @!!
      go!"Authenticate")) (Val #(GoInterface.ok ci))) (Val #name)) (Val #pw))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); authnCallOut Q resp err }}

end spec

end EtcdGrove
end Perennial
