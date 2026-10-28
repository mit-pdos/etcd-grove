/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/_Auth_RoleGrantPermission_Handler.lean` (the auth plan's E3za). Lean-first
(no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb._Auth_RoleGrantPermission_Handler
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.UnaryHandlerLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- The generated handler of `Auth.RoleGrantPermission`: decode a `*AuthRoleGrantPermissionRequest`, call `srv.RoleGrantPermission` (directly or
through the interceptor chain, with `info.FullMethod = "/etcdserverpb.Auth/RoleGrantPermission"`), as every
generated unary handler (`wp_unaryHandlerOwn`; the build checks that this handler's body is
`unaryHandlerImpl` at these arguments). -/
theorem etcdserverpb._Auth_RoleGrantPermission_Handler.wp_proof :
    etcdserverpb._Auth_RoleGrantPermission_Handler.spec (GF := GF) (hG := hG) :=
  wp_unaryHandlerOwn etcdserverpb._Auth_RoleGrantPermission_Handler etcdserverpb.AuthServer.ty
    etcdserverpb.AuthRoleGrantPermissionRequest.ty etcdserverpb.AuthRoleGrantPermissionResponse.ty go!"RoleGrantPermission" go!"/etcdserverpb.Auth/RoleGrantPermission"

end proof

end EtcdGrove
end Perennial
