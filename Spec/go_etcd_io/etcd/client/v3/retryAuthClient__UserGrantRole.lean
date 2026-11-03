/-
`(*clientv3.retryAuthClient).UserGrantRole(ctx, in, opts...)` (`client/v3/retry.go`; translated for the auth
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `rac.UserGrantRole(ctx, in, opts...)` on a `*retryAuthClient` over a stub on a connection to `addr`:
`rac.ac.UserGrantRole(ctx, in, opts...)` (no retry option added: an admin call): the call's answer
(`authCallOut`). -/
abbrev retryAuthClient.UserGrantRole.spec : Prop :=
  ∀ (rac conn : Loc) (addr : List GoString)
    (Spec : GrpcSpecMd (GF := GF) pbAuthUserGrantRoleRequest pbAuthUserGrantRoleResponse) (Φ : Unit → IProp GF) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (inp : Loc) (m : (pbAuthUserGrantRoleRequest (GF := GF)).M)
    (opts : GoSlice) (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryAuthAt rac conn ∗
      isEtcdConn conn addr ∗ isGrpcRpcsMd addr go!"/etcdserverpb.Auth/UserGrantRole" Spec ∗ □ ▷ attemptPre conn (GoInterface.ok ctx) Spec m Φ ∗ ctxOk ctx cd ∗
      (pbAuthUserGrantRoleRequest (GF := GF)).send inp m ∗ opts ↦*□ vs ∗ callOptsOk vs ∗
      ⌜(pbAuthUserGrantRoleRequest (GF := GF)).wireLen m < grpcMsgMax⌝ }}
    (App (App (App (Val (rac @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.retryAuthClient.ty @!!
        go!"UserGrantRole")) (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (pbAuthUserGrantRoleRequest (GF := GF)).send inp m ∗ authCallOut Φ resp err }}

end spec

end EtcdGrove
end Perennial
