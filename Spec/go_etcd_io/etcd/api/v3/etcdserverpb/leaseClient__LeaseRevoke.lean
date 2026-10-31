/-
`(*etcdserverpb.leaseClient).LeaseRevoke(ctx, in, opts...)` (`api/etcdserverpb/rpc_grpc.pb.go`, the
generated Lease stub; item 1, the client lease). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLease

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

/-- `c.LeaseRevoke(ctx, in, opts...)` on a stub on a connection to `addr` (as
`leaseClient.LeaseGrant`): `Invoke` of `"/etcdserverpb.Lease/LeaseRevoke"`: the call's answer
(`leaseRevokeCallOut`); the request comes back. The
request has no unknown fields (a struct literal; 2026-10-30, the wire model's bound,
`ProtoMsg.wireLen`). -/
abbrev leaseClient.LeaseRevoke.spec : Prop :=
  ∀ (lc conn : Loc) (addr : List GoString)
    (Spec : GrpcSpec (GF := GF) pbLeaseRevokeRequest pbLeaseRevokeResponse)
    (Φ : LeaseRevokeRespM → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (inp : Loc) (req : etcdserverpb.LeaseRevokeRequest) (opts : GoSlice) (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ leaseStubAt lc conn ∗
      isEtcdConn conn addr ∗ isGrpcRpcs addr go!"/etcdserverpb.Lease/LeaseRevoke" Spec ∗
      □ ▷ Spec req.ID' Φ ∗ ctxOk ctx cd ∗ inp ↦ req ∗ opts ↦*□ vs ∗ callOptsOk vs ∗
      ⌜req.unknownFields' = slice.nil⌝ }}
    (App (App (App (Val (lc @!! go.GoType.PointerType etcdserverpb.leaseClient.ty @!! go!"LeaseRevoke"))
      (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (∃ req' : etcdserverpb.LeaseRevokeRequest, inp ↦ req') ∗ leaseRevokeCallOut Φ resp err }}

end spec

end EtcdGrove
end Perennial
