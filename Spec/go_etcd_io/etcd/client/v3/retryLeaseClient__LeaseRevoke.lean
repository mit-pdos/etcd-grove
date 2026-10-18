/-
`(*clientv3.retryLeaseClient).LeaseRevoke(ctx, in, opts...)` (`client/v3/retry.go`; item 1, the
client lease). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLease

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

/-- `rlc.LeaseRevoke(ctx, in, opts...)` (as `retryLeaseClient.LeaseGrant`): the call's answer
(`leaseRevokeCallOut`). -/
abbrev retryLeaseClient.LeaseRevoke.spec : Prop :=
  ∀ (rlc conn : Loc) (addr : GoString)
    (Spec : GrpcSpec (GF := GF) pbLeaseRevokeRequest pbLeaseRevokeResponse)
    (Q : LeaseRevokeRespM → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (inp : Loc) (req : etcdserverpb.LeaseRevokeRequest) (opts : GoSlice) (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryLeaseAt rlc conn ∗
      isEtcdConn conn addr ∗ isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseRevoke" Spec ∗
      □ ▷ Spec req.ID' Q ∗ ctxOk ctx cd ∗ inp ↦ req ∗
      opts ↦*□ vs ∗ ⌜opts.len = opts.cap⌝ ∗ callOptsOk vs }}
    (App (App (App (Val (rlc @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.retryLeaseClient.ty @!!
        go!"LeaseRevoke")) (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (∃ req' : etcdserverpb.LeaseRevokeRequest, inp ↦ req') ∗ leaseRevokeCallOut Q resp err }}

end spec

end EtcdGrove
end Perennial
