/-
`(*clientv3.retryLeaseClient).LeaseGrant(ctx, in, opts...)` (`client/v3/retry.go`; item 1, the
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `rlc.LeaseGrant(ctx, in, opts...)` on a `*retryLeaseClient` over a stub on a connection to
`addr`: `rlc.lc.LeaseGrant(ctx, in, append(opts, withRepeatablePolicy())...)` (the options' slice
full, `len = cap`: the `append` reallocates): the call's answer (`leaseGrantCallOut`). -/
abbrev retryLeaseClient.LeaseGrant.spec : Prop :=
  ∀ (rlc conn : Loc) (addr : List GoString)
    (Spec : GrpcSpec (GF := GF) pbLeaseGrantRequest pbLeaseGrantResponse)
    (Q : LeaseGrantRespM → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (inp : Loc) (req : etcdserverpb.LeaseGrantRequest) (opts : GoSlice) (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryLeaseAt rlc conn ∗
      isEtcdConn conn addr ∗ isGrpcRpcs addr go!"/etcdserverpb.Lease/LeaseGrant" Spec ∗
      □ ▷ Spec (req.TTL', req.ID') Q ∗ ctxOk ctx cd ∗ inp ↦ req ∗
      opts ↦*□ vs ∗ ⌜opts.len = opts.cap⌝ ∗ callOptsOk vs ∗
      ⌜req.unknownFields' = slice.nil⌝ }}
    (App (App (App (Val (rlc @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.retryLeaseClient.ty @!!
        go!"LeaseGrant")) (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (∃ req' : etcdserverpb.LeaseGrantRequest, inp ↦ req') ∗ leaseGrantCallOut Q resp err }}

end spec

end EtcdGrove
end Perennial
