/-
`(*clientv3.lessor).TimeToLive(ctx, id, opts...)` (`client/v3/lease.go`; the closed lease example, `notes/lease-ex-plan.md`). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.lessor__TimeToLive
public import Spec.go_etcd_io.etcd.client.v3.toLeaseTimeToLiveRequest
public import Spec.go_etcd_io.etcd.client.v3.retryLeaseClient__LeaseTimeToLive
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.LeaseTimeToLiveResponse__GetHeader
public import Spec.go_etcd_io.etcd.client.v3.ContextError

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
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem lessor.TimeToLive.wp_proof
    (wp_toReq : toLeaseTimeToLiveRequest.spec (GF := GF) (hG := hG))
    (wp_retry : retryLeaseClient.LeaseTimeToLive.spec (GF := GF) (hG := hG))
    (wp_GetHeader : LeaseTimeToLiveResponse.GetHeader.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    lessor.TimeToLive.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
