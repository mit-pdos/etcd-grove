/-
`clientv3.toLeaseTimeToLiveRequest(id, opts...)` (`client/v3/op.go`; the closed lease example, `notes/lease-ex-plan.md`). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.toLeaseTimeToLiveRequest
public import Spec.go_etcd_io.etcd.client.v3.LeaseOp__applyOpts

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

theorem toLeaseTimeToLiveRequest.wp_proof
    (wp_applyOpts : LeaseOp.applyOpts.spec (GF := GF) (hG := hG)) :
    toLeaseTimeToLiveRequest.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
