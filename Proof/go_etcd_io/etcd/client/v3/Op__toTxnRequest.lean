/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Op__toTxnRequest.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Op__toTxnRequest
public import Spec.go_etcd_io.etcd.client.v3.Op__toRequestOp
public import Spec.go_etcd_io.etcd.client.v3.Cmp__Clone
public import Spec.go_etcd_io.etcd.client.v3.Cmp__GetCompare
public import Proof.go_etcd_io.etcd.client.v3.OpTxnRequest

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

theorem Op.toTxnRequest.wp_proof (wp_toRequestOp : Op.toRequestOp.spec (GF := GF) (hG := hG))
    (wp_Clone : Cmp.Clone.spec (GF := GF) (hG := hG))
    (wp_GetCompare : Cmp.GetCompare.spec (GF := GF) (hG := hG)) :
    Op.toTxnRequest.spec (GF := GF) (hG := hG) := by
  intro opv o cs ts es
  exact toTxnRequest_core wp_Clone wp_GetCompare opv o cs ts es
    (fun t _ v => wp_toRequestOp v t)

end proof

end EtcdGrove
end Perennial
