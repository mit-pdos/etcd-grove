/-
Proof of `Spec/go_etcd_io/etcd/client/v3/retryKVClient__Txn.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.retryKVClient__Txn
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.kVClient__Txn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem retryKVClient.Txn.wp_proof (wp_kVClient_Txn : kVClient.Txn.spec (GF := GF) (hG := hG)) :
    retryKVClient.Txn.spec (GF := GF) (hG := hG) := by
  intro rkv conn addr Spec Q ctx cd inp req t opts vs
  wp_start as ⟨#Hrkv, #Hconn, #Hrpc, #Hpre, #Hctx, Hin, #Ht, #Hopts, #Hok⟩
  iunfold retryKVAt at Hrkv
  icases Hrkv with ⟨%kc, #Hkc, #Hstub⟩
  wp_auto
  wp_apply wp_kVClient_Txn kc conn addr Spec Q ctx cd inp req t opts vs $$ [Hin] as %resp %err Hres
  · iframe #
    iframe
  iapply HΦ
  iexact Hres

end proof

end EtcdGrove
end Perennial
