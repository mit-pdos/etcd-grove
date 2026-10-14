/-
Proof of `Spec/go_etcd_io/etcd/client/v3/retryKVClient__Put.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.retryKVClient__Put
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.kVClient__Put

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

theorem retryKVClient.Put.wp_proof (wp_kVClient_Put : kVClient.Put.spec (GF := GF) (hG := hG)) :
    retryKVClient.Put.spec (GF := GF) (hG := hG) := by
  intro rkv conn K ctx cd inp req k v opts vs Q
  wp_start as ⟨#Hrkv, #Hconn, #Hctx, Hin, #Hk, #Hv, #Hopts, #Hok, #Hrun⟩
  iunfold retryKVAt at Hrkv
  icases Hrkv with ⟨%kc, #Hkc, #Hstub⟩
  wp_auto
  wp_apply wp_kVClient_Put kc conn K ctx cd inp req k v opts vs Q $$ [Hin] as %resp %err Hres
  · iframe #
    iframe
  iapply HΦ
  iexact Hres

end proof

end EtcdGrove
end Perennial
