/-
Proof of `Spec/go_etcd_io/etcd/client/v3/retryKVClient__DeleteRange.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.retryKVClient__DeleteRange
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.kVClient__DeleteRange

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

theorem retryKVClient.DeleteRange.wp_proof (wp_kVClient_DeleteRange : kVClient.DeleteRange.spec (GF := GF) (hG := hG)) :
    retryKVClient.DeleteRange.spec (GF := GF) (hG := hG) := by
  intro rkv conn addr Spec Q ctx cd inp req k e opts vs
  wp_start as ⟨#Hrkv, #Hconn, #Hrpc, Hpre, #Hctx, Hin, #Hk, #He, #Hopts, #Hok, %Hsz⟩
  iunfold retryKVAt at Hrkv
  icases Hrkv with ⟨%kc, #Hkc, #Hstub⟩
  wp_auto
  wp_apply wp_kVClient_DeleteRange kc conn addr Spec Q ctx cd inp req k e opts vs $$ [Hin Hpre] as %resp %err Hres
  · iframe #
    iframe
    try (ipureintro; exact Hsz)
  iapply HΦ
  iexact Hres

end proof

end EtcdGrove
end Perennial
