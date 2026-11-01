/-
Proof of `Spec/go_etcd_io/etcd/client/v3/retryKVClient__Compact.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.retryKVClient__Compact
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.kVClient__Compact

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

theorem retryKVClient.Compact.wp_proof (wp_kVClient_Compact : kVClient.Compact.spec (GF := GF) (hG := hG)) :
    retryKVClient.Compact.spec (GF := GF) (hG := hG) := by
  intro rkv conn addr Spec Q ctx cd inp req opts vs
  wp_start as ⟨#Hrkv, #Hconn, #Hrpc, Hpre, #Hctx, Hin, #Hopts, #Hok, %Hsz⟩
  iunfold retryKVAt at Hrkv
  icases Hrkv with ⟨%kc, #Hkc, #Hstub⟩
  wp_auto
  wp_apply wp_kVClient_Compact kc conn addr Spec Q ctx cd inp req opts vs $$ [Hin Hpre] as %resp %err Hres
  · iframe #
    iframe
    try (ipureintro; exact Hsz)
  iapply HΦ
  iexact Hres

end proof

end EtcdGrove
end Perennial
