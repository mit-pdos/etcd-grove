/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__startBufWait.lean` (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__startBufWait
public import Spec.time.Time__IsZero

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem watchGRPCStream.startBufWait.wp_proof
    (wp_IsZero : time.Time.IsZero.spec (GF := GF) (hG := hG)) :
    watchGRPCStream.startBufWait.spec (GF := GF) (hG := hG) := by
  intro wgs ws lg bl dq t
  wp_start as ⟨#Hlg, Hbl, Hok, Ht⟩
  ihave #Ptime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  wp_auto
  wp_if_destruct
  · iapply HΦ; iframe
  · iunfold bufLogOk at Hok
    icases Hok with (%Hbn | Hbl')
    · subst Hbn
      wp_auto
      iapply HΦ; iframe
    · iunfold isBlockLogger at Hbl'
      icases Hbl' with ⟨%nowf, %lf, %iv, %th, %Hnn, -, -, #Hnow, -, #Hnowf, -, -⟩
      rw [decide_eq_false Hnn]
      wp_auto
      wp_apply wp_IsZero $$ [$Ptime $Ht] as %bz Ht
      cases bz
      · wp_auto
        iapply HΦ; iframe
      · wp_auto
        wp_apply Hnowf as %tn
        iapply HΦ; iframe

end proof

end EtcdGrove
end Perennial
