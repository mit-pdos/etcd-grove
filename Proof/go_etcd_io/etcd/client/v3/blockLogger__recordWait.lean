/-
Proof of `Spec/go_etcd_io/etcd/client/v3/blockLogger__recordWait.lean` (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.blockLogger__recordWait
public import Perennial.Proof.time
public import Perennial.Proof.sync

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

theorem blockLogger.recordWait.wp_proof :
    blockLogger.recordWait.spec (GF := GF) (hG := hG) := by
  intro α A x bl d
  wp_start as ⟨Hbl, HA⟩
  iunfold isBlockLogger at Hbl
  icases Hbl with ⟨%nowf, %lf, %iv, %th, %Hnn, #Hiv, #Hth, #Hnow, #Hlf, #Hnowf, #Hlff, #Hmu⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, ⟨%t, %n, %dw, Ht, Hn, Hd⟩⟩
  wp_apply Hnowf as %tn
  wp_apply time.Time.wp_ptr_Sub $$ [$now] as %w now
  wp_if_destruct
  · wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Ht Hn Hd]
    · iexists _, _, _; iframe
    iapply HΦ; iframe
  · wp_if_destruct
    · wp_if_destruct
      · wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Ht Hn Hd]
        · iexists _, _, _; iframe
        iapply HΦ; iframe
      · wp_bind (App (App (App (Val #lf) (Val #(n + W64 1))) (Val #(dw + d))) (Val #w))
        iapply Hlff $$ %x %(n + W64 1) %(dw + d) %w [HA]
        · iexact HA
        inext; iintro HA
        wp_auto
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Ht Hn Hd]
        · iexists _, _, _; iframe
        iapply HΦ; iframe
    · wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Ht Hn Hd]
      · iexists _, _, _; iframe
      iapply HΦ; iframe

end proof

end EtcdGrove
end Perennial
