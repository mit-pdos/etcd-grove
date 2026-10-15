/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/txWriteBuffer__put.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.txWriteBuffer__put
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.txWriteBuffer__putInternal

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem backend.txWriteBuffer.put.wp_proof
    (hPutInternal : backend.txWriteBuffer.putInternal.spec (GF := GF) (hG := hG)) :
    backend.txWriteBuffer.put.spec (GF := GF) (hG := hG) := by
  intro txw W b bi k v kb vb Hlen
  wp_start as ⟨HW, #Hb, #Hk, #Hv⟩
  unfold ownWB
  icases HW with ⟨%m, %s, Hbk, Hseq, Hbks, Hs⟩
  ihave #Hb' := Hb
  iunfold isBucket at Hb
  icases Hb with ⟨%bo, %Hbo, #HID, #-, #-⟩
  subst Hbo
  wp_auto
  wp_apply HID
  wp_apply wp_mapInsert $$ Hs as Hs
  wp_apply (hPutInternal txw { W with seq := W.seq.insert bi.id false } _ bi k v kb vb Hlen)
    $$ [Hbk Hseq Hbks Hs] as HW
  · iframe Hb' Hk Hv
    unfold ownWB
    iexists m, s
    iframe
  unfold ownWB
  simp only [WBuf.put]
  iapply HΦ $$ HW

end proof

end EtcdGrove
end Perennial
