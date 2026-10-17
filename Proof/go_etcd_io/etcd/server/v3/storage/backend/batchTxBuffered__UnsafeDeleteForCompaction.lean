/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTxBuffered__UnsafeDeleteForCompaction.lean`
(etcd#21982): `t.batchTx.UnsafeDeleteForCompaction(bucketType, key)`, and, unlike `UnsafeDelete`,
no `pendingDeleteOperations++`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeDeleteForCompaction
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__UnsafeDeleteForCompaction

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend go_uber_org

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [go_etcd_io.bbolt.Assumptions] [go_uber_org.zap.Assumptions]

theorem backend.batchTxBuffered.UnsafeDeleteForCompaction.wp_proof
    (hBT : backend.batchTx.UnsafeDeleteForCompaction.spec (GF := GF) (hG := hG)) :
    backend.batchTxBuffered.UnsafeDeleteForCompaction.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b t st bk bi key kb dk Hhas Hp Hhb Hhk
  wp_start as ⟨#Hb, #Ht, Hl, #Hbk, Hkey⟩
  icases isBackend_bt γ P W Pk b t $$ [Hb Ht] with
    ⟨%db0, %lg, %h, #Hbe, #Hlg, %Hlgn, #Hlim, #Hh, #Hhs, #Hm, #Hdb, %HP⟩
  · iframe #
  unfold batchLocked batchLockedAt batchPhys
  icases Hl with ⟨%t', %db, #Ht', Hown, ⟨%hk, Htxf, Hpend, Hdel, HW, Hhkf, Hhk, Hdb', Hwtx, #Htxdb, Hmu⟩,
    Hg, %Hwf⟩
  icombine Ht Ht' gives %Heq
  subst Heq
  wp_auto
  wp_apply (hBT γ P W Pk b t st bk bi key kb dk) $$ [Htxf Hpend Hwtx $Hkey] as ⟨Hw, Hkey⟩
  · iframe #
    unfold btW
    iframe
  unfold btW
  icases Hw with ⟨Htxf, Hpend, Hwtx⟩
  iapply HΦ
  iframe Hkey
  iexists t, db
  iframe Ht' Hown
  ihave Hg := batchGhost_step γ P (st := st) (st' := (st.delC bi kb)) rfl rfl rfl
    (pend_succ_nat Hwf Hp) (fun i => by simp [BSess.delC])
    (hkData_delC st bi kb Hhk) $$ Hg
  iframe Hg
  isplitl
  · iexists hk
    simp only [BSess.del, BSess.delC]
    iframe
    iframe #
  · ipureintro
    exact sessWf_delC HP Hwf Hp Hhb

end proof

end EtcdGrove
end Perennial
