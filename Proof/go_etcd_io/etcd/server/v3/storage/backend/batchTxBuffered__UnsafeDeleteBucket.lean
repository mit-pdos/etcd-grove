/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTxBuffered__UnsafeDeleteBucket.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeDeleteBucket
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__UnsafeDeleteBucket

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend go_uber_org

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [go_etcd_io.bbolt.Assumptions] [go_uber_org.zap.Assumptions]

theorem backend.batchTxBuffered.UnsafeDeleteBucket.wp_proof
    (hBT : backend.batchTx.UnsafeDeleteBucket.spec (GF := GF) (hG := hG)) :
    backend.batchTxBuffered.UnsafeDeleteBucket.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b t st bk bi Hhas Hne Hp Hsb Hhk Hfk c k Hkc
  wp_start as ⟨#Hb, #Ht, Hl, #Hbk, Hrbp⟩
  icases isBackend_bt γ P W Pk b t $$ [Hb Ht] with
    ⟨%db0, %lg, %h, #Hbe, #Hlg, #Hlgn, #Hlim, #Hh, #Hhs, #Hm, #Hdb, %HP⟩
  · iframe #
  unfold batchLocked batchLockedAt batchPhys
  icases Hl with ⟨%t', %db, #Ht', Hown, ⟨%hk, Htxf, Hpend, Hdel, HW, Hhkf, Hhk, Hdb', Hwtx, #Htxdb, Hmu⟩,
    Hg, %Hwf⟩
  icombine Ht Ht' gives %Heq
  subst Heq
  wp_auto
  icases batchGhostAt_bufRc γ P st false c $$ Hg with ⟨Hg, #Hbr⟩
  ihave #Hbr' := bufRc_congr (st := st) (st' := (st.delBucket bi k)) rfl rfl $$ Hbr
  imod batchGhost_step_rb γ P (st := st) (st' := (st.delBucket bi k)) rfl rfl rfl
    (pend_succ_nat Hwf Hp) (fun i => by simp [BSess.del, BSess.create, BSess.delBucket])
    bi.name (hkData_delBucket st bi Hhk)
    (rbData_delBucket_other st bi) (fkOkG_delBucket Hfk) (fkVals_delBucket Hfk) (fun _ => ⟨bi.id, Hhas⟩)
    (BSess.delBucket_S_other st bi) rfl (trkOk_delBucketS Hwf bi) (fun L _ hd => dlsW_step (dlsS_delBucket Hsb) (dlsOk_delBucket Hsb) rfl rfl hd)
    (fun m hm => tkSet_ne _ _ hm)
    k c (fun m hm => by cases k <;> simp [BSess.delBucket, cwAdd, hm]) (fun h => by subst h; rfl)
    (fun h _ => by subst h; right; simp [BSess.delBucket, cwAdd]) (fun h => by subst h; revert Hkc; cases c <;> decide) $$ Hbr' Hg Hrbp
    with ⟨Hg, Hrbp⟩
  wp_apply (hBT γ P W Pk b t st bk bi Hne) $$ [Htxf Hpend Hwtx] as Hw
  · iframe #
    unfold btW
    iframe
  unfold btW
  icases Hw with ⟨Htxf, Hpend, Hwtx⟩
  iapply HΦ
  iframe Hrbp
  iexists t, db
  iframe Ht' Hown
  iframe Hg
  isplitl
  · iexists hk
    simp only [BSess.put, BSess.del, BSess.create, BSess.delBucket]
    iframe
    iframe #
  · ipureintro
    exact sessWf_delBucket Hwf Hp Hsb

end proof

end EtcdGrove
end Perennial
