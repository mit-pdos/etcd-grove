/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTxBuffered__UnsafeCreateBucket.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeCreateBucket
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__UnsafeCreateBucket

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

theorem backend.batchTxBuffered.UnsafeCreateBucket.wp_proof
    (hBT : backend.batchTx.UnsafeCreateBucket.spec (GF := GF) (hG := hG)) :
    backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b t st bk bi Hhas Hn0 Hn1 Hp c k Hkc
  wp_start as ⟨#Hb, #Ht, Hl, #Hbk, Hrbp⟩
  icases isBackend_bt γ P W Pk b t $$ [Hb Ht] with
    ⟨%db0, %lg, %h, #Hbe, #Hlg, #Hlgn, #Hlim, #Hh, #Hhs, #Hm, #Hdb, %HP⟩
  · iframe #
  unfold batchLocked batchLockedAt batchPhys
  icases Hl with ⟨%t', %db, #Ht', Hown, ⟨%hk, Htxf, Hpend, Hdel, HW, Hhkf, Hhk, Hdb', Hwtx, #Htxdb, Hmu⟩,
    Hg, %Hwf⟩
  icombine Ht Ht' gives %Heq
  subst Heq
  icases batchGhostAt_bufRc γ P st false c $$ Hg with ⟨Hg, #Hbr⟩
  ihave #Hbr' := bufRc_congr (st := st) (st' := (st.create bi)) rfl rfl $$ Hbr
  imod batchGhost_step_rb γ P (st := st) (st' := (st.create bi)) rfl rfl rfl
    (pend_succ_nat Hwf Hp) (fun i => by simp [BSess.del, BSess.create, BSess.delBucket])
    bi.name (hkData_create st bi)
    (rbData_create_other st bi) fkOkG_create fkVals_create (fun _ => ⟨bi.id, Hhas⟩)
    (BSess.create_S_other st bi) rfl (trkOk_createS Hwf bi) (fun L _ hd => dlsW_step dlsS_create dlsOk_create rfl rfl hd)
    (fun _ _ => rfl) k c (fun _ _ => rfl) (fun _ => rfl) (fun _ h => h) (fun h => by subst h; revert Hkc; cases c <;> decide) $$ Hbr' Hg Hrbp with ⟨Hg, Hrbp⟩
  wp_apply (hBT γ P W Pk b t st bk bi Hn0 Hn1) $$ [Htxf Hpend Hwtx] as Hw
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
    exact sessWf_create Hwf Hp

end proof

end EtcdGrove
end Perennial
