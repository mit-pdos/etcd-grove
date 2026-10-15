/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTxBuffered__unsafeCommit.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__unsafeCommit
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__unsafeCommit
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__commit
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__begin
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__reset
public import Spec.go_etcd_io.bbolt.Tx__Rollback_kv
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ReadSide
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvCommit

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
variable [go_etcd_io.bbolt.Assumptions] [go_uber_org.zap.Assumptions] [_root_.Perennial.time.Assumptions]

theorem backend.batchTxBuffered.unsafeCommit.wp_proof
    (hRollback : bbolt.Tx.Rollback_kv.spec (GF := GF) (hG := hG))
    (hReset : backend.readTx.reset.spec (GF := GF) (hG := hG))
    (hBC : backend.batchTx.commit.spec (GF := GF) (hG := hG))
    (hBegin : backend.backend.begin.spec (GF := GF) (hG := hG)) :
    backend.batchTxBuffered.unsafeCommit.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b t rt st win stop m u
  wp_start as ⟨#Hb, #Ht, #Hrt, Hl, HWR, Hrr, %Hc, Hpay⟩
  obtain ⟨Hroom, Hp0, HWe, Hview⟩ := Hc
  icases isBackend_bt γ P W Pk b t $$ [Hb Ht] with
    ⟨%db0, %lg, %h, #Hbe, #Hlg, %Hlgn, #Hlim, #Hh, #Hhs, #Hm, #Hdb0, %HP⟩
  · iframe #
  icases isBackend_b γ P W Pk b $$ Hb with
    ⟨%t2, %rt2, %db1, %lg2, #-, #Hrt2, #-, %-, #Hmi, #-, #-, #Hrg, #-, #-, #Hci, %-⟩
  icombine Hrt Hrt2 gives %Heq
  subst Heq
  unfold batchLockedW batchGhostW
  icases Hl with ⟨%t1, %db0', #Ht1, Hown, Hph, ⟨Hv, %n0, %w0, %u00, Hrvs, Ha, Hmo, Hus, Hopn, Hhkd, %Hbg0⟩,
    %Hwf⟩
  icombine Ht Ht1 gives %Heq1
  subst Heq1
  imod (rtRes_cm_open γ P rt st.C st.R win) $$ [$Hrr $Hrvs] with
    ⟨%rtx, %cm, %wg, Hrtx, Hcm, Hwg, HRB, Hrb, HrtCm, Hrvs⟩
  icases rtCm_rvs γ P st.C st.R win $$ HrtCm with ⟨Hrvs2, HrtCmBack⟩
  imod ghostVar_update_halves (((st.C, st.R) : RView), false) γ.rvs _ _ $$ Hrvs Hrvs2 with
    ⟨Hrvs, Hrvs2⟩
  -- the commit opens the hook's window (`BSess.setHw`): the hook may re-put its keys
  have Hwin := hookWin_of Hbg0 Hp0
  ihave Hpay : payIn γ (st.setHw true) stop m u $$ [Hpay]
  · rw [payIn_setHw]; iexact Hpay
  ihave Hl : batchLocked γ P b (st.setHw true) $$ [Hown Hph Hv Hrvs Ha Hmo Hus Hopn Hhkd]
  · iapply batchLockedW_setHw γ P b st
    unfold batchLockedW batchGhostW
    iexists t, db0'
    iframe
    iframe #
    ipureintro
    exact ⟨Hbg0, Hwf⟩
  wp_auto
  have Hp0 : (st.setHw true).cnt.p0 = sint.nat (st.setHw true).pend := Hp0
  have HWe : ∀ nm i, P.BT.lookup nm = some i → P.HB nm = false →
      bkOf (st.setHw true).W.bks i = [] := HWe
  have Hview : win = false →
      vData P ((st.setHw true).C, (st.setHw true).R) = sData P (st.setHw true).S := Hview
  have Hwf := sessWf_setHw Hwf
  have Hbg0 := bgOk_setHw true Hbg0
  wp_join iprop(∃ st' : BSess, batchLocked γ P b st' ∗ Pk ∗ ⌜hookStep P (st.setHw true) st'⌝ ∗
      t_ptr ↦ t) at next
      with [Hl HWR t] as ⟨%st', Hl, HWR, %Hs, t⟩
  · unfold hooksSpec
    icases Hhs with (%Hnil | ⟨%ho, %Hho, #Hhook⟩)
    · subst Hnil
      wp_auto
      wp_join_done
      iexists (st.setHw true)
      iframe
      ipureintro
      exact hookStep_refl P (st.setHw true)
    · subst Hho
      wp_auto
      wp_apply Hhook $$ %(st.setHw true) [$Hl $HWR] as ⟨%st', Hl, HWR, %Hs⟩
      · ipureintro
        exact ⟨rfl, Hroom, Hwin⟩
      wp_join_done
      iexists st'
      iframe
      ipureintro
      exact Hs
  ihave Hl := batchLocked_W γ P b st' $$ Hl
  unfold batchLockedW batchGhostW
  icases Hl with ⟨%t1, %db, #Ht1, Hown, Hph, ⟨Hv, %n, %w, %u0, Hrvs, Ha, Hmo, Hus, Hopn, Hhkd, %Hbg⟩,
    %Hwf'⟩
  icombine Ht Ht1 gives %Heq1
  subst Heq1
  have Hs0 := Hs
  obtain ⟨hC, hR, hSs, hWs, hp1, hp2, hn, htx, hcnt⟩ := Hs0
  imod ghostVar_update_halves (((st'.C, st'.R) : RView), win) γ.rvs _ _ $$ Hrvs Hrvs2 with
    ⟨Hrvs, Hrvs2⟩
  ihave HrtCm : rtCm γ P st'.C st'.R win $$ [HrtCmBack Hrvs2]
  · rw [hC, hR, setHw_C, setHw_R]
    iapply HrtCmBack $$ Hrvs2
  ihave HRB : ownRB (rbufOf (baseOf rt)) st'.R $$ [HRB]
  · rw [hR, setHw_R]
    iexact HRB
  unfold batchPhys
  icases Hph with ⟨%hk, Htxf, Hpend, Hdel, HW, Hhkf, Hhk, Hdb, Hwtx, #Htxdb, Hmu⟩
  icases Hrb with (Hrb | ⟨%Hnull, #Hbs⟩)
  rotate_left
  · unfold bStopped
    icombine Hopn Hbs gives %Hcb
    exact absurd Hcb.2 (by decide)
  ihave %Hrnn : ⌜rtx ≠ Loc.null⌝ $$ [Hrb]
  · unfold rollbackRes
    icases Hrb with ⟨%γwg, %γw, %γo, %γd, %D, -, -, -, -, Hl1, -⟩
    iapply txLive_nonnull $$ Hl1
  try wp_auto
  rw [decide_eq_false Hrnn]
  wp_auto
  wp_apply wp_fork $$ [Hrb]
  · wp_auto
    wp_apply (wp_rollback_Wait γ rtx wg) $$ [$Hrb] as ⟨%D, Hl1, #Hsn⟩
    wp_apply (hRollback rtx D) $$ [$Hl1 $Hsn] as -
    itrivial
  wp_apply (hReset rt st'.R cm rtx wg) $$ [$HRB $Hcm $Hrtx $Hwg] as %cm' %wg' ⟨HRB, Hcm, Hcmm, Hrtx, Hwg, Hwgz⟩
  wp_apply (hBC γ P W Pk b t db st' stop) $$ [Htxf Hpend Hwtx $Hdb $Htxdb $Hmu] as ⟨Hmu, Hres⟩
  · iframe #
    unfold btW
    iframe
  iapply wp_fupd
  cases stop
  · icases Hres with (⟨%HA, Hw, Hdb, #Htxdb⟩ | ⟨%HB, Hdb, Hpend, %tx', Htxf, Hrest⟩)
    · unfold btW
      icases Hw with ⟨Htxf, Hpend, Hwtx⟩
      rw [HA.1]
      wp_auto
      wp_apply (hBegin γ P W Pk b db st'.C false) $$ [$Hmu $Hdb] as %txr ⟨Hmu, Hdb, #Htxdbr, Hrd⟩
      · iframe #
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
      have hview : win = false → vData P (st'.C, st'.R.reset) = vData P (st'.C, st'.R) := by
        intro hw
        rw [(commit_final (tx' := st'.tx) (cnt' := ⟨0, 0, 0, 0, false⟩) HP Hwf rfl HWe Hs Hwf' (Or.inr ⟨HA.1, rfl⟩)).2.2, hC, hR]
        exact (Hview hw).symm
      imod (rtRes_cm_close γ P rt st'.C st'.C st'.R win false txr cm' wg' hview) $$
        [$Hci $HrtCm $Hrvs $Hv $Hrtx $Hcm $Hcmm $Hwg $Hwgz $HRB Hrd] with ⟨Hrr, Hrvs, Hv, Hbv⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]
        iexact Hrd
      imod (commit_ghost γ P (st.setHw true) st' st'.C st'.tx m u n w u0 HWe Hp0 Hs Hwf Hbg) $$
        [$Hpay $Ha $Hmo $Hus $Hopn $Hv $Hrvs $Hhkd] with ⟨%cnt', %Hcw, Hg, Hpo⟩
      obtain ⟨hsw, hfo, hv⟩ := commit_final (tx' := st'.tx) (cnt' := cnt') HP Hwf Hcw HWe Hs Hwf' (Or.inr ⟨HA.1, rfl⟩)
      imodintro
      iapply HΦ
      iframe Hrr HWR Hpo
      try simp only [Bool.false_eq_true, ↓reduceIte]
      iexists (commitSt st' st'.C st'.tx cnt'), db
      iframe Hown Hg
      try unfold batchPhys
      simp only [commitSt_C, commitSt_R, commitSt_S, commitSt_W, commitSt_pend, commitSt_ndel, commitSt_tx]
      isplitl [Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu]
      · iexists hk
        iframe
        iframe #
      isplitr
      · ipureintro
        exact ⟨hfo, hv, by simp [commitSt]⟩
      iexact Hbv
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hrest with ⟨Hwtx, #Htxdb'⟩
      wp_auto
      wp_apply (hBegin γ P W Pk b db st'.S false) $$ [$Hmu $Hdb] as %txr ⟨Hmu, Hdb, #Htxdbr, Hrd⟩
      · iframe #
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
      have hview : win = false → vData P (st'.S, st'.R.reset) = vData P (st'.C, st'.R) := by
        intro hw
        rw [(commit_final (tx' := tx') (cnt' := ⟨0, 0, 0, 0, false⟩) HP Hwf rfl HWe Hs Hwf' (Or.inl rfl)).2.2, hC, hR]
        exact (Hview hw).symm
      imod (rtRes_cm_close γ P rt st'.C st'.S st'.R win false txr cm' wg' hview) $$
        [$Hci $HrtCm $Hrvs $Hv $Hrtx $Hcm $Hcmm $Hwg $Hwgz $HRB Hrd] with ⟨Hrr, Hrvs, Hv, Hbv⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]
        iexact Hrd
      imod (commit_ghost γ P (st.setHw true) st' st'.S tx' m u n w u0 HWe Hp0 Hs Hwf Hbg) $$
        [$Hpay $Ha $Hmo $Hus $Hopn $Hv $Hrvs $Hhkd] with ⟨%cnt', %Hcw, Hg, Hpo⟩
      obtain ⟨hsw, hfo, hv⟩ := commit_final (tx' := tx') (cnt' := cnt') HP Hwf Hcw HWe Hs Hwf' (Or.inl rfl)
      imodintro
      iapply HΦ
      iframe Hrr HWR Hpo
      try simp only [Bool.false_eq_true, ↓reduceIte]
      iexists (commitSt st' st'.S tx' cnt'), db
      iframe Hown Hg
      try unfold batchPhys
      simp only [commitSt_C, commitSt_R, commitSt_S, commitSt_W, commitSt_pend, commitSt_ndel, commitSt_tx]
      isplitl [Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu]
      · iexists hk
        iframe
        iframe #
      isplitr
      · ipureintro
        exact ⟨hfo, hv, by simp [commitSt]⟩
      iexact Hbv
  · icases Hres with (⟨%HA, -⟩ | ⟨%HB, Hdb, Hpend, %tx', Htxf, -⟩)
    · exact absurd HA.2 (by decide)
    wp_auto
    unfold payIn
    simp only [↓reduceIte]
    icases Hpay with ⟨Hbo, Hq⟩
    imod opn_stop γ $$ Hopn Hq Hbo with #Hbs
    have hview : win = false → vData P (st'.S, st'.R.reset) = vData P (st'.C, st'.R) := by
      intro hw
      rw [(commit_final (tx' := tx') (cnt' := ⟨0, 0, 0, 0, false⟩) HP Hwf rfl HWe Hs Hwf' (Or.inl rfl)).2.2, hC, hR]
      exact (Hview hw).symm
    imod (rtRes_cm_close γ P rt st'.C st'.S st'.R win true Loc.null cm' wg' hview) $$
      [$Hci $HrtCm $Hrvs $Hv $Hrtx $Hcm $Hcmm $Hwg $Hwgz $HRB] with ⟨Hrr, -, -, -⟩
    · simp only [↓reduceIte]
      iframe Hbs
    imodintro
    iapply HΦ
    iframe Hrr HWR
    unfold payOut
    simp only [Bool.true_eq_false, _root_.false_and, ↓reduceIte]
    iframe Hown Hbs Hpend

end proof

end EtcdGrove
end Perennial
