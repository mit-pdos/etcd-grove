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
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ReadSide
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvCommit
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt
public import Spec.go_etcd_io.bbolt.Tx__Rollback

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
variable [go_etcd_io.bbolt.Assumptions] [go_uber_org.zap.Assumptions] [_root_.Perennial.time.Assumptions]

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt backend Fs in
/-- (S3e) bbolt's canonical spec in the backend's vocabulary, at `theFs` (until then the
`_kv` spec `Tx.Rollback_kv`). -/
private theorem bbolt.kvGlue_Tx__Rollback_kv (h : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt] [os.file.FieldAssumptions]
      [os.fileStat.FieldAssumptions], bbolt.Tx.Rollback.spec (GF := GF) (hG := hG)) :
  ∀ (tx : Loc) (γ : DBNames) (D : backend.Data),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ txLive tx γ 1 (bbolt.TxView.ro D) }}
    (App (Val (tx @!! go.GoType.PointerType go_etcd_io.bbolt.Tx.ty @!! go!"Rollback")) (Val #()))
  {{ RET #GoInterface.nil; backend.txDone tx ∗ threadTok }} := by
  intro tx γ D
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, onFs_none hfs]
    iintro %Φ ⟨-, H⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, backend.curAt_eq, backend.bktEnts_eq, backend.seekIdx_eq,
      onFs_some hfs]
    iintro %Φ ⟨-, Hl⟩ HΦ
    have h' := h tx γ (TxView.ro D)
    try simp only [wView.proj_rw, wView.proj_base, wView.proj_cur, wView.proj_gen, TxView.ro.proj_rw, TxView.ro.proj_base, TxView.ro.proj_cur, TxView.ro.proj_gen, wView_setBkt, wView_dropBkt] at h'
    wp_apply h' $$ [$Hl] as ⟨#Hd, Ht⟩
    iapply HΦ; iframe Ht; iexact Hd

theorem backend.batchTxBuffered.unsafeCommit.wp_proof
    (hRollback : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt] [os.file.FieldAssumptions]
      [os.fileStat.FieldAssumptions], bbolt.Tx.Rollback.spec (GF := GF) (hG := hG))
    (hReset : backend.readTx.reset.spec (GF := GF) (hG := hG))
    (hBC : backend.batchTx.commit.spec (GF := GF) (hG := hG))
    (hBegin : backend.backend.begin.spec (GF := GF) (hG := hG)) :
    backend.batchTxBuffered.unsafeCommit.spec (GF := GF) (hG := hG) := by
  replace hRollback := bbolt.kvGlue_Tx__Rollback_kv hRollback
  intro γ P W Pk b t rt st win stop m u X Y L' c Sc Rr E hE
  wp_start as ⟨#Hb, #Ht, #Hrt, Hl, HWR, Hrr, %Hc, Hpre, %Hdlw, %Hhw0, Hpay, HX, #Hrq, %Hsc, HRr, #Hacc⟩
  obtain ⟨Hroom, Hp0, HWe, Htk⟩ := Hc
  icases isBackend_bt γ P W Pk b t $$ [Hb Ht] with
    ⟨%db0, %lg, %h, #Hbe, #Hlg, #Hlgn, #Hlim, #Hh, #Hhs, #Hm, #Hdb0, %HP⟩
  · iframe #
  icases isBackend_b γ P W Pk b $$ Hb with
    ⟨%t2, %rt2, %db1, %lg2, #-, #Hrt2, #-, #-, #Hmi, #-, #-, #Hrg, #-, #-, #Hci, %-⟩
  ihave #Hbc := isBackend_beginCtx γ P W Pk b $$ Hb
  icombine Hrt Hrt2 gives %Heq
  subst Heq
  unfold batchLockedW batchGhostW
  icases Hl with ⟨%t1, %db0', #Ht1, Hown, Hph, ⟨Hv, %n0, %w0, %u00, Hrvs, Ha, Hmo, Hus, Hopn, Hhkd, Hfkh,
    %Hbg0⟩, %Hwf⟩
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
  -- out of a window, the state is out of an `Unlock`'s (the batch lock's quarter's agreement)
  icases batchViewQW_win γ P st win $$ Hv with ⟨Hv, %Hwin00⟩
  have Hwin0 : win = false → st.win = false := fun h => Hwin00 h Hhw0
  icases trkSide_cw γ P st c $$ Hhkd with ⟨Hhkd, %Hcw0⟩
  -- (A1.5) the claimed writes are among `Sc` (none in the client-facing mode)
  have HcwS : ∀ n, st.cw n = true → n ∈ Sc := fun n h => by
    rcases Hsc.2 with hc | hS
    · rw [Hcw0 hc Hhw0 n] at h; cases h
    · exact hS n h
  ihave Hl : batchLocked γ P b (st.setHw true) $$ [Hown Hph Hv Hrvs Ha Hmo Hus Hopn Hhkd Hfkh]
  · ihave Hv := batchViewQ_setHw γ P st win (fun h => (Hdlw h).1) $$ Hv
    iapply batchLocked_setHw_mk γ P b t db0' st c
    iframe Ht Hown Hph Hv
    isplitl [Hrvs Ha Hmo Hus Hopn Hhkd Hfkh]
    · iexists n0, w0, u00
      iframe
      ipureintro; exact Hbg0
    · ipureintro; exact Hwf
  wp_auto
  have Hp0 : (st.setHw true).cnt.p0 = sint.nat (st.setHw true).pend := Hp0
  have HWe : ∀ nm i, P.BT.lookup nm = some i → P.HB nm = false →
      bkOf (st.setHw true).W.bks i = [] := HWe
  have Hwf := sessWf_setHw Hwf
  have Hbg0 := bgOk_setHw true Hbg0
  wp_join iprop(∃ st' : BSess, batchLocked γ P b st' ∗ Pk ∗ ⌜hookStep P (st.setHw true) st'⌝ ∗
      payIn γ (st.setHw true) stop m u ∗ t_ptr ↦ t ∗ Y) at next
      with [Hl HWR t HX Hpay] as ⟨%st', Hl, HWR, %Hs, Hpay, t, HY⟩
  · unfold commitReq
    icases Hrq with (#Hw | ⟨%t', %h', #Ht', #Hh', #Hrq⟩)
    · -- no request: the hook as `hooksSpec` says, `X` passed along
      ihave HY := Hw $$ HX
      unfold hooksSpec
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
        wp_apply Hhook $$ %(st.setHw true) %stop %m %u [$Hl $HWR $Hpay] as ⟨%st', Hl, HWR, Hpay, %Hs⟩
        · ipureintro
          exact ⟨rfl, Hroom, Hwin⟩
        wp_join_done
        iexists st'
        iframe
        ipureintro
        exact Hs
    · -- the request: the backend's hooks serve it
      icombine Ht Ht' gives %Heqt
      subst Heqt
      icombine Hh Hh' gives %Heqh
      subst Heqh
      unfold hooksReq
      icases Hrq with ⟨%ho, %Hho, #Hhook⟩
      subst Hho
      wp_auto
      wp_apply Hhook $$ %(st.setHw true) %stop %m %u [$Hl $HWR $HX $Hpay] as ⟨%st', Hl, HWR, HY, Hpay, %Hs⟩
      · ipureintro
        exact ⟨rfl, Hroom, Hwin⟩
      wp_join_done
      iexists st'
      iframe
      ipureintro
      exact Hs
  ihave Hl := batchLocked_W γ P b st' $$ Hl
  unfold batchLockedW batchGhostW
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hl with ⟨%t1, %db, #Ht1, Hown, Hph, ⟨Hv, %n, %w, %u0, Hrvs, Ha, Hmo, Hus, Hopn, Hhkd, Hfkh,
    %Hbg⟩, %Hwf'⟩
  unfold batchViewQ
  icases Hv with ⟨%Lb, Hv, %Hdlb⟩
  have Hdlc : dlsS P st' ∧ dlsOk P st' (if win then L' else Lb) := by
    refine ⟨Hdlb.1, ?_⟩
    cases win with
    | true =>
      simp only [↓reduceIte]
      exact dlsOk_congr Hs.2.2.1 Hs.2.2.2.2.2.2.2.2.2.2.1 (Hdlw rfl).2
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply Hdlb.2.1
      rw [Hs.2.2.2.2.2.2.2.2.2.2.2.1]
      exact Hwin0 rfl
  icombine Ht Ht1 gives %Heq1
  subst Heq1
  have HcwS' : ∀ n, st'.cw n = true → n ∈ Sc := fun n h => by
    rw [Hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2] at h; exact HcwS n h
  -- (A1.5) the commit moves every tracked bucket's readers' contents to the writer's
  have HokC : ∀ C' : Data, (C' = st'.S ∨ (st'.pend = W64 0 ∧ C' = st'.C)) → ∀ n, n ∈ Sc →
      P.RB n = true → rvBkt P (C', st'.R.reset) n = bktOf st.S n := fun C' hC' n _ hn => by
    rw [(trkOk_commitG (tx' := Loc.null) (cnt' := ⟨0, 0, 0, 0, false⟩) Hs Htk
      Hbg.2.2.2.2.2.2.2.2.2.2.1 Hwf' hC').2 n hn]
    exact bktOf_rb Hs.2.2.2.1 hn
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
  icases Hph with ⟨%hk, Htxf, Hpend, Hdel, HW, Hhkf, Hhk, Hdb, Hwtx, #Htxdb, Hmu, #Hbdb⟩
  icases Hrb with (Hrb | ⟨%Hnull, #Hbs⟩)
  rotate_left
  · unfold bStopped
    icombine Hopn Hbs gives %Hcb
    exact absurd Hcb.2 (by decide)
  ihave %Hrnn : ⌜rtx ≠ Loc.null⌝ $$ [Hrb]
  · unfold rollbackRes
    icases Hrb with ⟨%γwg, %γw, %γo, %γd, %D, %db1, -, -, -, -, Hl1, -⟩
    iapply txLive_nonnull $$ Hl1
  try wp_auto
  rw [decide_eq_false Hrnn]
  wp_auto
  -- (2026-11-06, `notes/begin-tok-plan.md`) the fork's fresh token stays here, for the new read
  -- transaction (or the post, at the stop); the rollback goroutine exits with the old one's
  wp_apply wp_fork_tok_self $$ [Hrb] as Htok
  · wp_auto
    wp_apply (wp_rollback_Wait γ rtx wg) $$ [$Hrb] as ⟨%D, Hl1⟩
    wp_apply (hRollback rtx γ.db D) $$ [$Hl1] as ⟨-, Htok⟩
    iframe Htok
    itrivial
  wp_apply (hReset rt st'.R cm rtx wg) $$ [$HRB $Hcm $Hrtx $Hwg] as %cm' %wg' ⟨HRB, Hcm, Hcmm, Hrtx, Hwg, Hwgz⟩
  -- (backend-snapshot B1) a stop's payment goes to the stop's commit, which stops the backend at its
  -- commit point (`stopPay`)
  ihave Hsplit : iprop((if stop then stopPay γ else emp) ∗
      (if stop then emp else payIn γ (st.setHw true) stop m u)) $$ [Hpay]
  · cases stop
    · simp only [Bool.false_eq_true, ↓reduceIte]
      iframe Hpay
    · simp only [↓reduceIte]
      unfold payIn stopPay
      simp only [↓reduceIte]
      iframe Hpay
  icases Hsplit with ⟨Hsp, Hpay⟩
  wp_apply (hBC γ P W Pk b t db st' stop) $$ [Htxf Hpend Hwtx $Hdb $Htxdb $Hmu $Hopn $Hsp] as ⟨Hmu, Hres⟩
  · iframe #
    unfold btW
    iframe
  iapply wp_fupd
  cases stop
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hres with (⟨%HA, Hw, Hdb, #Htxdb, Hopn⟩ | ⟨%HB, Hdb, Hpend, %tx', Htxf, Hrest⟩)
    · unfold btW
      icases Hw with ⟨Htxf, Hpend, Hwtx⟩
      rw [HA.1]
      wp_auto
      wp_apply (hBegin γ.db b db st'.C false) $$ [$Hmu $Hdb Htok] as %txr ⟨Hmu, Hdb, #Htxdbr, Hrd⟩
      · iframe #
        simp only [Bool.false_eq_true, ↓reduceIte]
        iexact Htok
      ihave Hpre : (if win then thinV γ (vData P (st'.C, st'.R.reset)) L'
          else thinV γ (vData P (st'.C, st'.R.reset)) (vData P (st'.C, st'.R))) $$ [Hpre]
      · rw [(commit_final (tx' := st'.tx) (cnt' := ⟨0, 0, 0, 0, false⟩) HP Hwf rfl HWe Hs Hwf' (Or.inr ⟨HA.1, rfl⟩)).2.2, hC, hR,
          setHw_C, setHw_R, setHw_S]
        iexact Hpre
      icases fkHalf_rd γ P st' (st'.C, st'.R.reset)
        (fun f w h => fkOkRvG_of (fkOkG_commit (C' := st'.C) (tx' := st'.tx) (cnt' := st'.cnt) (Or.inr rfl) f w h))
        $$ Hfkh with ⟨Hfkh, #Hfkr⟩
      ihave Hupd := trkSide_updR γ P st' (commitSt st' st'.C st'.tx ⟨0, 0, 0, 0, false⟩) (st'.C, st'.R)
        (st'.C, st'.R.reset) false false Sc (fun n _ v => v = bktOf st.S n) Rr E hE Hsc.1 rfl rfl rfl
        (fun n hn hi _ => ⟨rfl, rvBkt_commit_idle Hs Htk Hbg.2.2.2.2.2.2.2.2.2.2.1 Hwf' (Or.inr ⟨HA.1, rfl⟩) hn hi⟩)
        (fun _ _ => Or.inl rfl) (fun _ _ _ => rfl) HcwS' (fun _ _ _ => rfl) (fun n hn hRB => HokC _ (Or.inr ⟨HA.1, rfl⟩) n hn hRB)
        $$ [$Hhkd $HRr $Hacc]
      imod (rtRes_cm_close γ P rt st'.C st'.C st'.R win false txr cm' wg' Lb L'
        iprop(trkSide γ P (commitSt st' st'.C st'.tx ⟨0, 0, 0, 0, false⟩) ∗ Rr)) $$
        [$Hci $HrtCm $Hrvs $Hv $Hrtx $Hcm $Hcmm $Hwg $Hwgz $HRB $Hpre $Hupd Hrd]
        with ⟨Hrr, Hrvs, ⟨Hhkd, HRr⟩, Hv, Hbv⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]
        iframe Hrd; isplitr; · iexists db0; iexact Hdb0
        iframe #
      imod (commit_ghost γ P (st.setHw true) st' st'.C st'.tx m u n w u0 _ ⟨0, 0, 0, 0, false⟩ HWe Hp0 Hs
        Hwf Hbg
        (Or.inr ⟨HA.1, rfl⟩) Hdlc Htk Hwf') $$ [$Hpay $Ha $Hmo $Hus $Hopn $Hv $Hrvs $Hhkd $Hfkh] with ⟨%cnt', %Hcw, Hg, Hpo⟩
      obtain ⟨hsw, hfo, hv⟩ := commit_final (tx' := st'.tx) (cnt' := cnt') HP Hwf Hcw HWe Hs Hwf' (Or.inr ⟨HA.1, rfl⟩)
      imodintro
      iapply HΦ
      iframe Hrr HWR Hpo HY HRr
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
        exact ⟨hfo, hv, by simp [commitSt], Hs.2.2.2.1⟩
      iexact Hbv
    · try simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hrest with ⟨Hwtx, #Htxdb', Hopn⟩
      wp_auto
      wp_apply (hBegin γ.db b db st'.S false) $$ [$Hmu $Hdb Htok] as %txr ⟨Hmu, Hdb, #Htxdbr, Hrd⟩
      · iframe #
        simp only [Bool.false_eq_true, ↓reduceIte]
        iexact Htok
      ihave Hpre : (if win then thinV γ (vData P (st'.S, st'.R.reset)) L'
          else thinV γ (vData P (st'.S, st'.R.reset)) (vData P (st'.C, st'.R))) $$ [Hpre]
      · rw [(commit_final (tx' := tx') (cnt' := ⟨0, 0, 0, 0, false⟩) HP Hwf rfl HWe Hs Hwf' (Or.inl rfl)).2.2, hC, hR,
          setHw_C, setHw_R, setHw_S]
        iexact Hpre
      icases fkHalf_rd γ P st' (st'.S, st'.R.reset)
        (fun f w h => fkOkRvG_of (fkOkG_commit (C' := st'.S) (tx' := tx') (cnt' := st'.cnt) (Or.inl rfl) f w h))
        $$ Hfkh with ⟨Hfkh, #Hfkr⟩
      ihave Hupd := trkSide_updR γ P st' (commitSt st' st'.S tx' ⟨0, 0, 0, 0, false⟩) (st'.C, st'.R)
        (st'.S, st'.R.reset) false false Sc (fun n _ v => v = bktOf st.S n) Rr E hE Hsc.1 rfl rfl rfl
        (fun n hn hi _ => ⟨rfl, rvBkt_commit_idle Hs Htk Hbg.2.2.2.2.2.2.2.2.2.2.1 Hwf' (Or.inl rfl) hn hi⟩)
        (fun _ _ => Or.inl rfl) (fun _ _ _ => rfl) HcwS' (fun _ _ _ => rfl) (fun n hn hRB => HokC _ (Or.inl rfl) n hn hRB)
        $$ [$Hhkd $HRr $Hacc]
      imod (rtRes_cm_close γ P rt st'.C st'.S st'.R win false txr cm' wg' Lb L'
        iprop(trkSide γ P (commitSt st' st'.S tx' ⟨0, 0, 0, 0, false⟩) ∗ Rr)) $$
        [$Hci $HrtCm $Hrvs $Hv $Hrtx $Hcm $Hcmm $Hwg $Hwgz $HRB $Hpre $Hupd Hrd]
        with ⟨Hrr, Hrvs, ⟨Hhkd, HRr⟩, Hv, Hbv⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]
        iframe Hrd; isplitr; · iexists db0; iexact Hdb0
        iframe #
      imod (commit_ghost γ P (st.setHw true) st' st'.S tx' m u n w u0 _ ⟨0, 0, 0, 0, false⟩ HWe Hp0 Hs
        Hwf Hbg
        (Or.inl rfl) Hdlc Htk Hwf') $$ [$Hpay $Ha $Hmo $Hus $Hopn $Hv $Hrvs $Hhkd $Hfkh] with ⟨%cnt', %Hcw, Hg, Hpo⟩
      obtain ⟨hsw, hfo, hv⟩ := commit_final (tx' := tx') (cnt' := cnt') HP Hwf Hcw HWe Hs Hwf' (Or.inl rfl)
      imodintro
      iapply HΦ
      iframe Hrr HWR Hpo HY HRr
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
        exact ⟨hfo, hv, by simp [commitSt], Hs.2.2.2.1⟩
      iexact Hbv
  · icases Hres with (⟨%HA, -⟩ | ⟨%HB, Hdb, Hpend, %tx', Htxf, Hrest⟩)
    · exact absurd HA.2 (by decide)
    wp_auto
    simp only [↓reduceIte]
    -- (backend-snapshot B1) the stop's commit stopped the backend and took the commit invariant's half
    icases Hrest with ⟨#Hbs, Hhalf⟩
    ihave Hpre : (if win then thinV γ (vData P (st'.S, st'.R.reset)) L'
        else thinV γ (vData P (st'.S, st'.R.reset)) (vData P (st'.C, st'.R))) $$ [Hpre]
    · rw [(commit_final (tx' := tx') (cnt' := ⟨0, 0, 0, 0, false⟩) HP Hwf rfl HWe Hs Hwf' (Or.inl rfl)).2.2, hC, hR,
        setHw_C, setHw_R, setHw_S]
      iexact Hpre
    icases fkHalf_rd γ P st' (st'.S, st'.R.reset)
      (fun f w h => fkOkRvG_of (fkOkG_commit (C' := st'.S) (tx' := tx') (cnt' := st'.cnt) (Or.inl rfl) f w h))
      $$ Hfkh with ⟨Hfkh, #Hfkr⟩
    ihave Hupd := trkSide_updR γ P st' (commitSt st' st'.S tx' ⟨0, 0, 0, 0, false⟩) (st'.C, st'.R)
      (st'.S, st'.R.reset) false false Sc (fun n _ v => v = bktOf st.S n) Rr E hE Hsc.1 rfl rfl rfl
      (fun n hn hi _ => ⟨rfl, rvBkt_commit_idle Hs Htk Hbg.2.2.2.2.2.2.2.2.2.2.1 Hwf' (Or.inl rfl) hn hi⟩)
      (fun _ _ => Or.inl rfl) (fun _ _ _ => rfl) HcwS' (fun _ _ _ => rfl) (fun n hn hRB => HokC _ (Or.inl rfl) n hn hRB)
      $$ [$Hhkd $HRr $Hacc]
    imod (rtRes_cm_close γ P rt st'.C st'.S st'.R win true Loc.null cm' wg' Lb L'
      iprop(trkSide γ P (commitSt st' st'.S tx' ⟨0, 0, 0, 0, false⟩) ∗ Rr)) $$
      [$Hci $HrtCm $Hrvs $Hv $Hrtx $Hcm $Hcmm $Hwg $Hwgz $HRB $Hpre $Hupd] with ⟨Hrr, -, ⟨Hhkd, HRr⟩, Hvq, -⟩
    · simp only [↓reduceIte]
      iframe Hbs Hfkr
    imodintro
    iapply HΦ
    iframe Hrr HWR HY HRr
    unfold payOut
    simp only [Bool.true_eq_false, _root_.false_and, ↓reduceIte]
    iframe Hown Hbs Hpend Htok
    -- (R2b-3c part 2) the database, and the lock's ghost shares at the committed data
    iunfold bDBOutG
    iexists db, st'.S
    iframe Hbdb Hdb Hhalf
    unfold bStopG fkHalf
    icases Hfkh with ⟨-, Hfkd, Hdls⟩
    iunfold trkSide at Hhkd
    icases Hhkd with ⟨Hhkd, -⟩
    ihave Hhkd := trkHalf_mono γ P _ _ (fun _ => True) (fun _ _ => trivial) $$ Hhkd
    ihave Hhkd := (show trkHalf (GF := GF) γ P (commitSt st' st'.S tx' ⟨0, 0, 0, 0, false⟩).S ⊢
      trkHalf γ P st'.S from .rfl) $$ Hhkd
    iframe Hhkd Hfkd
    isplitl [Hvq Hdls]
    · iexists _, _
      rw [← vData_reset P st'.S st'.R]
      iframe Hvq Hdls
      -- (2026-11-07, the stop image) the quarter's agreement with the deleted entries
      ipureintro; rw [vData_reset P st'.S st'.R]; exact dlVd_of_dlsOk Hdlc.2
    iexists _
    iexact Hfkr

end proof

end EtcdGrove
end Perennial
