/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTxBuffered__Unlock.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__Unlock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__Unlock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__commit
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__Lock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__Unlock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.txWriteBuffer__writeback
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ReadSide
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.WritebackLemmas
public import Proof.go_etcd_io.raft.v3.FrameH

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

set_option hygiene false in
/-- `batchTx.Unlock` with the batch left free at state `S` (`hb` its ghost bound, `hf` its
freedom), then the postcondition (the four free outcomes: nothing pending, or written back
without a commit, with or without a view to update). -/
local macro "bu_free" S:term:max hb:term:max hf:term:max : tactic => `(tactic| (
    wp_apply (hBU γ P W Pk b t)
      $$ [$(frameH `Hown) Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu Hv Hrvs Ha Hmo Hus Hopn Hhkd Hfkh HWv HPk]
    · iframe #
      unfold batchFree batchPhys batchGhostAt
      ileft
      iexists $S, db
      try simp only [wbSt_C, wbSt_S, wbSt_R, wbSt_W, wbSt_pend, wbSt_ndel, wbSt_tx]
      isplitl [Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu]
      · iexists hk
        iframe
        iframe #
      isplitl [Hv Hrvs Ha Hmo Hus Hopn Hhkd Hfkh]
      · iframe Hv
        iexists _, _, u0
        iframe
        ipureintro
        exact $hb
      isplitr
      · ipureintro
        exact $hf
      iframe HWv HPk
    iapply HΦ
    iexact HQ
  ))

set_option hygiene false in
/-- `commit` of the written-back batch (`vw`: whether a view update is owed, `L` the logical view
it comes back at; `Hpc` the commit's thinness premise), up to its outcome `Hpost` (both commit tests, with or without the view). -/
local macro "bu_commit" vw:term:max L:term:max : tactic => `(tactic| (
    wp_apply (hC γ P W Pk b t rt (wbSt P st) $vw false 2 0 iprop(True) iprop(True) $L) $$ [Hown Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu Hv Hrvs Ha Hmo Hus Hopn Hhkd Hfkh HPk Hpc] as ⟨-, HPk, -, Hpost⟩
    · iframe #
      unfold batchLockedW batchGhostW batchPhys
      isplitl [Hown Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu Hv Hrvs Ha Hmo Hus Hopn Hhkd Hfkh]
      · iexists t, db
        try simp only [wbSt_C, wbSt_S, wbSt_R, wbSt_W, wbSt_pend, wbSt_ndel, wbSt_tx]
        iframe Ht Hown
        isplitl [Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu]
        · iexists hk
          iframe
          iframe #
        isplitl [Hv Hrvs Ha Hmo Hus Hopn Hhkd Hfkh]
        · iframe Hv
          iexists n - 1, w + 1, u0
          iframe
          ipureintro
          exact bgOk_unfree hbg'
        · ipureintro
          exact hwf'
      iframe HPk
      isplitr
      · ipureintro
        exact ⟨Hroom, rfl, fun _ i _ _ => bkOf_writebackW _ _ i⟩
      isplitl [Hpc]
      · simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hpc
      unfold payIn
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]
      isplitr
      · isplitr
        · ipureintro
          rfl
        iapply monoNatLbOwn_le 1 (by omega) $$ Hlb1
      isplitr
      · itrivial
      iapply commitReq_true
    try simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hpost with ⟨%st2, %db2, Hown, Hph2, Hg2, %Hfin, Hbv2⟩
  ))

set_option hygiene false in
/-- `batchTx.Unlock` after a commit, then the postcondition. -/
local macro "bu_release" : tactic => `(tactic| (
    wp_apply (hBU γ P W Pk b t) $$ [$(frameH `Hown) Hph2 Hg2 HWv HPk]
    · iframe #
      ileft
      iexists st2, db2
      iframe
      ipureintro
      exact Hfin.1
    iapply HΦ
    iexact HQ
  ))

theorem backend.batchTxBuffered.Unlock.wp_proof
    (hRLock : backend.readTx.Lock.spec (GF := GF) (hG := hG))
    (hWB : backend.txWriteBuffer.writeback.spec (GF := GF) (hG := hG))
    (hRUnlock : backend.readTx.Unlock.spec (GF := GF) (hG := hG))
    (hC : backend.batchTxBuffered.commit.spec (GF := GF) (hG := hG))
    (hBU : backend.batchTx.Unlock.spec (GF := GF) (hG := hG)) :
    backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b t st Q Hhw Hroom
  wp_start as ⟨#Hb, #Ht, Hl, Htok, Hcase⟩
  icases isBackend_bt γ P W Pk b t $$ [Hb Ht] with
    ⟨%db0, %lg, %h, #Hbe, #Hlg, %Hlgn, #Hlim, #Hh, #Hhs, #Hm, #Hdb0, %HP⟩
  · iframe #
  icases isBackend_b γ P W Pk b $$ Hb with
    ⟨%t2, %rt, %db1, %lg2, #-, #Hrt, #-, %-, #Hmi, #-, #-, #Hrg, #-, #-, #Hci, %-⟩
  ihave Hl := batchLocked_W γ P b st $$ Hl
  unfold batchLockedW batchGhostW
  icases Hl with ⟨%t1, %db, #Ht1, Hown, Hph, ⟨Hv, %n, %w, %u0, Hrvs, Ha, Hmo, Hus, Hopn, Hhkd, Hfkh,
    %Hbg⟩, %Hwf⟩
  icombine Ht Ht1 gives %Heq1
  subst Heq1
  unfold batchPhys
  icases Hph with ⟨%hk, Htxf, Hpend, Hdel, HW, Hhkf, Hhk, Hdb, Hwtx, #Htxdb, Hmu⟩
  wp_auto
  by_cases hp0 : st.pend = W64 0
  · icases Hcase with (⟨#Hth, %Hnw, HWv, HPk, HQ⟩ | ⟨%vd, Hbv, HPk, HQw⟩)
    · rw [decide_eq_true hp0]
      wp_auto
      obtain ⟨hfo, hbg⟩ := free_of_pend0 HP Hwf Hbg hp0 Hhw
      bu_free st hbg hfo
    · -- nothing written: the logical view is `relog`'s (`relog_same`)
      ihave ⟨Hv, Hbv, #Hthvd⟩ := batchViewQ_bView γ P st 1 vd $$ [$Hv $Hbv]
      iunfold thinV at Hthvd
      icases Hthvd with ⟨%Hsub, -⟩
      rw [decide_eq_true hp0]
      wp_auto
      obtain ⟨hfo, hbg⟩ := free_of_pend0 HP Hwf Hbg hp0 Hhw
      have hvf := vData_free P st Hwf hfo.2.2.1 hfo.2.2.2.1
      ihave Hbv : bView γ 1 (relog P vd st) $$ [Hbv]
      · rw [relog_same P vd st hvf.symm Hsub]; iexact Hbv
      icases HQw $$ Hbv with ⟨HWv, HQ⟩
      bu_free st hbg hfo
  · icases Hcase with (⟨#Hth, %Hnw, HWv, HPk, HQ⟩ | ⟨%vd, Hbv, HPk, HQw⟩)
    · -- a deleting session: the write-back leaves the readers' view; the commit's new physical
      -- view is thin of the old
      rw [decide_eq_false hp0]
      wp_auto
      wp_apply (hRLock γ P rt) $$ [$Hrg] as ⟨Hwl, Hrr⟩
      unfold wbTok
      icombine Ha Htok gives %Hle
      imod ownTokAuth_sub 1 γ.wb n $$ Ha Htok with Ha
      imod mono_nat_own_update (w + 1) (by omega) $$ Hmo with ⟨Hmo, #Hlb1⟩
      icases rtRes_wb_open γ P rt st.C st.R $$ [$Hrr $Hrvs] with ⟨HRB, %HRok, Hwb, Hrvs⟩
      have hbb := bgOk_bufBound HP Hwf Hbg
      wp_apply (hWB (wbOf t) st.W (rbufOf (baseOf rt)) st.R Hwf.1 Hwf.2.1 (fun i => hbb i)) $$ [$HW $HRB]
        as ⟨HW, HRB⟩
      have hver : uint.Z st.R.ver + 1 < 2 ^ 64 := by
        have := Hbg.1
        have : 0 ≤ uint.Z st.R.ver := by word
        omega
      have hbg' := bgOk_writeback Hbg Hle
      have hwf' := sessWf_writeback Hwf hp0
      have hsafe : safeRv P (st.C, writebackR st.W st.R) := hwf'.2.2.2.2.2.2.2.2.2.2.1
      icases fkHalf_rd γ P st (st.C, writebackR st.W st.R) (fun f w h => fkOkRvG_of (fkOkG_wb f w h)) $$ Hfkh
        with ⟨Hfkh, #Hfkr⟩
      ihave Hfkh := fkHalf_mono γ P (st' := wbSt P st) fkOkG_wb $$ Hfkh
      have hsame := vData_writeback_same P st.C st.W st.R Hnw
      imod (rtRes_wb_close_same γ P rt st.W st.C st.R Hwf.2.2.1 hver hsame hsafe
        (rbClean_writeback Hnw)) $$ [$Hci $Hwb $HRB $Hrvs $Hfkr]
        with ⟨Hrr, Hrvs⟩
      ihave Hv : batchViewQ γ P (wbSt P st) $$ [Hv]
      · unfold batchViewQ; rw [wbSt_C, wbSt_R, hsame]; iexact Hv
      wp_apply (hRUnlock γ P rt) $$ [$Hwl $Hrr]
      by_cases hcond : (sint.Z P.limit ≤ sint.Z st.pend ∨ 0 < sint.Z st.ndel)
      · ihave Hpc : thinV γ (sData P (wbSt P st).S) (vData P ((wbSt P st).C, (wbSt P st).R)) $$ []
        · rw [wbSt_S, wbSt_C, wbSt_R, hsame]
          iexact Hth
        wp_if_destruct
        · bu_commit false (vData P (st.C, st.R))
          bu_release
        wp_if_destruct
        · bu_commit false (vData P (st.C, st.R))
          bu_release
        exfalso
        rcases hcond with h | h
        · omega
        · exact Hif (by have : sint.Z (W64 0) = 0 := rfl; omega)
      · wp_if_destruct
        · exfalso; exact hcond (Or.inl (by omega))
        wp_if_destruct
        · exfalso; exact hcond (Or.inr (by have : sint.Z (W64 0) = 0 := rfl; omega))
        have hfo' := freeOk_writeback Hwf hp0 (by omega) (fun h => hcond (Or.inr h))
        bu_free (wbSt P st) hbg' hfo'
    · -- a put session: back at `relog P vd st`
      ihave ⟨Hv, Hbv, #Hthvd⟩ := batchViewQ_bView γ P st 1 vd $$ [$Hv $Hbv]
      ihave #Hrel := thinV_relog γ P vd st $$ Hthvd
      rw [decide_eq_false hp0]
      wp_auto
      wp_apply (hRLock γ P rt) $$ [$Hrg] as ⟨Hwl, Hrr⟩
      unfold wbTok
      icombine Ha Htok gives %Hle
      imod ownTokAuth_sub 1 γ.wb n $$ Ha Htok with Ha
      imod mono_nat_own_update (w + 1) (by omega) $$ Hmo with ⟨Hmo, #Hlb1⟩
      icases rtRes_wb_open γ P rt st.C st.R $$ [$Hrr $Hrvs] with ⟨HRB, %HRok, Hwb, Hrvs⟩
      have hbb := bgOk_bufBound HP Hwf Hbg
      wp_apply (hWB (wbOf t) st.W (rbufOf (baseOf rt)) st.R Hwf.1 Hwf.2.1 (fun i => hbb i)) $$ [$HW $HRB]
        as ⟨HW, HRB⟩
      have hver : uint.Z st.R.ver + 1 < 2 ^ 64 := by
        have := Hbg.1
        have : 0 ≤ uint.Z st.R.ver := by word
        omega
      have hbg' := bgOk_writeback Hbg Hle
      have hwf' := sessWf_writeback Hwf hp0
      have hsafe : safeRv P (st.C, writebackR st.W st.R) := hwf'.2.2.2.2.2.2.2.2.2.2.1
      icases fkHalf_rd γ P st (st.C, writebackR st.W st.R) (fun f w h => fkOkRvG_of (fkOkG_wb f w h)) $$ Hfkh
        with ⟨Hfkh, #Hfkr⟩
      ihave Hfkh := fkHalf_mono γ P (st' := wbSt P st) fkOkG_wb $$ Hfkh
      unfold batchViewQ
      icases Hv with ⟨%L0, Hv⟩
      by_cases hcond : (sint.Z P.limit ≤ sint.Z st.pend ∨ 0 < sint.Z st.ndel)
      · -- committed: the window opens at the exact new physical view, the commit's close moves it
        -- to `relog` (R11-2)
        imod (rtRes_wb_close γ P rt st.W st.C st.R vd L0 (relog P vd st) true Hwf.2.2.1 hver hsafe)
          $$ [$Hci $Hwb $HRB $Hrvs $Hv $Hbv $Hfkr] with ⟨Hrr, Hrvs, Hv, -⟩
        · simp only [↓reduceIte]; itrivial
        ihave Hv : batchViewQ γ P (wbSt P st) $$ [Hv]
        · unfold batchViewQ; rw [wbSt_C, wbSt_R]; iexists _; iexact Hv
        wp_apply (hRUnlock γ P rt) $$ [$Hwl $Hrr]
        ihave Hpc : thinV γ (sData P (wbSt P st).S) (relog P vd st) $$ []
        · rw [wbSt_S]; iexact Hrel
        wp_if_destruct
        · bu_commit true (relog P vd st)
          icases HQw $$ Hbv2 with ⟨HWv, HQ⟩
          bu_release
        wp_if_destruct
        · bu_commit true (relog P vd st)
          icases HQw $$ Hbv2 with ⟨HWv, HQ⟩
          bu_release
        exfalso
        rcases hcond with h | h
        · omega
        · exact Hif (by have : sint.Z (W64 0) = 0 := rfl; omega)
      · -- not committed: the write-back's close moves the view to `relog`
        have hfo' := freeOk_writeback Hwf hp0 (by omega) (fun h => hcond (Or.inr h))
        have hvf : vData P (st.C, writebackR st.W st.R) = sData P st.S := by
          rw [← wbSt_S P st, ← vData_free P (wbSt P st) hwf' hfo'.2.2.1 hfo'.2.2.2.1, wbSt_C, wbSt_R]
        imod (rtRes_wb_close γ P rt st.W st.C st.R vd L0 (relog P vd st) false Hwf.2.2.1 hver hsafe)
          $$ [$Hci $Hwb $HRB $Hrvs $Hv $Hbv $Hfkr] with ⟨Hrr, Hrvs, Hv, Hbvw⟩
        · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hvf]; iexact Hrel
        simp only [Bool.false_eq_true, ↓reduceIte]
        ihave Hv : batchViewQ γ P (wbSt P st) $$ [Hv]
        · unfold batchViewQ; rw [wbSt_C, wbSt_R]; iexists _; iexact Hv
        wp_apply (hRUnlock γ P rt) $$ [$Hwl $Hrr]
        wp_if_destruct
        · exfalso; exact hcond (Or.inl (by omega))
        wp_if_destruct
        · exfalso; exact hcond (Or.inr (by have : sint.Z (W64 0) = 0 := rfl; omega))
        icases HQw $$ Hbvw with ⟨HWv, HQ⟩
        bu_free (wbSt P st) hbg' hfo'

end proof

end EtcdGrove
end Perennial
