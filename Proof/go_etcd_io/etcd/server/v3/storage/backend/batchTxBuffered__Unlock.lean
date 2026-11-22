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
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvCommit
public import Proof.go_etcd_io.raft.v3.FrameH
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.UnlockBare
import all Proof.go_etcd_io.etcd.server.v3.storage.backend.TrackedLemmas
import all Proof.go_etcd_io.etcd.server.v3.storage.backend.ClaimedLemmas

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
    imod trkSide_conf (hG := hG) γ P $S _ Sc (fun n => bktOf st.S n) Rr Rr' E
      (fun n hn => (rvBkt_idle (($hb).2.2.2.2.2.2.2.2.2.2.1) (HScRB n hn) (($hf).2.2.2.2.2 n (HScRB n hn))).trans
        (by rw [wbSt_S])) $$ [$(frameH `Hhkd) $(frameH `HRr) $(frameH `Hcf)] with ⟨Hhkd, HRr⟩
    imod trkSide_idle (hG := hG) γ P $S _ Sp rp (fun n _ hRB => ($hf).2.2.2.2.2 n hRB)
      ($hb).2.2.2.2.2.2.2.2.2.2.1 ⊤ (by solve_ndisj) $$ [$(frameH `Hhkd) $(frameH `Hrb)]
      with ⟨Hhkd, Hin⟩
    imod rbPartR_idle (hG := hG) γ P $S _ _ rc (fun n _ hRB => ($hf).2.2.2.2.2 n hRB) ⊤ (by solve_ndisj) $$ [$(frameH `Hhkd) $(frameH `Hrc)] with ⟨Hhkd, Hinc⟩
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
        iframe #
        ipureintro
        exact $hb
      isplitr
      · ipureintro
        exact $hf
      iframe HWv HPk
    iapply HΦ
    iframe HQ HRr Hin Hinc
  ))

set_option hygiene false in
/-- `batchTx.Unlock` with nothing pending (A1.5: the claimed writes forgotten, `BSess.clrCw`, every
tracked bucket idle), then the postcondition. -/
local macro "bu_free0" hb:term:max hf:term:max : tactic => `(tactic| (
    imod trkSide_conf (hG := hG) γ P st _ Sc (fun n => bktOf st.S n) Rr Rr' E
      (fun n hn => rvBkt_idle (($hb).2.2.2.2.2.2.2.2.2.2.1) (HScRB n hn) (($hf).2.2.2.2.2 n (HScRB n hn)))
      $$ [$(frameH `Hhkd) $(frameH `HRr) $(frameH `Hcf)] with ⟨Hhkd, HRr⟩
    imod trkSide_idle (hG := hG) γ P st _ Sp rp (fun n _ hRB => ($hf).2.2.2.2.2 n hRB)
      ($hb).2.2.2.2.2.2.2.2.2.2.1 ⊤ (by solve_ndisj) $$ [$(frameH `Hhkd) $(frameH `Hrb)]
      with ⟨Hhkd, Hin⟩
    imod rbPartR_idle (hG := hG) γ P st _ _ rc (fun n _ hRB => ($hf).2.2.2.2.2 n hRB) ⊤ (by solve_ndisj) $$ [$(frameH `Hhkd) $(frameH `Hrc)] with ⟨Hhkd, Hinc⟩
    wp_apply (hBU γ P W Pk b t)
      $$ [$(frameH `Hown) Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu Hv Hrvs Ha Hmo Hus Hopn Hhkd Hfkh HWv HPk]
    · iframe #
      unfold batchFree
      ileft
      iexists st.clrCw, db
      isplitl [Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu]
      · iapply (show batchPhys (GF := GF) γ b t db st ⊢ batchPhys γ b t db st.clrCw from .rfl)
        unfold batchPhys
        iexists hk
        iframe
        iframe #
      isplitl [Hv Hrvs Ha Hmo Hus Hopn Hhkd Hfkh]
      · iapply batchGhostAt_clr γ P st true true (fun n hn => ($hf).2.2.2.2.2 n hn)
        unfold batchGhostAt
        iframe Hv
        iexists _, _, u0
        iframe
        iframe #
        ipureintro
        exact $hb
      isplitr
      · ipureintro
        exact $hf
      iframe HWv HPk
    iapply HΦ
    iframe HQ HRr Hin Hinc
  ))

set_option hygiene false in
/-- `commit` of the written-back batch (`vw`: whether a view update is owed, `L` the logical view
it comes back at; `Hpc` the commit's thinness premise), up to its outcome `Hpost` (both commit tests, with or without the view). -/
local macro "bu_commit" S:term:max vw:term:max L:term:max : tactic => `(tactic| (
    ihave #Hlb0 := backend.cntLb_zero (GF := GF) γ
    ihave #HaccC := rbAcc_mono (hG := hG) γ Sc (unlockOk P st) (fun n _ v => v = bktOf ($S).S n) Rr E
      (fun n o v _ h => Or.inl h) $$ Hacc
    wp_apply (hC γ P W Pk b t rt $S $vw false 2 0 iprop(True) iprop(True) $L true Sc Rr E 0 Q hE) $$ [Hown Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu Hv Hrvs Ha Hmo Hus Hopn Hhkd Hfkh HPk Hpc HRr HWc] as ⟨-, HRr, HPk, -, Hpost, Hcnt⟩
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
        · try simp only [↓reduceIte, Bool.false_eq_true]
          iframe Hv
          iexists n - 1, w + 1, u0
          iframe
          isplitl []
          · first | iexact HbrW2 | iexact Hbrw
          ipureintro
          exact hbg' false (fun h => by cases h)
        · ipureintro
          exact hwf'
      iframe HPk
      isplitr
      · ipureintro
        exact ⟨Hroom, rfl, fun _ i _ _ => bkOf_writebackW _ _ i, fun n _ => tkWb_idle_del _ n⟩
      isplitl [Hpc]
      · simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hpc
      isplitr
      · ipureintro; first | (intro h; cases h; done) | (intro _; exact ⟨rfl, Hdlr⟩)
      isplitr
      · ipureintro; rfl
      unfold payIn
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]
      isplitr
      · isplitr
        · ipureintro
          rfl
        iapply monoNatLbOwn_le 1 (by omega) $$ Hlb1
      isplitr
      · iapply commitReq_true
      isplitr
      · ipureintro; exact ⟨Hnd, Or.inr HcwWb⟩
      iframe HRr
      simp only [Bool.false_eq_true, ↓reduceIte]
      try iframe Hlb0
      try iexact HWc
    try simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hpost with ⟨%st2, %db2, Hown, Hph2, Hg2, %Hfin, Hbv2⟩
    icases Hcnt with ⟨-, HWc⟩
  ))

set_option hygiene false in
/-- `batchTx.Unlock` after a commit, then the postcondition. -/
local macro "bu_release" : tactic => `(tactic| (
    imod batchGhostAt_conf (hG := hG) γ P st2 true false Sc (fun n => bktOf st.S n) Rr Rr' E
      (fun n hn => ⟨HScRB n hn, Hfin.1.2.2.2.2.2 n (HScRB n hn),
        (bktOf_rb Hfin.2.2.2 (HScRB n hn)).trans (by simp [wbSt_S])⟩)
      $$ [$(frameH `Hg2) $(frameH `HRr) $(frameH `Hcf)] with ⟨Hg2, HRr⟩
    imod batchGhostAt_idle (hG := hG) γ P st2 _ Sp _ rp rc Hfin.1.2.2.2.2.2 ⊤ (by solve_ndisj) $$ [$(frameH `Hg2) $(frameH `Hrb) $(frameH `Hrc)]
      with ⟨Hg2, Hin, Hinc⟩
    wp_apply (hBU γ P W Pk b t) $$ [$(frameH `Hown) Hph2 Hg2 HWv HPk]
    · iframe #
      ileft
      iexists st2, db2
      iframe
      iframe #
      ipureintro
      exact Hfin.1
    iapply HΦ
    iframe HQ HRr Hin Hinc
  ))

/-- `Unlock` handed no part of the tracked buckets, in a claimed session (the session's code; A1.5: the
claimed writes among `Sc`, the client's accessor run at the write-back and at the commit). -/
private theorem unlock_coreC
    (hRLock : backend.readTx.Lock.spec (GF := GF) (hG := hG))
    (hWB : backend.txWriteBuffer.writeback.spec (GF := GF) (hG := hG))
    (hRUnlock : backend.readTx.Unlock.spec (GF := GF) (hG := hG))
    (hC : backend.batchTxBuffered.commit.spec (GF := GF) (hG := hG))
    (hBU : backend.batchTx.Unlock.spec (GF := GF) (hG := hG)) :
    ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess) (Q : IProp GF)
      (Sc : List GoString) (Rr Rr' : IProp GF) (E : CoPset) (Sp : GoString → Prop) (rp rc : GMap GoString BktData),
    ↑rbClaimN ⊆ E → st.cnt.hw = false → sint.Z st.pend + P.hookMax < 2 ^ 58 → Sc.Nodup →
    (∀ n, st.cw n = true → n ∈ Sc) → (∀ n, n ∈ Sc → P.RB n = true) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗
        bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st true ∗ wbTok γ ∗ Rr ∗ rbAcc γ Sc (unlockOk P st) Rr E ∗
        rbConf γ Sc (fun n => bktOf st.S n) Rr Rr' E ∗ rbPart γ Sp rp ∗ rbPartR γ (fun n => n ∈ Sc) rc ∗
        ((thinV γ (sData P st.S) (vData P (st.C, st.R)) ∗
           ⌜∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st.W.bks i = []⌝ ∗ W ∗ Pk ∗ Q) ∨
         (∃ vd : VData, ⌜sbKept P st⌝ ∗ bView γ 1 vd ∗ Pk ∗ (bView γ 1 (relog P vd st) -∗ W ∗ Q))) }}
      (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"Unlock")) (Val #()))
    {{ RET #(); Q ∗ Rr' ∗ rbOwnIn γ Sp rp ∗ rbOwnInR γ (fun n => n ∈ Sc) rc }} := by
  intro γ P W Pk b t st Q Sc Rr Rr' E Sp rp rc hE Hhw Hroom Hnd HcwS HScRB
  wp_start as ⟨#Hb, #Ht, Hl, Htok, HRr, #Hacc, Hcf, Hrb, Hrc, Hcase⟩
  icases isBackend_bt γ P W Pk b t $$ [Hb Ht] with
    ⟨%db0, %lg, %h, #Hbe, #Hlg, #Hlgn, #Hlim, #Hh, #Hhs, #Hm, #Hdb0, %HP⟩
  · iframe #
  icases isBackend_b γ P W Pk b $$ Hb with
    ⟨%t2, %rt, %db1, %lg2, #-, #Hrt, #-, #-, #Hmi, #-, #-, #Hrg, #-, #-, #Hci, %-⟩
  ihave Hl := batchLocked_W γ P b st true $$ Hl
  unfold batchLockedW batchGhostW
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hl with ⟨%t1, %db, #Ht1, Hown, Hph, ⟨Hv, %n, %w, %u0, Hrvs, Ha, Hmo, Hus, Hopn, Hhkd, Hfkh,
    #Hbr, %Hbg⟩, %Hwf⟩
  ihave #Hbrw := bufRc_wbSt P st $$ Hbr
  icombine Ht Ht1 gives %Heq1
  subst Heq1
  -- (A1.5) the write-back keeps a claimed write only on a bucket it leaves deleted from
  have HcwWb : ∀ n, (wbSt P st).cw n = true → n ∈ Sc := fun n h => by
    rw [wbSt_cw] at h
    exact HcwS n (Bool.and_eq_true_iff.1 h).1
  have HclWb : ∀ n, st.cw n = true → (wbSt P st).tk n = .idle ∨ (wbSt P st).cw n = true := fun n h => by
    show tkWb st.tk n = .idle ∨ (wbSt P st).cw n = true
    rw [wbSt_cw]
    by_cases e : tkWb st.tk n = .idle
    · exact Or.inl e
    · right; simp [h, e]
  -- no claimed write is left once nothing is deleted
  have HcwWb0 : st.ndel = W64 0 → ∀ n, (wbSt P st).cw n = false := fun hn0 n => by
    rw [wbSt_cw]
    cases h : st.cw n
    · rfl
    · simp [tkWb_idle_of_ndel0 Hbg.2.2.2.2.2.2.2.2.2.2.1 hn0 n (HScRB n (HcwS n h))]
  unfold batchPhys
  icases Hph with ⟨%hk, Htxf, Hpend, Hdel, HW, Hhkf, Hhk, Hdb, Hwtx, #Htxdb, Hmu⟩
  wp_auto
  by_cases hp0 : st.pend = W64 0
  · icases Hcase with (⟨#Hth, %Hnw, HWv, HPk, HQ⟩ | ⟨%vd, %Hkept, Hbv, HPk, HQw⟩)
    · rw [decide_eq_true hp0]
      wp_auto
      obtain ⟨hfo, hbg⟩ := free_of_pend0 HP Hwf Hbg hp0 Hhw
      bu_free0 hbg hfo
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
      bu_free0 hbg hfo
  · icases Hcase with (⟨#Hth, %Hnw, HWv, HPk, HQ⟩ | ⟨%vd, %Hkept, Hbv, HPk, HQw⟩)
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
      ihave %hbb := bufRc_bufBound st $$ Hbr
      wp_apply (hWB (wbOf t) st.W (rbufOf (backend.baseOf rt)) st.R Hwf.1 Hwf.2.1 (fun i => hbb i)) $$ [$HW $HRB]
        as ⟨HW, HRB⟩
      have hver : uint.Z st.R.ver + 1 < 2 ^ 64 := by
        have := Hbg.1
        have : 0 ≤ uint.Z st.R.ver := by word
        omega
      have hbg' := bgOk_writeback Hbg Hle
      have hwf' := sessWf_writeback Hwf hp0
      have hsafe : safeRv P (st.C, writebackR st.W st.R) := hwf'.2.2.2.2.2.2.2.2.2.2.1.1
      icases fkHalf_rd γ P st (st.C, writebackR st.W st.R) (fun f w h => fkOkRvG_of (fkOkG_wb f w h)) $$ Hfkh
        with ⟨Hfkh, #Hfkr⟩
      ihave Hfkh := fkHalf_mono γ P (st' := wbSt P st) fkOkG_wb rfl rfl $$ Hfkh
      have hsame := vData_writeback_same P st.C st.W st.R Hnw
      ihave Hupd := trkSide_updR γ P st (wbSt P st) (st.C, st.R) (st.C, writebackR st.W st.R) true true Sc
        (unlockOk P st) Rr E hE Hnd rfl rfl rfl
        (fun n hn hi _ => ⟨by simp [wbSt, tkWb, hi],
          (rvBkt_wb_keep Hbg.2.2.2.2.2.2.2.2.2.2.1 hn (Or.inl hi)).symm⟩) HclWb (fun n _ hi => by simp [wbSt, tkWb, hi]) HcwS (fun h => by cases h)
        (unlockOk_wb Hbg.2.2.2.2.2.2.2.2.2.2.1) $$ [$Hhkd $HRr $Hacc]
      imod (rtRes_wb_close_same γ P rt st.W st.C st.R (iprop(trkSide γ P (wbSt P st) true ∗ Rr)) Hwf.2.2.1 hver hsame
        hsafe (rbClean_writeback Hnw)) $$ [$Hci $Hwb $HRB $Hrvs $Hfkr $Hupd]
        with ⟨Hrr, Hrvs, ⟨Hhkd, HRr⟩⟩
      ihave Hv : batchViewQ γ P (wbSt P st) $$ [Hv]
      · unfold batchViewQ; rw [wbSt_C, wbSt_R, hsame]
        icases Hv with ⟨%L, Hq, %Hd⟩
        iexists L; iframe Hq; ipureintro
        exact dlsW_step (st := st) (st' := wbSt P st) (dlsS_congr (by rw [wbSt_S]) rfl)
          (dlsOk_congr (by rw [wbSt_S]) rfl) rfl (by simp [wbSt, Hhw]) Hd
      wp_apply (hRUnlock γ P rt) $$ [$Hwl $Hrr]
      by_cases hcond : (sint.Z P.limit ≤ sint.Z st.pend ∨ 0 < sint.Z st.ndel)
      · ihave Hpc : thinV γ (sData P (wbSt P st).S) (vData P ((wbSt P st).C, (wbSt P st).R)) $$ []
        · rw [wbSt_S, wbSt_C, wbSt_R, hsame]
          iexact Hth
        wp_if_destruct
        · ihave HWc : W $$ [HWv]
          · iexact HWv
          bu_commit (wbSt P st) false (vData P (st.C, st.R))
          ihave HWv : W $$ [HWc]
          · try simp only [Bool.false_eq_true, ↓reduceIte]
            iexact HWc
          bu_release
        wp_if_destruct
        · ihave HWc : W $$ [HWv]
          · iexact HWv
          bu_commit (wbSt P st) false (vData P (st.C, st.R))
          ihave HWv : W $$ [HWc]
          · try simp only [Bool.false_eq_true, ↓reduceIte]
            iexact HWc
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
          Hbg.2.2.2.2.2.2.2.2.2.2.1
        ihave Hhkd := trkSide_mode γ P (wbSt P st) true false (fun _ _ _ => HcwWb0 hfo'.2.2.1) $$ Hhkd
        bu_free (wbSt P st) (hbg' true (fun _ => tkWb_idle_of_ndel0 Hbg.2.2.2.2.2.2.2.2.2.2.1 hfo'.2.2.1)) hfo'
    · -- a put session: back at `relog P vd st`
      ihave ⟨Hv, Hbv, %Hdvw⟩ := batchViewQ_bView_dl γ P st 1 vd $$ [$Hv $Hbv]
      have Hdvd : dlsOk P st vd := Hdvw.2.1 (Hdvw.2.2 Hhw)
      -- the commit window (`win`) and the session's state agree with the logical view `relog`
      have Hdlr : dlsOk P ({ wbSt P st with win := true }) (relog P vd st) :=
        dlsOk_congr (by simp only [wbSt_S]) rfl (dlsOk_relog Hkept Hdvd)
      have Hdlr0 : dlsW P (wbSt P st) (relog P vd st) :=
        ⟨dlsS_congr (by rw [wbSt_S]) rfl Hdvw.1,
          fun _ => dlsOk_congr (by rw [wbSt_S]) rfl (dlsOk_relog Hkept Hdvd),
          fun _ => Hdvw.2.2 Hhw⟩
      have HdlS : dlsS P ({ wbSt P st with win := true }) :=
        dlsS_congr (by simp only [wbSt_S]) rfl Hdvw.1
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
      ihave %hbb := bufRc_bufBound st $$ Hbr
      wp_apply (hWB (wbOf t) st.W (rbufOf (backend.baseOf rt)) st.R Hwf.1 Hwf.2.1 (fun i => hbb i)) $$ [$HW $HRB]
        as ⟨HW, HRB⟩
      have hver : uint.Z st.R.ver + 1 < 2 ^ 64 := by
        have := Hbg.1
        have : 0 ≤ uint.Z st.R.ver := by word
        omega
      have hbg' := bgOk_writeback Hbg Hle
      have hwf' := sessWf_writeback Hwf hp0
      have hsafe : safeRv P (st.C, writebackR st.W st.R) := hwf'.2.2.2.2.2.2.2.2.2.2.1.1
      icases fkHalf_rd γ P st (st.C, writebackR st.W st.R) (fun f w h => fkOkRvG_of (fkOkG_wb f w h)) $$ Hfkh
        with ⟨Hfkh, #Hfkr⟩
      ihave Hfkh := fkHalf_mono γ P (st' := wbSt P st) fkOkG_wb rfl rfl $$ Hfkh
      unfold batchViewQ
      icases Hv with ⟨%L0, Hv, %Hd0⟩
      by_cases hcond : (sint.Z P.limit ≤ sint.Z st.pend ∨ 0 < sint.Z st.ndel)
      · -- committed: the window opens at the exact new physical view, the commit's close moves it
        -- to `relog` (R11-2)
        ihave Hupd := trkSide_updR γ P st (wbSt P st) (st.C, st.R) (st.C, writebackR st.W st.R) true true Sc
          (unlockOk P st) Rr E hE Hnd rfl rfl rfl
          (fun n hn hi _ => ⟨by simp [wbSt, tkWb, hi],
            (rvBkt_wb_keep Hbg.2.2.2.2.2.2.2.2.2.2.1 hn (Or.inl hi)).symm⟩) HclWb (fun n _ hi => by simp [wbSt, tkWb, hi]) HcwS (fun h => by cases h)
          (unlockOk_wb Hbg.2.2.2.2.2.2.2.2.2.2.1) $$ [$Hhkd $HRr $Hacc]
        imod (rtRes_wb_close γ P rt st.W st.C st.R vd L0 (relog P vd st) true
          (iprop(trkSide γ P (wbSt P st) true ∗ Rr)) Hwf.2.2.1 hver hsafe)
          $$ [$Hci $Hwb $HRB $Hrvs $Hv $Hbv $Hfkr $Hupd] with ⟨Hrr, Hrvs, ⟨Hhkd, HRr⟩, Hv, -⟩
        · simp only [↓reduceIte]; itrivial
        ihave Hhkd := trkSide_congr γ P (wbSt P st) ({ wbSt P st with win := true }) rfl rfl rfl
          (fun _ _ => rfl) rfl true (fun h => h) $$ Hhkd
        ihave Hv : batchViewQ0 γ P ({ wbSt P st with win := true }) $$ [Hv]
        · unfold batchViewQ0; simp only [wbSt_C, wbSt_R]; iexists _; iframe Hv; ipureintro
          exact HdlS
        wp_apply (hRUnlock γ P rt) $$ [$Hwl $Hrr]
        ihave Hpc : thinV γ (sData P ({ wbSt P st with win := true }).S) (relog P vd st) $$ []
        · simp only [wbSt_S]; iexact Hrel
        ihave Hfkh : fkHalf γ P ({ wbSt P st with win := true }) $$ [Hfkh]
        · iapply fkHalf_mono γ P (st := wbSt P st) (st' := { wbSt P st with win := true })
            (fun _ _ h => h) rfl rfl
          iexact Hfkh
        wp_if_destruct
        · ihave HWc : iprop(bView γ 1 (relog P vd st) -∗ W ∗ Q) $$ [HQw]
          · iexact HQw
          have hbrW2 : bufRc (GF := GF) (wbSt P st) ⊢ bufRc { C := st.C, S := st.S, R := writebackR st.W st.R, W := writebackW st.W st.R, pend := st.pend, ndel := st.ndel, tx := st.tx, cnt := (wbSt P st).cnt, dl := (wbSt P st).dl, win := true, tk := (wbSt P st).tk, cw := (wbSt P st).cw } :=
            bufRc_congr rfl rfl
          ihave #HbrW2 := hbrW2 $$ Hbrw
          bu_commit ({ wbSt P st with win := true }) true (relog P vd st)
          icases HWc $$ Hbv2 with ⟨HWv, HQ⟩
          bu_release
        wp_if_destruct
        · ihave HWc : iprop(bView γ 1 (relog P vd st) -∗ W ∗ Q) $$ [HQw]
          · iexact HQw
          have hbrW2 : bufRc (GF := GF) (wbSt P st) ⊢ bufRc { C := st.C, S := st.S, R := writebackR st.W st.R, W := writebackW st.W st.R, pend := st.pend, ndel := st.ndel, tx := st.tx, cnt := (wbSt P st).cnt, dl := (wbSt P st).dl, win := true, tk := (wbSt P st).tk, cw := (wbSt P st).cw } :=
            bufRc_congr rfl rfl
          ihave #HbrW2 := hbrW2 $$ Hbrw
          bu_commit ({ wbSt P st with win := true }) true (relog P vd st)
          icases HWc $$ Hbv2 with ⟨HWv, HQ⟩
          bu_release
        exfalso
        rcases hcond with h | h
        · omega
        · exact Hif (by have : sint.Z (W64 0) = 0 := rfl; omega)
      · -- not committed: the write-back's close moves the view to `relog`
        have hfo' := freeOk_writeback Hwf hp0 (by omega) (fun h => hcond (Or.inr h))
          Hbg.2.2.2.2.2.2.2.2.2.2.1
        have hvf : vData P (st.C, writebackR st.W st.R) = sData P st.S := by
          rw [← wbSt_S P st, ← vData_free P (wbSt P st) hwf' hfo'.2.2.1 hfo'.2.2.2.1, wbSt_C, wbSt_R]
        ihave Hupd := trkSide_updR γ P st (wbSt P st) (st.C, st.R) (st.C, writebackR st.W st.R) true true Sc
          (unlockOk P st) Rr E hE Hnd rfl rfl rfl
          (fun n hn hi _ => ⟨by simp [wbSt, tkWb, hi],
            (rvBkt_wb_keep Hbg.2.2.2.2.2.2.2.2.2.2.1 hn (Or.inl hi)).symm⟩) HclWb (fun n _ hi => by simp [wbSt, tkWb, hi]) HcwS (fun h => by cases h)
          (unlockOk_wb Hbg.2.2.2.2.2.2.2.2.2.2.1) $$ [$Hhkd $HRr $Hacc]
        imod (rtRes_wb_close γ P rt st.W st.C st.R vd L0 (relog P vd st) false
          (iprop(trkSide γ P (wbSt P st) true ∗ Rr)) Hwf.2.2.1 hver hsafe)
          $$ [$Hci $Hwb $HRB $Hrvs $Hv $Hbv $Hfkr $Hupd] with ⟨Hrr, Hrvs, ⟨Hhkd, HRr⟩, Hv, Hbvw⟩
        · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hvf]; iexact Hrel
        simp only [Bool.false_eq_true, ↓reduceIte]
        ihave Hv : batchViewQ γ P (wbSt P st) $$ [Hv]
        · unfold batchViewQ; rw [wbSt_C, wbSt_R]; iexists _; iframe Hv; ipureintro
          exact Hdlr0
        wp_apply (hRUnlock γ P rt) $$ [$Hwl $Hrr]
        wp_if_destruct
        · exfalso; exact hcond (Or.inl (by omega))
        wp_if_destruct
        · exfalso; exact hcond (Or.inr (by have : sint.Z (W64 0) = 0 := rfl; omega))
        icases HQw $$ Hbvw with ⟨HWv, HQ⟩
        ihave Hhkd := trkSide_mode γ P (wbSt P st) true false (fun _ _ _ => HcwWb0 hfo'.2.2.1) $$ Hhkd
        bu_free (wbSt P st) (hbg' true (fun _ => tkWb_idle_of_ndel0 Hbg.2.2.2.2.2.2.2.2.2.2.1 hfo'.2.2.1)) hfo'

/-- **`Unlock`** (claimed buckets: A1.5; the client-facing statement is its corollary `Unlock.spec_free`). -/
theorem backend.batchTxBuffered.Unlock.wp_proof
    (hRLock : backend.readTx.Lock.spec (GF := GF) (hG := hG))
    (hWB : backend.txWriteBuffer.writeback.spec (GF := GF) (hG := hG))
    (hRUnlock : backend.readTx.Unlock.spec (GF := GF) (hG := hG))
    (hC : backend.batchTxBuffered.commit.spec (GF := GF) (hG := hG))
    (hBU : backend.batchTx.Unlock.spec (GF := GF) (hG := hG)) :
    backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b t st Q S r Sc rc Rr Rr' E hE Hhw Hroom Hnd HcwS
  iintro %Φ ⟨#Hpkg, #Hb, #Ht, Hl, Htok, Hrb, Hrc, HRr, #Hacc, Hcf, Hcase⟩ HΦ
  icases batchLocked_rbPartR_RB γ P b st true _ rc $$ [$Hl $Hrc] with ⟨Hl, Hrc, %HScRB⟩
  iapply (unlock_coreC hRLock hWB hRUnlock hC hBU γ P W Pk b t st Q Sc Rr Rr' E S r rc hE Hhw Hroom Hnd HcwS HScRB) $$ %Φ
    [Hl Htok HRr Hcf Hrb Hrc Hcase]
  · iframe Hl Htok HRr Hcf Hrb Hrc Hcase; iframe #
  inext
  iintro ⟨HQ, HRr, Hin, Hinc⟩
  iapply HΦ
  iframe HQ Hin Hinc HRr

end proof

end EtcdGrove
end Perennial
