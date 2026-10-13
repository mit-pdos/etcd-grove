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

theorem backend.batchTxBuffered.Unlock.wp_proof
    (hRLock : backend.readTx.Lock.spec (GF := GF) (hG := hG))
    (hWB : backend.txWriteBuffer.writeback.spec (GF := GF) (hG := hG))
    (hRUnlock : backend.readTx.Unlock.spec (GF := GF) (hG := hG))
    (hC : backend.batchTxBuffered.commit.spec (GF := GF) (hG := hG))
    (hBU : backend.batchTx.Unlock.spec (GF := GF) (hG := hG)) :
    backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b t st Q
  wp_start as ⟨#Hb, #Ht, Hl, Htok, Hcase⟩
  icases isBackend_bt γ P W Pk b t $$ [Hb Ht] with
    ⟨%db0, %lg, %h, #Hbe, #Hlg, %Hlgn, #Hlim, #Hh, #Hhs, #Hm, #Hdb0, %HP⟩
  · iframe #
  icases isBackend_b γ P W Pk b $$ Hb with
    ⟨%t2, %rt, %db1, %lg2, #-, #Hrt, #-, %-, #Hmi, #-, #-, #Hrg, #-, #-, #Hci, %-⟩
  ihave Hl := batchLocked_W γ P b st $$ Hl
  unfold batchLockedW batchGhostW
  icases Hl with ⟨%t1, %db, #Ht1, Hown, Hph, ⟨Hv, %n, %w, %u0, Hrvs, Ha, Hmo, Hus, Hopn, %Hbg⟩, %Hwf⟩
  icombine Ht Ht1 gives %Heq1
  subst Heq1
  unfold batchPhys
  icases Hph with ⟨%hk, Htxf, Hpend, Hdel, HW, Hhkf, Hhk, Hdb, Hwtx, #Htxdb, Hmu⟩
  wp_auto
  by_cases hp0 : st.pend = W64 0
  · icases Hcase with (⟨%Hvs, HWv, HPk, HQ⟩ | ⟨%vd, Hbv, HPk, HQw⟩)
    · rw [decide_eq_true hp0]
      wp_auto
      obtain ⟨hfo, hbg⟩ := free_of_pend0 HP Hwf Hbg hp0
      wp_apply (hBU γ P W Pk b t) $$ [$Hown Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu Hv Hrvs Ha Hmo Hus Hopn HWv HPk]
      · iframe #
        unfold batchFree batchPhys batchGhostAt
        ileft
        iexists st, db
        try simp only [wbSt_C, wbSt_S, wbSt_R, wbSt_W, wbSt_pend, wbSt_ndel, wbSt_tx]
        isplitl [Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu]
        · iexists hk
          iframe
          iframe #
        isplitl [Hv Hrvs Ha Hmo Hus Hopn]
        · iframe Hv
          iexists n, w, u0
          iframe
          ipureintro
          exact hbg
        isplitr
        · ipureintro
          exact hfo
        iframe HWv HPk
      iapply HΦ
      iexact HQ
    · unfold bView
      icases Hbv with ⟨Hbv1, Hcvw⟩
      icombine Hv Hbv1 gives % ⟨_, Hvd⟩
      rw [decide_eq_true hp0]
      wp_auto
      obtain ⟨hfo, hbg⟩ := free_of_pend0 HP Hwf Hbg hp0
      have hvf := vData_free P st Hwf hfo.2.2.1 hfo.2.2.2
      ihave Hbv : iprop(ghostVar γ.view (1 : Qp).half (sData P st.S) ∗ ghostVar γ.cvw (1 : Qp).half ())
        $$ [Hbv1 Hcvw]
      · rw [← hvf, Hvd]
        iframe
      icases HQw $$ Hbv with ⟨HWv, HQ⟩
      wp_apply (hBU γ P W Pk b t) $$ [$Hown Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu Hv Hrvs Ha Hmo Hus Hopn HWv HPk]
      · iframe #
        unfold batchFree batchPhys batchGhostAt
        ileft
        iexists st, db
        try simp only [wbSt_C, wbSt_S, wbSt_R, wbSt_W, wbSt_pend, wbSt_ndel, wbSt_tx]
        isplitl [Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu]
        · iexists hk
          iframe
          iframe #
        isplitl [Hv Hrvs Ha Hmo Hus Hopn]
        · iframe Hv
          iexists n, w, u0
          iframe
          ipureintro
          exact hbg
        isplitr
        · ipureintro
          exact hfo
        iframe HWv HPk
      iapply HΦ
      iexact HQ
  · icases Hcase with (⟨%Hvs, HWv, HPk, HQ⟩ | ⟨%vd, Hbv, HPk, HQw⟩)
    · rw [decide_eq_false hp0]
      wp_auto
      wp_apply (hRLock γ P rt) $$ [$Hrg] as ⟨Hwl, Hrr⟩
      unfold wbTok
      icombine Ha Htok gives %Hle
      imod ownTokAuth_sub 1 γ.wb n $$ Ha Htok with Ha
      imod mono_nat_own_update (w + 1) (by omega) $$ Hmo with ⟨Hmo, -⟩
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
      have hsame := vData_writeback_same P st.C st.W st.R Hvs.2
      have hvs' : vData P ((wbSt P st).C, (wbSt P st).R) = sData P (wbSt P st).S := by
        rw [wbSt_C, wbSt_R, wbSt_S, hsame]
        exact Hvs.1
      imod (rtRes_wb_close_same γ P rt st.W st.C st.R Hwf.2.2.1 hver hsame hsafe) $$ [$Hci $Hwb $HRB $Hrvs]
        with ⟨Hrr, Hrvs⟩
      ihave Hv : ghostVar γ.view (1 : Qp).half.half (vData P (st.C, writebackR st.W st.R)) $$ [Hv]
      · rw [hsame]; iexact Hv
      wp_apply (hRUnlock γ P rt) $$ [$Hwl $Hrr]
      by_cases hcond : (sint.Z P.limit ≤ sint.Z st.pend ∨ 0 < sint.Z st.ndel)
      · wp_if_destruct
        · wp_apply (hC γ P W Pk b t rt (wbSt P st) false false 2 0) $$ [Hown Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu Hv Hrvs Ha Hmo Hus Hopn HPk] as ⟨HPk, -, Hpost⟩
          · iframe #
            unfold batchLockedW batchGhostW batchPhys
            isplitl [Hown Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu Hv Hrvs Ha Hmo Hus Hopn]
            · iexists t, db
              try simp only [wbSt_C, wbSt_S, wbSt_R, wbSt_W, wbSt_pend, wbSt_ndel, wbSt_tx]
              iframe Ht Hown
              isplitl [Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu]
              · iexists hk
                iframe
                iframe #
              isplitl [Hv Hrvs Ha Hmo Hus Hopn]
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
              exact ⟨rfl, fun _ i _ _ => bkOf_writebackW _ _ i, fun _ => hvs'⟩
            unfold payIn
            rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]
            ipureintro
            rfl
          try simp only [Bool.false_eq_true, ↓reduceIte]
          icases Hpost with ⟨%st2, %db2, Hown, Hph2, Hg2, %Hfin, Hbv2⟩
          wp_apply (hBU γ P W Pk b t) $$ [$Hown Hph2 Hg2 HWv HPk]
          · iframe #
            ileft
            iexists st2, db2
            iframe
            ipureintro
            exact Hfin.1
          iapply HΦ
          iexact HQ
        wp_if_destruct
        · wp_apply (hC γ P W Pk b t rt (wbSt P st) false false 2 0) $$ [Hown Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu Hv Hrvs Ha Hmo Hus Hopn HPk] as ⟨HPk, -, Hpost⟩
          · iframe #
            unfold batchLockedW batchGhostW batchPhys
            isplitl [Hown Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu Hv Hrvs Ha Hmo Hus Hopn]
            · iexists t, db
              try simp only [wbSt_C, wbSt_S, wbSt_R, wbSt_W, wbSt_pend, wbSt_ndel, wbSt_tx]
              iframe Ht Hown
              isplitl [Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu]
              · iexists hk
                iframe
                iframe #
              isplitl [Hv Hrvs Ha Hmo Hus Hopn]
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
              exact ⟨rfl, fun _ i _ _ => bkOf_writebackW _ _ i, fun _ => hvs'⟩
            unfold payIn
            rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]
            ipureintro
            rfl
          try simp only [Bool.false_eq_true, ↓reduceIte]
          icases Hpost with ⟨%st2, %db2, Hown, Hph2, Hg2, %Hfin, Hbv2⟩
          wp_apply (hBU γ P W Pk b t) $$ [$Hown Hph2 Hg2 HWv HPk]
          · iframe #
            ileft
            iexists st2, db2
            iframe
            ipureintro
            exact Hfin.1
          iapply HΦ
          iexact HQ
        exfalso
        rcases hcond with h | h
        · omega
        · exact Hif (by have : sint.Z (W64 0) = 0 := rfl; omega)
      · wp_if_destruct
        · exfalso; exact hcond (Or.inl (by omega))
        wp_if_destruct
        · exfalso; exact hcond (Or.inr (by have : sint.Z (W64 0) = 0 := rfl; omega))
        have hfo' := freeOk_writeback Hwf hp0 (by omega) (fun h => hcond (Or.inr h))
        wp_apply (hBU γ P W Pk b t) $$ [$Hown Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu Hv Hrvs Ha Hmo Hus Hopn HWv HPk]
        · iframe #
          unfold batchFree batchPhys batchGhostAt
          ileft
          iexists (wbSt P st), db
          try simp only [wbSt_C, wbSt_S, wbSt_R, wbSt_W, wbSt_pend, wbSt_ndel, wbSt_tx]
          isplitl [Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu]
          · iexists hk
            iframe
            iframe #
          isplitl [Hv Hrvs Ha Hmo Hus Hopn]
          · iframe Hv
            iexists n - 1, w + 1, u0
            iframe
            ipureintro
            exact hbg'
          isplitr
          · ipureintro
            exact hfo'
          iframe HWv HPk
        iapply HΦ
        iexact HQ
    · rw [decide_eq_false hp0]
      wp_auto
      wp_apply (hRLock γ P rt) $$ [$Hrg] as ⟨Hwl, Hrr⟩
      unfold wbTok
      icombine Ha Htok gives %Hle
      imod ownTokAuth_sub 1 γ.wb n $$ Ha Htok with Ha
      imod mono_nat_own_update (w + 1) (by omega) $$ Hmo with ⟨Hmo, -⟩
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
      by_cases hcond : (sint.Z P.limit ≤ sint.Z st.pend ∨ 0 < sint.Z st.ndel)
      · imod (rtRes_wb_close γ P rt st.W st.C st.R vd true Hwf.2.2.1 hver hsafe) $$ [$Hci $Hwb $HRB $Hrvs $Hv $Hbv]
          with ⟨Hrr, Hrvs, Hv, -⟩
        wp_apply (hRUnlock γ P rt) $$ [$Hwl $Hrr]
        wp_if_destruct
        · wp_apply (hC γ P W Pk b t rt (wbSt P st) true false 2 0) $$ [Hown Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu Hv Hrvs Ha Hmo Hus Hopn HPk] as ⟨HPk, -, Hpost⟩
          · iframe #
            unfold batchLockedW batchGhostW batchPhys
            isplitl [Hown Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu Hv Hrvs Ha Hmo Hus Hopn]
            · iexists t, db
              try simp only [wbSt_C, wbSt_S, wbSt_R, wbSt_W, wbSt_pend, wbSt_ndel, wbSt_tx]
              iframe Ht Hown
              isplitl [Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu]
              · iexists hk
                iframe
                iframe #
              isplitl [Hv Hrvs Ha Hmo Hus Hopn]
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
              exact ⟨rfl, fun _ i _ _ => bkOf_writebackW _ _ i, fun h => absurd h (by decide)⟩
            unfold payIn
            rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]
            ipureintro
            rfl
          try simp only [Bool.false_eq_true, ↓reduceIte]
          icases Hpost with ⟨%st2, %db2, Hown, Hph2, Hg2, %Hfin, Hbv2⟩
          ihave Hbv2 : bView γ 1 (sData P st.S) $$ [Hbv2]
          · rw [← Hfin.2.1]
            iexact Hbv2
          icases HQw $$ Hbv2 with ⟨HWv, HQ⟩
          wp_apply (hBU γ P W Pk b t) $$ [$Hown Hph2 Hg2 HWv HPk]
          · iframe #
            ileft
            iexists st2, db2
            iframe
            ipureintro
            exact Hfin.1
          iapply HΦ
          iexact HQ
        wp_if_destruct
        · wp_apply (hC γ P W Pk b t rt (wbSt P st) true false 2 0) $$ [Hown Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu Hv Hrvs Ha Hmo Hus Hopn HPk] as ⟨HPk, -, Hpost⟩
          · iframe #
            unfold batchLockedW batchGhostW batchPhys
            isplitl [Hown Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu Hv Hrvs Ha Hmo Hus Hopn]
            · iexists t, db
              try simp only [wbSt_C, wbSt_S, wbSt_R, wbSt_W, wbSt_pend, wbSt_ndel, wbSt_tx]
              iframe Ht Hown
              isplitl [Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu]
              · iexists hk
                iframe
                iframe #
              isplitl [Hv Hrvs Ha Hmo Hus Hopn]
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
              exact ⟨rfl, fun _ i _ _ => bkOf_writebackW _ _ i, fun h => absurd h (by decide)⟩
            unfold payIn
            rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]
            ipureintro
            rfl
          try simp only [Bool.false_eq_true, ↓reduceIte]
          icases Hpost with ⟨%st2, %db2, Hown, Hph2, Hg2, %Hfin, Hbv2⟩
          ihave Hbv2 : bView γ 1 (sData P st.S) $$ [Hbv2]
          · rw [← Hfin.2.1]
            iexact Hbv2
          icases HQw $$ Hbv2 with ⟨HWv, HQ⟩
          wp_apply (hBU γ P W Pk b t) $$ [$Hown Hph2 Hg2 HWv HPk]
          · iframe #
            ileft
            iexists st2, db2
            iframe
            ipureintro
            exact Hfin.1
          iapply HΦ
          iexact HQ
        exfalso
        rcases hcond with h | h
        · omega
        · exact Hif (by have : sint.Z (W64 0) = 0 := rfl; omega)
      · imod (rtRes_wb_close γ P rt st.W st.C st.R vd false Hwf.2.2.1 hver hsafe) $$ [$Hci $Hwb $HRB $Hrvs $Hv $Hbv]
          with ⟨Hrr, Hrvs, Hv, Hbvw⟩
        wp_apply (hRUnlock γ P rt) $$ [$Hwl $Hrr]
        wp_if_destruct
        · exfalso; exact hcond (Or.inl (by omega))
        wp_if_destruct
        · exfalso; exact hcond (Or.inr (by have : sint.Z (W64 0) = 0 := rfl; omega))
        have hfo' := freeOk_writeback Hwf hp0 (by omega) (fun h => hcond (Or.inr h))
        ihave Hbvw : bView γ 1 (sData P st.S) $$ [Hbvw]
        · rw [← wbSt_S P st, ← vData_free P (wbSt P st) hwf' hfo'.2.2.1 hfo'.2.2.2, wbSt_C, wbSt_R]
          iexact Hbvw
        icases HQw $$ Hbvw with ⟨HWv, HQ⟩
        wp_apply (hBU γ P W Pk b t) $$ [$Hown Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu Hv Hrvs Ha Hmo Hus Hopn HWv HPk]
        · iframe #
          unfold batchFree batchPhys batchGhostAt
          ileft
          iexists (wbSt P st), db
          try simp only [wbSt_C, wbSt_S, wbSt_R, wbSt_W, wbSt_pend, wbSt_ndel, wbSt_tx]
          isplitl [Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu]
          · iexists hk
            iframe
            iframe #
          isplitl [Hv Hrvs Ha Hmo Hus Hopn]
          · iframe Hv
            iexists n - 1, w + 1, u0
            iframe
            ipureintro
            exact hbg'
          isplitr
          · ipureintro
            exact hfo'
          iframe HWv HPk
        iapply HΦ
        iexact HQ

end proof

end EtcdGrove
end Perennial
