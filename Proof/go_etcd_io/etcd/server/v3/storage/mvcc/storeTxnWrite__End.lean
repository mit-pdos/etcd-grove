/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.CmpSteps
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__End

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.storeTxnWrite.End.wp_proof : mvcc.storeTxnWrite.End.spec (GF := GF) (hG := hG) := by
  intro trace tw s γ ilog pend chs ps sealed P f crev Z ld Y G R
  wp_start as ⟨Htw, HhookC, HP, #HokN, Hq, HG, #HFG, Hcb⟩
  -- the caller's hook: its facts, and the writer's fragment, given back (D22 receiver epochs, S5b)
  icases (mvcc.hookIs_split γ P f).1 $$ HhookC with ⟨#HhookC, Hfrag⟩
  iunfold mvcc.storeTxnWriteCoreY at Htw
  iNamed Htw
  icases Hcres with ⟨Hcres, Hloan⟩
  obtain ⟨Hps, Hlen⟩ := Hps
  ihave #Hs0 : mvcc.isStore s γ $$ []
  · iexact Hs
  iunfold mvcc.isStore at Hs
  iNamedSuffix Hs "S"
  -- the lock token, the batch transaction's or the one the lessor's delete left: its `Unlock`s
  icases mvcc.lockedIs_unlock ld bt _ _ _ _ _ _ _ _ _ _ _ _ _ (mvcc.pendPuts ilog pend)
    $$ [$Hbt $Hlocked] with ⟨%U, Hlocked, #Hul⟩
  iunfold mvcc.unlockAt at Hul
  icases Hul with ⟨#HUnlock0, #HUnlock⟩
  have hsplit := dfrac_own_half_half (1 : Qp)
  have hpend : pend = [] ↔ chs.len = 0 := by
    obtain ⟨h1, h2⟩ := Hlen
    constructor
    · intro h
      have hz : ps.length = 0 := by rw [Hps, h]; rfl
      rw [← mvcc.W64_sint_nat chs.len h2, ← h1, hz]; rfl
    · intro h
      rw [h] at h1
      exact List.length_eq_zero_iff.1 (by rw [← Hps, h1]; rfl)
  wp_auto_lc 3
  -- the caller's invariant is the store's
  imod mvcc.hookOk_agree_lc ⊤ γ P Pw f fw $$ [$Hlc1 $HhookC $Hhook] with ⟨-, #HPPw, -⟩
  ihave HP := HPPw $$ HP
  -- `len(tw.changes) != 0`
  wp_if_destruct
  · -- no change: the lock is released, nothing committed
    have hnil : pend = [] := hpend.2 Hif
    subst hnil
    ihave Hw := mvcc.idxWriterB_nil γ.idx ilog sealed $$ Hw
    (try wp_auto)
    -- the writer's state checked back in (D22 receiver epochs, S2): the batch lock's key and the
    -- transaction's part of `s.mu`'s deposit ghost back
    icases ghostVar_halves γ.wv ilog $$ Hwv with ⟨Hwv, HwvW⟩
    -- the view's parts: the writer's pin's quarter and `writerRes`'s eighth (M2's item 37)
    icases (mvcc.bucketViewL_split γ (1 : Qp).half.half (1 : Qp).half.half.half _).1 $$ Hbv
      with ⟨HbvP, Hbv⟩
    -- the caller's step: the writer's slot back at the committed log
    ihave Hcb := (mvcc.endCb_nil_iff γ ilog crev Y R).1 $$ Hcb
    imod Hcb $$ Hcert HY with ⟨HY, HR⟩
    ihave HL : mvcc.writerL s γ $$ [Htoks Hw Hclog Hwv Hcur Hlrd HY]
    · iunfold mvcc.writerL
      iexists ilog, ntok
      simp only [named]
      iframe Htoks Hw Hclog Hwv Hcur Hlrd HY
      iframe #
      ipureintro; exact ⟨Hbudget, Hne⟩
    icases mvcc.muHeld_cur s γ crev ti $$ Hmu with ⟨%o, %Ho, Hpin, Hmub⟩
    imod mvcc.writerInv_checkinG s γ iprop(G ∗ □ (mvcc.slotF γ ∗ G -∗ False))
        (mvcc.slotF_excl_of γ G) ilog _ o $$ Hlc2 HwiS [HG] Hpin HL HwvW
      with ⟨Hwk, Hwr, ⟨HG, -⟩, HwvW, Hpin⟩
    · iframe HG HFG
    ihave HW : mvcc.writerRes s γ $$ [Hwk HwvW Hbv Hcres]
    · iunfold mvcc.writerRes
      iexists ilog
      simp only [named]
      iframe Hwk HwvW Hbv Hcres
      iframe #
      ipureintro; exact Hne
    ihave HW := mvcc.storeW_put s γ $$ [$Hreg $HW]
    rw [mvcc.pendPuts_nil]
    wp_apply HUnlock0 $$ [$Hlocked $HW $HP]
    · ipureintro; rfl
    (try wp_auto)
    wp_if_destruct
    rotate_left
    · exfalso
      exact Hif (hpend.1 rfl)
    (try wp_auto)
    -- the slot of the index's lock back in the readers' pool (D22 receiver epochs, S4)
    subst Ho
    imod mvcc.readerPool_checkin γ _ o $$ Hlc3 HpoolS Hpin [Hti Hrt] Htko with ⟨Htk, Hwr2, Hpin⟩
    · iunfold mvcc.idxSlot; iframe Hti Hrt
    ihave Hmu := Hmub $$ Hpin
    iunfold mvcc.muHeld at Hmu
    icases Hmu with ⟨Hmu, Hmua, %o', %Ho', Hfs⟩
    wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hmu Hmua Hwr Hwr2 Hfs] as Hmu
    · inext; iunfold mvcc.muInv; iexists crev; iframe Hmua
      isplitl [Hwr Hwr2]
      · iapply (mvcc.wDep_halves γ).2; iframe Hwr Hwr2
      iapply mvcc.fieldShare_of_at s γ _ o'; iexact Hfs
    (try wp_auto)
    iapply HΦ
    iframe HZ
    isplitl [Hmu HrevMu Htk]
    · iunfold mvcc.storeReaderC
      simp only [named]
      iframe Hmu HrevMu Htk
    unfold mvcc.commitLog
    rw [ite_eq_left rfl, mvcc.logQPost_nil]
    try rw [if_pos rfl]
    iframe Hcert Htok Hfrag HG HR
    iunfold mvcc.writerPin; iframe HbvP Hloan

  · -- a change: commit the pending revision under `s.revMu`
    have hne' : pend ≠ [] := fun h => Hif (hpend.1 h)
    (try wp_auto)
    wp_apply +noauto sync.RWMutex.wp_Lock $$ [$HrevMu] as ⟨Hlk, HP⟩
    wp_auto_lc 1
    imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.revMuInv s γ 1)) $$ Hlc1 HP with HP
    icases mvcc.revMuInv_open_held s γ _ crev $$ [HP Hmu] with ⟨HP, HrstR, Hmu⟩
    · iframe HP Hmu
    iunfold mvcc.revMuBody at HP
    icases HP with ⟨%log, %ntokL, %cL, HP⟩
    iNamedSuffix HP "L"
    obtain ⟨HcL1, HcL2⟩ := HcL
    -- the committed log is the writer's
    ihave %Hlog := ghostVar_agree γ.clog _ _ _ _ $$ HclogL Hclog
    subst log
    -- `currentRev++`: both halves
    ihave Hcur : (s.[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half}
        (W64 ((ilog.length : Int) - 1) : w64) : IProp GF) $$ [HrevL Hcur]
    · iapply ((typedPointsto_dfractional (GF := GF) _ _).dfractional _ _).2
      iframe
    rw [← hsplit]
    (try wp_auto)
    -- the ghost commit: the index writer, the committed log, the revision budget
    iunfold mvcc.revToken at Htok
    icombine Htoks Htok gives %Hge
    icombine HtoksL Htoks gives %Hn
    obtain ⟨-, Hn⟩ := Hn
    subst Hn
    ihave Htoks : ownTokAuth γ.revs ntokL $$ [HtoksL Htoks]
    · iapply (mvcc.ownTokAuth_halves γ.revs ntokL).2; iframe HtoksL Htoks
    obtain ⟨n, rfl⟩ : ∃ n, ntokL = n + 1 := ⟨ntokL - 1, by omega⟩
    imod ownTokAuth_delete_S γ.revs n $$ Htoks Htok with Htoks
    icases (mvcc.ownTokAuth_halves γ.revs n).1 $$ Htoks with ⟨HtoksL, Htoks⟩
    imod ghostVar_update_halves (ilog ++ [pend]) γ.clog _ _ $$ HclogL Hclog with ⟨HclogL, Hclog⟩
    -- the committed log's authority: `s.revMu`'s fraction and the caller's (`logQPre`)
    ihave HlogH := mvcc.revQ_commit_pre γ ilog pend hne' $$ [$HlogL $Hq]
    imod mvcc.idxWriterB_commit γ.idx ilog pend sealed (by omega) $$ Hw HlogH with ⟨Hw, HlogH, #Hcert'⟩
    icases mvcc.idxWriter_nevLb_nil γ.idx (ilog ++ [pend]) $$ Hw with ⟨Hw, #Hnev'⟩
    icases mvcc.revQ_commit_post γ ilog pend hne' $$ HlogH with ⟨HlogL, Hq⟩
    have hrev : (W64 ((ilog.length : Int) - 1) : w64) + W64 1 =
        W64 (((ilog ++ [pend]).length : Int) - 1) := by
      rw [← mvcc.W64_add_one]; simp
    rw [hrev]
    ihave Hcur2 : (s.[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half}
        (W64 (((ilog ++ [pend]).length : Int) - 1) : w64) : IProp GF) $$ [Hcur]
    · rw [← hsplit]; iexact Hcur
    icases ((typedPointsto_dfractional (GF := GF) _ _).dfractional _ _).1 $$ Hcur2 with ⟨HcurL, Hcur⟩
    -- the bucket's full view: `s.revMu`'s half, the transaction's and the compaction's part's eighth
    -- (the snapshot image's (a)), its bucket `m`, of `ilog` (M2's item 15: thin after a restore in
    -- compaction mode); the commit's puts keep it of the committed log
    iunfold mvcc.compactRes at Hcres
    icases Hcres with ⟨%sched, %fin, %nf, %mC, Hmeta, Hfin, %Hnf, Hmk, HbmC, HtrC⟩
    iunfold mvcc.bucketViewL at HbucketL
    icases HbucketL with ⟨%m1, HbucketL, -⟩
    iunfold mvcc.bucketViewL at Hbv
    icases Hbv with ⟨%m, Hbv, #Hbl⟩
    ihave %He1 := mvcc.bucketView_agree γ _ _ m1 m $$ [HbucketL Hbv]
    · iframe HbucketL Hbv
    ihave %He2 := mvcc.bucketView_agree γ _ _ mC m $$ [HbmC Hbv]
    · iframe HbmC Hbv
    subst m1 mC
    ihave Hview := mvcc.bucketView_join3 γ m $$ [$HbucketL $Hbv $HbmC]
    ihave #Hbl' := mvcc.bucketLog_append γ ilog pend m Hne $$ Hbl
    -- `tw.tx.Unlock()`: the write-back, then the batch lock's resource at the committed log
    -- (half the new view), the other half kept for `s.revMu`
    -- the writer's state at the committed log, checked back in (D22 receiver epochs, S2)
    imod ghostVar_update (ilog ++ [pend]) γ.wv ilog $$ Hwv with Hwv
    icases ghostVar_halves γ.wv (ilog ++ [pend]) $$ Hwv with ⟨Hwv, HwvW⟩
    -- the caller's step at the bump: `s.revMu`'s slot (at the transaction's compaction revision)
    -- and the writer's to the committed log
    icases mvcc.muHeld_crevUB s γ crev ti _ cL HcL1 $$ [$Hmu $HcrevL] with ⟨Hmu, HcrevL, %HcLe⟩
    subst HcLe
    ihave Hcb := (mvcc.endCb_cons_iff γ ilog pend hne' crev Y R).1 $$ Hcb
    imod Hcb $$ Hcert' [HXL HY] with ⟨HXL, HY, HR⟩
    · iframe HXL HY
    ihave HL : mvcc.writerL s γ $$ [Htoks Hw Hclog Hwv Hcur Hlrd HY]
    · iunfold mvcc.writerL
      iexists (ilog ++ [pend]), n
      simp only [named]
      iframe Htoks Hw Hclog Hwv Hcur Hlrd HY
      iframe #
      ipureintro
      exact ⟨by simp; omega, by simp⟩
    icases mvcc.muHeld_cur s γ crev ti $$ Hmu with ⟨%o, %Ho, Hpin, Hmub⟩
    imod mvcc.writerInv_checkinG s γ iprop(G ∗ □ (mvcc.slotF γ ∗ G -∗ False))
        (mvcc.slotF_excl_of γ G) (ilog ++ [pend]) _ o $$ Hlc2 HwiS [HG] Hpin HL HwvW
      with ⟨Hwk, Hwr, ⟨HG, -⟩, HwvW, Hpin⟩
    · iframe HG HFG
    ihave #HUnlock' := HUnlock $$ %m
      %(iprop(mvcc.bucketViewL γ (1 : Qp).half (ilog ++ [pend]) ∗
        mvcc.bucketViewL γ (1 : Qp).half.half (ilog ++ [pend])))
    ihave #Hc3 := Hcert'
    iunfold mvcc.idxCert at Hc3
    icases Hc3 with ⟨-, %Hlwf', -⟩
    have hb' : mvcc.LogB (ilog ++ [pend]) := ⟨Hlwf'.2.1, Hlwf'.2.2⟩
    ihave HtrC := mvcc.cmpTrack_append γ ilog pend hb' Hne m ⟨fin, sched⟩ $$ HtrC
    wp_apply HUnlock' $$ [$Hlocked $Hview $HP Hwk HwvW Hmeta Hfin Hmk HtrC] as ⟨Hbucket, HbvP⟩
    · iintro Hv
      icases (mvcc.bucketView_halves γ 1 _).1 $$ Hv with ⟨Hv1, Hv2⟩
      icases (mvcc.bucketView_quarters γ _).1 $$ Hv1 with ⟨Hv1, Hv1b⟩
      ihave Hv2 : mvcc.bucketViewL γ (1 : Qp).half (ilog ++ [pend]) $$ [Hv2]
      · iunfold mvcc.bucketViewL; iexists _; iframe Hv2; iexact Hbl'
      ihave Hv1b : mvcc.bucketViewL γ (1 : Qp).half.half (ilog ++ [pend]) $$ [Hv1b]
      · iunfold mvcc.bucketViewL; iexists _; iframe Hv1b; iexact Hbl'
      icases (mvcc.bucketView_halves γ (1 : Qp).half.half _).1 $$ Hv1 with ⟨Hv1, HvC⟩
      ihave Hv1 : mvcc.bucketViewL γ (1 : Qp).half.half.half (ilog ++ [pend]) $$ [Hv1]
      · iunfold mvcc.bucketViewL; iexists _; iframe Hv1; iexact Hbl'
      iframe Hv2 Hv1b
      iapply mvcc.storeW_put s γ
      iframe Hreg
      iunfold mvcc.writerRes
      iexists (ilog ++ [pend])
      simp only [named]
      iframe Hwk HwvW Hv1
      iframe #
      isplitr
      · ipureintro; simp
      iunfold mvcc.compactRes
      iexists sched, fin, nf, _
      iframe Hmeta Hfin Hmk HvC HtrC
      ipureintro; exact Hnf
    (try wp_auto)
    -- `tw.s.revMu.Unlock()`
    wp_if_destruct
    · exfalso
      exact hne' (hpend.2 Hif)
    · (try wp_auto)
      wp_apply sync.RWMutex.wp_Unlock $$ [$Hlk HcurL HclogL Hbucket HtoksL HlogL HcmpL HcrevL HXL HrstR]
        as HrevMu
      · inext
        iapply mvcc.revMuInv_close; iframe HrstR; iunfold mvcc.revMuBody
        iexists (ilog ++ [pend]), n, crev
        simp only [named]
        iframe HcurL HclogL Hbucket HtoksL HlogL HcmpL HcrevL HXL
        iframe #
        isplitl []
        · iunfold mvcc.certOkNext at HokN
          icases HokN with (%Hp0 | #Hok')
          · exact absurd Hp0 hne'
          · iexact Hok'
        ipureintro; simp; omega
      (try wp_auto)
      -- `tw.s.mu.RUnlock()`
      -- the slot of the index's lock back in the readers' pool (D22 receiver epochs, S4)
      subst Ho
      imod mvcc.readerPool_checkin γ _ o $$ Hlc3 HpoolS Hpin [Hti Hrt] Htko with ⟨Htk, Hwr2, Hpin⟩
      · iunfold mvcc.idxSlot; iframe Hti Hrt
      ihave Hmu := Hmub $$ Hpin
      iunfold mvcc.muHeld at Hmu
      icases Hmu with ⟨Hmu, Hmua, %o', %Ho', Hfs⟩
      wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hmu Hmua Hwr Hwr2 Hfs] as Hmu
      · inext; iunfold mvcc.muInv; iexists crev; iframe Hmua
        isplitl [Hwr Hwr2]
        · iapply (mvcc.wDep_halves γ).2; iframe Hwr Hwr2
        iapply mvcc.fieldShare_of_at s γ _ o'; iexact Hfs
      (try wp_auto)
      iapply HΦ
      iframe HZ
      isplitl [Hmu HrevMu Htk]
      · iunfold mvcc.storeReaderC
        simp only [named]
        iframe Hmu HrevMu Htk
      unfold mvcc.commitLog
      rw [ite_eq_right hne']
      try rw [ite_eq_right hne']
      iframe Hcert' Hq Hfrag HG HR
      iunfold mvcc.writerPin; iframe HbvP Hloan
end proof

end EtcdGrove
end Perennial
