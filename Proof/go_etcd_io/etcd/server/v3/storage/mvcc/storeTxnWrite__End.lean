/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

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
  intro trace tw s γ ilog pend chs ps sealed P f crev Z ld
  wp_start as ⟨Htw, HhookC, HP, #HokN, Hq⟩
  -- the caller's hook: its facts, and the writer's fragment, given back (D22 receiver epochs, S5b)
  icases (mvcc.hookIs_split γ P f).1 $$ HhookC with ⟨#HhookC, Hfrag⟩
  iunfold mvcc.storeTxnWriteCore at Htw
  iNamed Htw
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
    ihave HL : mvcc.writerL s γ $$ [Htoks Hw Hclog Hwv Hcur Hlrd]
    · iunfold mvcc.writerL
      iexists ilog, ntok
      simp only [named]
      iframe Htoks Hw Hclog Hwv Hcur Hlrd
      iframe #
      ipureintro; exact ⟨Hbudget, Hne⟩
    icases mvcc.muHeld_cur s γ crev ti $$ Hmu with ⟨%o, %Ho, Hpin, Hmub⟩
    imod mvcc.writerInv_checkin s γ ilog _ o $$ Hlc2 HwiS Hpin HL HwvW with ⟨Hwk, Hwr, HwvW, Hpin⟩
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
    iframe Hcert Htok Hfrag

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
    -- the bucket's full view: `s.revMu`'s half and the writer's
    ihave Hview : mvcc.bucketView γ 1 (mvcc.bucketMap ilog) $$ [HbucketL Hbv]
    · iapply (mvcc.bucketView_halves γ 1 _).2
      iframe HbucketL Hbv
    -- `tw.tx.Unlock()`: the write-back, then the batch lock's resource at the committed log
    -- (half the new view), the other half kept for `s.revMu`
    -- the writer's state at the committed log, checked back in (D22 receiver epochs, S2)
    imod ghostVar_update (ilog ++ [pend]) γ.wv ilog $$ Hwv with Hwv
    icases ghostVar_halves γ.wv (ilog ++ [pend]) $$ Hwv with ⟨Hwv, HwvW⟩
    ihave HL : mvcc.writerL s γ $$ [Htoks Hw Hclog Hwv Hcur Hlrd]
    · iunfold mvcc.writerL
      iexists (ilog ++ [pend]), n
      simp only [named]
      iframe Htoks Hw Hclog Hwv Hcur Hlrd
      iframe #
      ipureintro
      exact ⟨by simp; omega, by simp⟩
    icases mvcc.muHeld_cur s γ crev ti $$ Hmu with ⟨%o, %Ho, Hpin, Hmub⟩
    imod mvcc.writerInv_checkin s γ (ilog ++ [pend]) _ o $$ Hlc2 HwiS Hpin HL HwvW with ⟨Hwk, Hwr, HwvW, Hpin⟩
    ihave #HUnlock' := HUnlock $$ %(mvcc.bucketMap ilog)
      %(mvcc.bucketView γ (1 : Qp).half (mvcc.bucketMap (ilog ++ [pend])))
    wp_apply HUnlock' $$ [$Hlocked $Hview $HP Hwk HwvW Hcres] as Hbucket
    · rw [← mvcc.bucketMap_append ilog pend Hne]
      iintro Hv
      icases (mvcc.bucketView_halves γ 1 _).1 $$ Hv with ⟨Hv1, Hv2⟩
      iframe Hv2
      iapply mvcc.storeW_put s γ
      iframe Hreg
      iunfold mvcc.writerRes
      iexists (ilog ++ [pend])
      simp only [named]
      iframe Hwk HwvW Hv1 Hcres
      iframe #
      ipureintro; simp
    (try wp_auto)
    -- `tw.s.revMu.Unlock()`
    wp_if_destruct
    · exfalso
      exact hne' (hpend.2 Hif)
    · (try wp_auto)
      wp_apply sync.RWMutex.wp_Unlock $$ [$Hlk HcurL HclogL Hbucket HtoksL HlogL HcmpL HcrevL HrstR]
        as HrevMu
      · inext
        iapply mvcc.revMuInv_close; iframe HrstR; iunfold mvcc.revMuBody
        iexists (ilog ++ [pend]), n, cL
        simp only [named]
        iframe HcurL HclogL Hbucket HtoksL HlogL HcmpL HcrevL
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
      iframe Hcert' Hq Hfrag
end proof

end EtcdGrove
end Perennial
