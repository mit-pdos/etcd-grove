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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.storeTxnWrite.End.wp_proof : mvcc.storeTxnWrite.End.spec (GF := GF) (hG := hG) := by
  intro tw s γ ilog pend chs ps sealed P f crev Z
  wp_start as ⟨Htw, #HhookC, HP⟩
  iunfold mvcc.storeTxnWriteCore at Htw
  iNamed Htw
  obtain ⟨Hps, Hlen⟩ := Hps
  ihave #Hs0 : mvcc.isStore s γ $$ []
  · iexact Hs
  iunfold mvcc.isStore at Hs
  iNamedSuffix Hs "S"
  icombine Hidx HidxS gives %Hti_eq
  have Hti_eq' := mvcc.mkOk_loc_inj _ Hti_eq
  subst Hti_eq'
  iunfold mvcc.batchTxSpecG at Hbt
  icases Hbt with ⟨-, -, #HUnlock0, #HUnlock, -⟩
  have hsplit := mvcc.own_half_half (1 : Qp)
  have hpend : pend = [] ↔ chs.len = 0 := by
    obtain ⟨h1, h2⟩ := Hlen
    constructor
    · intro h
      have hz : ps.length = 0 := by rw [Hps, h]; rfl
      rw [← mvcc.W64_sint_nat chs.len h2, ← h1, hz]; rfl
    · intro h
      rw [h] at h1
      exact List.length_eq_zero_iff.1 (by rw [← Hps, h1]; rfl)
  wp_auto_lc 1
  -- the caller's invariant is the store's
  imod mvcc.hookIs_agree_lc ⊤ γ P Pw f fw $$ [$Hlc1 $HhookC $Hhook] with ⟨-, #HPPw, -⟩
  ihave HP := HPPw $$ HP
  -- `len(tw.changes) != 0`
  wp_if_destruct
  · -- no change: the lock is released, nothing committed
    have hnil : pend = [] := hpend.2 Hif
    subst hnil
    ihave Hw := mvcc.idxWriterB_nil γ.idx ilog sealed $$ Hw
    (try wp_auto)
    ihave HW : mvcc.writerRes s γ $$ [Htoks Hw Hclog Hcur Hbv Hcres]
    · iunfold mvcc.writerRes
      iexists ilog, ntok
      simp only [named]
      iframe Htoks Hw Hclog Hcur Hbv Hcres
      iframe #
      ipureintro; exact ⟨Hbudget, Hne⟩
    ihave HW := mvcc.storeW_put s γ $$ [$Hreg $HW]
    rw [mvcc.pendPuts_nil]
    wp_apply HUnlock0 $$ [$Hlocked $HW $HP]
    (try wp_auto)
    wp_if_destruct
    rotate_left
    · exfalso
      exact Hif (hpend.1 rfl)
    (try wp_auto)
    iunfold mvcc.muHeld at Hmu
    icases Hmu with ⟨Hmu, Hmua⟩
    wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hmu Hmua] as Hmu
    · inext; iunfold mvcc.muInv; iexists crev; iexact Hmua
    (try wp_auto)
    iapply HΦ
    iframe HZ
    isplitl [Hmu HrevMu Hti Hrt]
    · iunfold mvcc.storeReaderC
      iexists ti
      simp only [named]
      iframe Hmu HrevMu Hti Hrt
      iframe #
    unfold mvcc.commitLog
    rw [ite_eq_left rfl]
    try rw [if_pos rfl]
    iframe Hcert Htok

  · -- a change: commit the pending revision under `s.revMu`
    have hne' : pend ≠ [] := fun h => Hif (hpend.1 h)
    (try wp_auto)
    wp_apply +noauto sync.RWMutex.wp_Lock $$ [$HrevMu] as ⟨Hlk, HP⟩
    wp_auto_lc 1
    imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.revMuInv s γ 1)) $$ Hlc1 HP with HP
    iunfold mvcc.revMuInv at HP
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
    imod mvcc.idxWriterB_commit γ.idx ilog pend sealed (by omega) $$ Hw HlogL with ⟨Hw, HlogL, #Hcert'⟩
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
    ihave #HUnlock' := HUnlock $$ %(mvcc.pendPuts ilog pend) %(mvcc.bucketMap ilog)
      %(mvcc.bucketView γ (1 : Qp).half (mvcc.bucketMap (ilog ++ [pend])))
    wp_apply HUnlock' $$ [$Hlocked $Hview $HP Htoks Hw Hclog Hcur Hcres] as Hbucket
    · rw [← mvcc.bucketMap_append ilog pend Hne]
      iintro Hv
      icases (mvcc.bucketView_halves γ 1 _).1 $$ Hv with ⟨Hv1, Hv2⟩
      iframe Hv2
      iapply mvcc.storeW_put s γ
      iframe Hreg
      iunfold mvcc.writerRes
      iexists (ilog ++ [pend]), n
      simp only [named]
      iframe Htoks Hw Hclog Hcur Hv1 Hcres
      iframe #
      ipureintro
      exact ⟨by simp; omega, by simp⟩
    (try wp_auto)
    -- `tw.s.revMu.Unlock()`
    wp_if_destruct
    · exfalso
      exact hne' (hpend.2 Hif)
    · (try wp_auto)
      wp_apply sync.RWMutex.wp_Unlock $$ [$Hlk HcurL HclogL Hbucket HtoksL HlogL HcmpL HcrevL]
        as HrevMu
      · inext
        iunfold mvcc.revMuInv
        iexists (ilog ++ [pend]), n, cL
        simp only [named]
        iframe HcurL HclogL Hbucket HtoksL HlogL HcmpL HcrevL
        iframe #
        ipureintro; simp; omega
      (try wp_auto)
      -- `tw.s.mu.RUnlock()`
      iunfold mvcc.muHeld at Hmu
      icases Hmu with ⟨Hmu, Hmua⟩
      wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hmu Hmua] as Hmu
      · inext; iunfold mvcc.muInv; iexists crev; iexact Hmua
      (try wp_auto)
      iapply HΦ
      iframe HZ
      isplitl [Hmu HrevMu Hti Hrt]
      · iunfold mvcc.storeReaderC
        iexists ti
        simp only [named]
        iframe Hmu HrevMu Hti Hrt
        iframe #
      unfold mvcc.commitLog
      rw [ite_eq_right hne']
      try rw [ite_eq_right hne']
      iframe Hcert'
end proof

end EtcdGrove
end Perennial
