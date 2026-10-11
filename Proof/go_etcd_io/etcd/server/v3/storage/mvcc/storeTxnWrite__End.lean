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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.storeTxnWrite.End.wp_proof : mvcc.storeTxnWrite.End.spec (GF := GF) (hG := hG) := by
  intro tw s γ ilog pend
  wp_start as Htw
  iunfold mvcc.storeTxnWriteIs at Htw
  iNamed Htw
  ihave #Hs0 : mvcc.isStore s γ $$ []
  · iexact Hs
  iunfold mvcc.isStore at Hs
  iNamedSuffix Hs "S"
  iunfold mvcc.batchTxSpec at Hbt
  icases Hbt with ⟨-, -, #HUnlock0, #HUnlock⟩
  ihave %Hlen := ownSlice_len chs (DFrac.own 1) ps $$ Hchs
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
  (try wp_auto)
  -- `len(tw.changes) != 0`
  wp_if_destruct
  · -- no change: the lock is released, nothing committed
    have hnil : pend = [] := hpend.2 Hif
    subst hnil
    (try wp_auto)
    ihave HW : mvcc.writerRes s γ $$ [Htoks Hw Hclog Hcur]
    · iunfold mvcc.writerRes
      iexists ilog, ntok
      simp only [named]
      iframe Htoks Hw Hclog Hcur
      iframe #
      ipureintro; exact ⟨Hbudget, Hne⟩
    rw [mvcc.pendPuts_nil]
    wp_apply HUnlock0 $$ [$Hlocked $HW]
    (try wp_auto)
    wp_if_destruct
    · exfalso
      exact Hif (hpend.1 rfl)
    (try wp_auto)
    wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hmu] as Hmu
    · inext; iunfold mvcc.muInv; itrivial
    (try wp_auto)
    iapply HΦ
    isplitl [Hmu HrevMu Hti]
    · iunfold mvcc.storeReader
      iexists ti
      simp only [named]
      iframe Hmu HrevMu Hti
      iframe #
    unfold mvcc.commitLog
    rw [if_pos rfl]
    iexact Hcert

  · -- a change: commit the pending revision under `s.revMu`
    have hne' : pend ≠ [] := fun h => Hif (hpend.1 h)
    (try wp_auto)
    wp_apply +noauto sync.RWMutex.wp_Lock $$ [$HrevMu] as ⟨Hlk, HP⟩
    wp_auto_lc 1
    imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.revMuInv s γ 1)) $$ Hlc1 HP with HP
    iunfold mvcc.revMuInv at HP
    icases HP with ⟨%log, HP⟩
    iNamedSuffix HP "L"
    -- the committed log is the writer's
    ihave %Hlog := ghostVar_agree γ.clog _ _ _ _ $$ HclogL Hclog
    subst Hlog
    -- `currentRev++`: both halves
    ihave Hcur : (s.[store, go!"currentRev"] ↦ (W64 ((ilog.length : Int) - 1) : w64) : IProp GF)
        $$ [HrevL Hcur]
    · rw [hsplit]
      iapply (dfractional (Φ := fun dq => (s.[store, go!"currentRev"] ↦{dq}
        (W64 ((ilog.length : Int) - 1) : w64) : IProp GF)) _ _).2
      iframe
    (try wp_auto)
    -- the ghost commit: the index writer, the committed log, the revision budget
    icombine Htoks Htok gives %Hge
    obtain ⟨n, rfl⟩ : ∃ n, ntok = n + 1 := ⟨ntok - 1, by omega⟩
    imod ownTokAuth_delete_S γ.revs n $$ Htoks Htok with Htoks
    imod ghostVar_update_halves (ilog ++ [pend]) γ.clog _ _ $$ HclogL Hclog with ⟨HclogL, Hclog⟩
    imod mvcc.idxWriter_commit γ.idx ilog pend (by omega) Hne $$ Hw with ⟨Hw, #Hcert'⟩
    have hrev : (W64 ((ilog.length : Int) - 1) : w64) + W64 1 =
        W64 (((ilog ++ [pend]).length : Int) - 1) := by
      rw [← mvcc.W64_add_one]; simp
    rw [hrev] at Hcur
    rw [hsplit] at Hcur
    icases (dfractional (Φ := fun dq => (s.[store, go!"currentRev"] ↦{dq}
        (W64 (((ilog ++ [pend]).length : Int) - 1) : w64) : IProp GF)) _ _).1 $$ Hcur
      with ⟨HcurL, Hcur⟩
    -- the batch lock's resource, at the committed log
    ihave HW : mvcc.writerRes s γ $$ [Htoks Hw Hclog Hcur]
    · iunfold mvcc.writerRes
      iexists (ilog ++ [pend]), n
      simp only [named]
      iframe Htoks Hw Hclog Hcur
      iframe #
      ipureintro
      exact ⟨by simp; omega, by simp⟩
    -- `tw.tx.Unlock()`: the write-back
    wp_apply (HUnlock (mvcc.pendPuts ilog pend) (mvcc.bucketMap ilog)) $$ [$Hlocked $HW $HbucketL]
      as Hbucket
    (try wp_auto)
    rw [← mvcc.bucketMap_append ilog pend Hne] at Hbucket
    -- `tw.s.revMu.Unlock()`
    wp_if_destruct
    · (try wp_auto)
      wp_apply sync.RWMutex.wp_Unlock $$ [$Hlk HcurL HclogL Hbucket] as HrevMu
      · inext
        iunfold mvcc.revMuInv
        iexists (ilog ++ [pend])
        simp only [named]
        iframe HcurL HclogL Hbucket
        iframe #
        ipureintro; simp
      (try wp_auto)
      -- `tw.s.mu.RUnlock()`
      wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hmu] as Hmu
      · inext; iunfold mvcc.muInv; itrivial
      (try wp_auto)
      iapply HΦ
      isplitl [Hmu HrevMu Hti]
      · iunfold mvcc.storeReader
        iexists ti
        simp only [named]
        iframe Hmu HrevMu Hti
        iframe #
      unfold mvcc.commitLog
      rw [if_neg hne']
      iexact Hcert'
    · exfalso
      exact hne' (hpend.2 Hif)
end proof

end EtcdGrove
end Perennial
