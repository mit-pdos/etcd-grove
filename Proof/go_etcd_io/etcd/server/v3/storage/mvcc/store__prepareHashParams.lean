/-
Proof of `Spec/.../mvcc/store__prepareHashParams.lean` (etcd-io/etcd#21202, pr-verify/etcd-21202).
Lean-first. The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__prepareHashParams
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__Keep

@[expose] public section

set_option linter.unusedVariables false
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
variable [go_etcd_io.etcd.cache.v3.Assumptions]

set_option maxHeartbeats 1000000 in
theorem mvcc.store.prepareHashParams.wp_proof
    (hKeep : mvcc.treeIndex.Keep.spec (GF := GF) (hG := hG)) :
    mvcc.store.prepareHashParams.spec (GF := GF) (hG := hG) := by
  intro s γ rev compactRev Hcmp Hrev0
  wp_start as ⟨#Hs, Hrd, Hcok⟩
  ihave #Hs0 : mvcc.isStore s γ $$ []
  · iexact Hs
  iunfold mvcc.isStore at Hs
  iNamed Hs
  iunfold mvcc.storeReaderC at Hrd
  icases Hrd with ⟨%ti2, Hrd⟩
  iNamedSuffix Hrd "R"
  icombine Hidx HidxR gives %Hti_eq
  have Hti_eq' := mvcc.mkOk_loc_inj _ Hti_eq
  subst Hti_eq'
  ihave Hinit : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, ⟨%ecp, #Hcomp⟩, ⟨%ef, #Hfut⟩, -⟩
  ihave #Hbk' := mvcc.isKeyBackendG_cmp _ s γ _ _ _ Hcmp $$ Hbk
  iunfold mvcc.isKeyBackendG at Hbk'
  icases Hbk' with ⟨%bi, %Hbi, -, -, -, -, -, -, #HCmp⟩
  icases HCmp $$ [] with ⟨-, -, #HRT⟩
  · ipureintro; trivial
  subst Hbi
  (try wp_auto)
  -- `s.mu.RLock()`: its part of `s.mu`'s resource, at the compaction revision `cm`
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$HmuR] as ⟨Hmul, HmuP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.muInv s γ sync.rfrac)) $$ Hlc1 HmuP with HmuP
  iunfold mvcc.muInv at HmuP
  icases HmuP with ⟨%cm, HmuP⟩
  iunfold mvcc.muInvAt at HmuP
  iNamed HmuP
  -- `s.revMu.RLock()`
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$HrevMuR] as ⟨Hrevl, HP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.revMuInv s γ sync.rfrac)) $$ Hlc1 HP with HP
  iunfold mvcc.revMuInv at HP
  icases HP with ⟨%log, %ntok, %c, HP⟩
  iNamed HP
  ihave %Hcc := mvcc.crevUB_agree γ.idx _ _ cm c HcM Hc.1 $$ HcrevM Hcrev
  subst Hcc
  icases mvcc.crevUB_get_lb γ.idx _ cm $$ HcrevM with ⟨HcrevM, #Hlbc⟩
  ihave %Hcur0 := mvcc.idxCert_lastRev γ log Hne $$ Hcert
  -- the custom compaction revision is at or above the store's
  icases mvcc.hashCrevOk_bound γ compactRev _ cm HcM $$ [$Hcok $HcrevM] with ⟨Hcok, HcrevM, %Hcge⟩
  have Hcm1 : -1 ≤ cm := HcM
  have Hcmlt : cm < log.length := Hc.2
  have Hlen : sint.Z (W64 ((log.length : Int) - 1) : w64) = (log.length : Int) - 1 := by
    have hpos : 0 < log.length := List.length_pos_iff.2 Hne
    have := Hbudget
    unfold sint.Z W64
    rw [BitVec.toInt_ofInt_eq_self (by decide) (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)
      (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)]
  (try wp_auto)
  -- `compactRev`: the caller's if positive, else the store's
  wp_if_destruct
  all_goals (try wp_auto)
  all_goals
    ihave compactRev : compactRev_ptr ↦ (mvcc.hashCrev compactRev cm) $$ [compactRev]
    · unfold mvcc.hashCrev
      first
        | (rw [if_pos (by word)]; iexact compactRev)
        | (rw [if_neg (by word)]; iexact compactRev)
  all_goals
    have Hpcm : cm ≤ sint.Z (mvcc.hashCrev compactRev cm) := by
      unfold mvcc.hashCrev
      split
      · have : sint.Z (W64 cm : w64) = cm := by
          have := Hbudget
          unfold sint.Z W64
          rw [BitVec.toInt_ofInt_eq_self (by decide) (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)
            (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)]
        omega
      · next h => exact Hcge (by word)
    clear Hif
  all_goals
    -- `s.revMu.RUnlock()`
    wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hrevl Hrev Hbucket Hclog Hcert Htoks Hlog Hcmp Hcrev]
      as HrevMuR
    · inext
      iunfold mvcc.revMuInv
      iexists log, ntok, cm
      simp only [named]
      iframe Hrev Hbucket Hclog Htoks Hlog Hcmp Hcrev
      iframe #
      ipureintro; exact ⟨Hne, Hbudget, Hc⟩
    (try wp_auto)
    wp_if_destruct
    · -- `rev > 0`
      have Hr0 := Hif; clear Hif
      wp_if_destruct
      · -- `rev < compactRev`: `ErrCompacted`
        have Hlt := Hif; clear Hif
        wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hmul HcmpM HcrevM] as HmuR
        · inext
          iunfold mvcc.muInv
          iexists cm
          iunfold mvcc.muInvAt
          simp only [named]
          iframe HcmpM HcrevM
          iframe #
          ipureintro; exact HcM
        (try wp_auto)
        iapply HΦ
        iframe Hcok
        isplitl [HmuR HrevMuR HtiR HrtR]
        · iunfold mvcc.storeReaderC
          iexists ti
          simp only [named]
          iframe HmuR HrevMuR HtiR HrtR
          iframe #
        iexists log, cm
        iframe #
        isplitr
        · ipureintro; exact ⟨Hne, Hcm1, Hcmlt⟩
        iright; ileft
        isplitr
        · ipureintro; exact ⟨by word, by word, rfl⟩
        first | (iexists ecp; iframe #) | (ipureintro; rfl) | iframe
      · -- `rev > currentRev`
        have Hnc := Hif; clear Hif
        rw [decide_eq_true Hr0]
        (try wp_auto)
        by_cases Hfut : sint.Z (W64 ((log.length : Int) - 1) : w64) < sint.Z rev
        · rw [decide_eq_true Hfut]
          (try wp_auto)
          wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hmul HcmpM HcrevM] as HmuR
          · inext
            iunfold mvcc.muInv
            iexists cm
            iunfold mvcc.muInvAt
            simp only [named]
            iframe HcmpM HcrevM
            iframe #
            ipureintro; exact HcM
          (try wp_auto)
          iapply HΦ
          iframe Hcok
          isplitl [HmuR HrevMuR HtiR HrtR]
          · iunfold mvcc.storeReaderC
            iexists ti
            simp only [named]
            iframe HmuR HrevMuR HtiR HrtR
            iframe #
          iexists log, cm
          iframe #
          isplitr
          · ipureintro; exact ⟨Hne, Hcm1, Hcmlt⟩
          iright; iright
          isplitr
          · ipureintro; exact ⟨by word, by word, rfl, by word⟩
          first | (iexists ef; iframe #) | (ipureintro; rfl) | iframe
        · rw [decide_eq_false Hfut]
          (try wp_auto)
          have Hne0 : ¬ rev = W64 0 := by intro h; subst h; revert Hr0; decide
          rw [decide_eq_false Hne0]
          (try wp_auto)
          have HP : mvcc.hashRev rev (W64 ((log.length : Int) - 1)) = rev := by
            unfold mvcc.hashRev; exact if_neg Hne0
          -- `kvindex.Keep(prev)`, under `s.mu` (its part of the compaction revision, at or below `prev`)
          have Hpv : -1 ≤ cm ∧ cm ≤ sint.Z (mvcc.hashRev rev (W64 ((log.length : Int) - 1))) ∧
              0 ≤ sint.Z (mvcc.hashRev rev (W64 ((log.length : Int) - 1))) ∧
              sint.Z (mvcc.hashRev rev (W64 ((log.length : Int) - 1))) < (mvcc.IdxKnow.cert log).log.length := by
            simp only [mvcc.IdxKnow.log_cert]
            unfold mvcc.hashRev
            split <;> omega
          rw [HP] at Hpv
          wp_apply (hKeep ti γ.idx (mvcc.IdxKnow.cert log) _ _ cm) $$ [$HtiR $HcrevM] as %keepm ⟨HtiR, -, HcrevM, %A, Hkeep, %HA⟩
          · rw [mvcc.idxKnows_cert]; iframe #; ipureintro; exact Hpv
          (try wp_auto)
          -- `s.b.ReadTx()`, `tx.RLock()`
          wp_apply HRT as %rt #Hrt
          (try wp_auto)
          ipersist tx
          ihave #Hrt' := Hrt
          iunfold mvcc.metaReadTx at Hrt'
          icases Hrt' with ⟨#HRL, #HRU, -⟩
          wp_apply HRL
          (try wp_auto)
          -- `s.mu.RUnlock()`
          wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hmul HcmpM HcrevM] as HmuR
          · inext
            iunfold mvcc.muInv
            iexists cm
            iunfold mvcc.muInvAt
            simp only [named]
            iframe HcmpM HcrevM
            iframe #
            ipureintro; exact HcM
          (try wp_auto)
          iapply HΦ
          iframe Hcok
          isplitl [HmuR HrevMuR HtiR HrtR]
          · iunfold mvcc.storeReaderC
            iexists ti
            simp only [named]
            iframe HmuR HrevMuR HtiR HrtR
            iframe #
          iexists log, cm
          iframe #
          isplitr
          · ipureintro; exact ⟨Hne, Hcm1, Hcmlt⟩
          ileft
          isplitr
          · ipureintro
            rw [HP]
            refine ⟨rfl, rfl, rfl, rfl, ?_, Hpv.2.1, Hpv.2.2.1, ?_⟩
            · intro h
              refine ⟨?_, ?_⟩ <;> (first | omega | (exfalso; apply Hr0; word))
            · first | omega | exact le_refl _
          isplitl [Hkeep]
          · iexists A
            iframe Hkeep
            ipureintro
            simpa only [mvcc.IdxKnow.log_cert] using HA
          isplitr
          · iframe #
            try (ipureintro; rfl)
          · iunfold mvcc.hashCleanup
            iintro !> %Φ'
            (try iintro !>)
            iintro _ HΦ'
            wp_auto
            wp_apply HRU
            (try wp_auto)
            iapply HΦ'; itrivial

    · have Hr0 := Hif; clear Hif
      have Hz : rev = W64 0 := by word
      rw [decide_eq_false Hr0]
      (try wp_auto)
      rw [decide_eq_true Hz]
      (try wp_auto)
      have HP : mvcc.hashRev rev (W64 ((log.length : Int) - 1)) = W64 ((log.length : Int) - 1) := by
        unfold mvcc.hashRev; exact if_pos Hz
      -- `kvindex.Keep(prev)`, under `s.mu` (its part of the compaction revision, at or below `prev`)
      have Hpv : -1 ≤ cm ∧ cm ≤ sint.Z (mvcc.hashRev rev (W64 ((log.length : Int) - 1))) ∧
          0 ≤ sint.Z (mvcc.hashRev rev (W64 ((log.length : Int) - 1))) ∧
          sint.Z (mvcc.hashRev rev (W64 ((log.length : Int) - 1))) < (mvcc.IdxKnow.cert log).log.length := by
        simp only [mvcc.IdxKnow.log_cert]
        unfold mvcc.hashRev
        split <;> omega
      rw [HP] at Hpv
      wp_apply (hKeep ti γ.idx (mvcc.IdxKnow.cert log) _ _ cm) $$ [$HtiR $HcrevM] as %keepm ⟨HtiR, -, HcrevM, %A, Hkeep, %HA⟩
      · rw [mvcc.idxKnows_cert]; iframe #; ipureintro; exact Hpv
      (try wp_auto)
      -- `s.b.ReadTx()`, `tx.RLock()`
      wp_apply HRT as %rt #Hrt
      (try wp_auto)
      ipersist tx
      ihave #Hrt' := Hrt
      iunfold mvcc.metaReadTx at Hrt'
      icases Hrt' with ⟨#HRL, #HRU, -⟩
      wp_apply HRL
      (try wp_auto)
      -- `s.mu.RUnlock()`
      wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hmul HcmpM HcrevM] as HmuR
      · inext
        iunfold mvcc.muInv
        iexists cm
        iunfold mvcc.muInvAt
        simp only [named]
        iframe HcmpM HcrevM
        iframe #
        ipureintro; exact HcM
      (try wp_auto)
      iapply HΦ
      iframe Hcok
      isplitl [HmuR HrevMuR HtiR HrtR]
      · iunfold mvcc.storeReaderC
        iexists ti
        simp only [named]
        iframe HmuR HrevMuR HtiR HrtR
        iframe #
      iexists log, cm
      iframe #
      isplitr
      · ipureintro; exact ⟨Hne, Hcm1, Hcmlt⟩
      ileft
      isplitr
      · ipureintro
        rw [HP]
        refine ⟨rfl, rfl, rfl, rfl, ?_, Hpv.2.1, Hpv.2.2.1, ?_⟩
        · intro h
          refine ⟨?_, ?_⟩ <;> (first | omega | (exfalso; apply Hr0; word))
        · first | omega | exact le_refl _
      isplitl [Hkeep]
      · iexists A
        iframe Hkeep
        ipureintro
        simpa only [mvcc.IdxKnow.log_cert] using HA
      isplitr
      · iframe #
        try (ipureintro; rfl)
      · iunfold mvcc.hashCleanup
        iintro !> %Φ'
        (try iintro !>)
        iintro _ HΦ'
        wp_auto
        wp_apply HRU
        (try wp_auto)
        iapply HΦ'; itrivial


end proof

end EtcdGrove
end Perennial
