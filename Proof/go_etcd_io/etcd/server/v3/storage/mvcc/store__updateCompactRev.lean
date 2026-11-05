/-
Proof of the spec of the same name (the mvcc store's compaction, unit 5c).
The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.M1Placeholders
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__updateCompactRev
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.NewJob
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__compactBarrier
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.Scheduler__Schedule
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.SetScheduledCompact
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.CmpSteps
public import Proof.ReceiptTactics

@[expose] public section

set_option linter.unusedVariables false

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

theorem mvcc.store.updateCompactRev.wp_proof
    (h0 : schedule.NewJob.spec (GF := GF) (hG := hG))
    (h1 : mvcc.store.compactBarrier.spec (GF := GF) (hG := hG))
    (h2 : schedule.Scheduler.Schedule.spec (GF := GF) (hG := hG))
    (h3 : mvcc.SetScheduledCompact.spec (GF := GF) (hG := hG)) :
    mvcc.store.updateCompactRev.spec (GF := GF) (hG := hG) := by
  intro s γ rev c cp P hk Pre Q Post S Fok Fce Ffr hcmp hlag hpos1 hS1 hS2
  wp_start as ⟨#Hs, HmuA, Hright, #HpermR, Hctx, HRTok, #HsupM, HS, Hcb⟩
  ihave #Hs' := Hs
  iunfold mvcc.isStore at Hs'
  iNamed Hs'
  -- the restorable right (M2, the storage side, item 17): its queue, the closer's eighth of the
  -- fields (which read `s.b` and `s.fifoSched`) and the jobs' share
  icases (mvcc.compactRightR_iff s γ c).1 $$ Hright with
    ⟨Hcr, Hq, %o, ⟨Hfs, #Hsc, Hstc, Htok⟩, #Hstop⟩
  iunfold mvcc.fieldShareAt at Hfs
  iNamed Hfs
  iunfold mvcc.storeFields at Hflds
  iNamed Hflds
  obtain ⟨b, ti, ssched, sstop⟩ := o
  ihave #Hph0 := Hph
  iunfold mvcc.physOk at Hph
  iNamed Hph
  try simp only
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  -- (question 5's core stage) a receipt from `s.revMu.Lock`'s resolution, for `ForceCommit`'s
  -- write-back token
  wp_take_receipt as Hr2
  ipersist s
  wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$HrevMu] as ⟨Hwl, HR⟩
  wp_auto_lc 3
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.revMuInv s γ 1)) $$ Hlc1 HR with HR
  icases mvcc.revMuInv_open_cur s γ _ _ _ _ $$ [HR Hfrst Hcur] with ⟨HR, HrstR, Hfrst, Hcur⟩
  · iframe HR Hfrst Hcur
  iunfold mvcc.muInvLag at HmuA
  iNamed HmuA
  -- the lock's body, with the compaction revision's physical value (M2's item 15: the lag)
  iunfold mvcc.revMuBodyL at HR
  icases HR with ⟨%log, %ntok, %c', %cp', HR⟩
  iNamed HR
  ihave %Hcc := mvcc.crevUB_agree γ.idx _ _ c' c Hc.1 (by omega) $$ Hcrev Hcr
  subst Hcc
  iunfold mvcc.revLag at Hlag
  icases Hlag with ⟨%Hp', Hlag⟩
  icombine Hcmp HcmpM gives %Hv
  have Hv : (W64 cp' : w64) = W64 cp := by first | exact Hv.2 | exact Hv
  have Hpp : cp = cp' := by
    obtain ⟨-, Hc'⟩ := Hc
    word
  subst Hpp
  ihave Hinit : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, ⟨%ecp, #Hcomp⟩, ⟨%ef, #Hfut⟩, -⟩
  ihave #Hschp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule $$ []
  · iPkgInit
  ihave #Hfifo := HisSched
  ihave #Hfifo' := Hfifo
  iunfold schedule.isFifo at Hfifo'
  icases Hfifo' with ⟨%Hnn, -⟩
  cases ssched with
  | nil => exact absurd rfl Hnn
  | ok sci =>
  wp_auto
  wp_if_destruct
  · -- `rev <= s.compactMainRev`: `ErrCompacted`, a barrier job; no lag (the caller's `rev` is
    -- at least the revision it lags)
    have Hcpc : c' = cp := by
      have hcz : sint.Z (W64 cp : w64) = cp := by
        obtain ⟨-, Hc'⟩ := Hc
        word
      rw [hcz] at Hif
      rcases Int.lt_or_eq_of_le Hp'.2 with hlt | heq
      · have := hlag hlt; omega
      · exact heq.symm
    subst Hcpc
    wp_apply chan.wp_make1 (V := Unit) as %ch %γch ⟨#Hch, %Hchcap, Hchown⟩
    imod alloc_broadcast_chan (E := ⊤) iprop(True) γch ch $$ Hch Hchown with Hbc
    ihave #Hbc0 := ownBroadcastChan_Unknown _ _ _ _ $$ Hbc
    (try wp_auto)
    ipersist ch
    -- the barrier, tracked (item 17: the right's queue; the last job's `Post` passed through)
    iunfold mvcc.compactQueue at Hq
    icases Hq with ⟨%Ps, %p, %Qq, %Rq, Hq, #Hp, HRq, Hwq⟩
    imod (schedule.savedProp_alloc Qq) with ⟨%post, #Hpost⟩
    wp_func_lits
    (try wp_auto)
    wp_apply h0 γ.sch _ _ iprop(mvcc.compactCloser ch iprop(True) ∗ □ iprop(True)) Qq Qq
      $$ [] as %j #Hj
    · iframe #
      iunfold schedule.jobFnSpec
      iintro !> %ctx' %cd' !> %Φj ⟨Hrun, ⟨Hcl', -⟩, HQp, #Hctx', #HPD'⟩ HΦj
      iapply wp_fupd
      wp_auto_lc 2
      -- the barrier leases the fields' eighth for its run (item 17)
      imod mvcc.storeStopR_lease s γ _ $$ Hstop Hrun Hlc1 with ⟨Hfj, Hlease⟩
      wp_apply (h1 s γ ctx' cd' ch iprop(True) mvcc.q8 _) $$ [$Hcl' $Hfj] as Hfj
      · iframe #
        isplitl []
        · iunfold mvcc.barrierCtx
          iright
          iexact Hctx'
        imodintro; itrivial
      (try wp_auto)
      imod mvcc.jobLease_return s γ _ $$ Hlease Hfj Hlc2 with Hrun
      imodintro
      iapply HΦj
      iframe Hrun HQp
    · (try wp_auto)
      wp_apply h2 sci γ.sch j iprop(mvcc.compactCloser ch iprop(True) ∗ □ iprop(True)) Qq Qq
          (some (Ps, p, post)) $$ [Hbc Hq] as Hq
      · iframe #
        isplitl [Hbc]
        · iunfold mvcc.compactCloser
          isplitl [Hbc]
          · iexists γch; iexact Hbc
          imodintro; itrivial
        simp only [schedule.schedPre]
        iframe Hq Hp Hpost
      simp only [schedule.schedPost]
      ihave Hq : mvcc.compactQueue γ c' $$ [Hq HRq Hwq]
      · iunfold mvcc.compactQueue
        iexists Ps ++ [p], post, Qq, Rq
        simp only [List.append_assoc, List.cons_append, List.nil_append]
        iframe Hq Hpost HRq Hwq
      (try wp_auto)
      -- the caller's step at `ErrCompacted` (under `s.revMu`, its slot read)
      have hrc : sint.Z rev ≤ c' := by
        have hcz : sint.Z (W64 c' : w64) = c' := by obtain ⟨-, Hc'⟩ := Hc; word
        rw [hcz] at Hif; exact Hif
      iunfold mvcc.cmpCb at Hcb
      icases Hcb with ⟨-, Hce, -⟩
      imod Hce $$ %log [] HX with ⟨HX, HFce⟩
      · ipureintro; exact hrc
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hrev Hclog Hbucket Htoks Hlog Hcmp Hcrev HX HrstR]
      · iframe #
        inext
        iapply mvcc.revMuInv_close; iframe HrstR; iunfold mvcc.revMuBody
        iexists log, ntok, c'
        simp only [named]
        iframe
        iframe #
        ipureintro; exact ⟨Hne, Hbudget, Hc⟩
      (try wp_auto)
      icases mvcc.lockCtxM_pre γ P hk Pre Q Post $$ Hctx with ⟨Hback, HPre⟩
      iapply HΦ
      iframe HRTok Hback HS
      iright
      ileft
      iframe HFce
      isplitr
      · ipureintro; exact ⟨hrc, trivial, rfl⟩
      isplitr
      · iexists ecp; iframe Hcomp; ipureintro; rfl
      isplitl [HcmpM HcrevM]
      · iunfold mvcc.muInvAt; simp only [named]; iframe; iframe #; ipureintro; exact HcM.1
      isplitl [Hcr Hq Hcur Hfb Hfidx Hfsch Hfstop Hfrst Hstc Htok]
      · iapply (mvcc.compactRightR_iff s γ _).2
        iframe Hcr Hq
        iexists ⟨b, ti, GoInterface.ok sci, sstop⟩
        iframe Hsc Hstc Htok Hstop
        iunfold mvcc.fieldShareAt; simp only [named]; iframe Hcur Hfrst Hph0
        iunfold mvcc.storeFields; simp only [named]; iframe Hfb Hfidx Hfsch Hfstop
      isplitl [HPre]
      · iexact HPre
      iunfold mvcc.compactChan
      iexists γch
      iexact Hbc0
  · ihave #Hcert' := Hcert
    iunfold mvcc.idxCert at Hcert'
    icases Hcert' with ⟨-, %Hwf, -⟩
    have hc : sint.Z (W64 cp : w64) = cp := by
      obtain ⟨-, Hc'⟩ := Hc
      word
    rw [hc] at Hif
    have Hgt : cp < sint.Z rev := by omega
    have Hge : c' ≤ sint.Z rev := by
      by_cases hcp : cp < c'
      · exact hlag hcp
      · omega
    have hlen0 : 0 < log.length := List.length_pos_iff.mpr Hne
    have hl : sint.Z (W64 ((log.length : Int) - 1) : w64) = (log.length : Int) - 1 := by
      have := Hwf.2.1
      word
    rw [hl]
    wp_if_destruct
    · -- `rev > s.currentRev`: `ErrFutureRev`, the caller's step there (under `s.revMu`, its slot read;
      -- `KV.Compact.contract`, 2026-11-06: until then excluded by the caller's certificate)
      have hfr : (log.length : Int) - 1 < sint.Z rev := by omega
      iunfold mvcc.cmpCb at Hcb
      icases Hcb with ⟨-, -, Hfr⟩
      imod Hfr $$ %log [] HX with ⟨HX, HFfr⟩
      · ipureintro; exact ⟨hfr, Hc.2⟩
      (try wp_auto)
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hrev Hclog Hbucket Htoks Hlog Hcmp Hcrev HX HrstR Hlag]
      · iframe #
        inext
        iapply mvcc.revMuInv_closeL; iframe HrstR; iunfold mvcc.revMuBodyL
        iexists log, ntok, c', cp
        simp only [named]
        iframe Hrev Hclog Hbucket Htoks Hlog Hcmp Hcrev HX
        iframe #
        isplitr
        · ipureintro; exact Hne
        isplitr
        · ipureintro; exact Hbudget
        isplitl [Hlag]
        · iunfold mvcc.revLag; iframe Hlag; ipureintro; exact Hp'
        ipureintro; exact Hc
      (try wp_auto)
      icases mvcc.lockCtxM_pre γ P hk Pre Q Post $$ Hctx with ⟨Hback, HPre⟩
      iapply HΦ
      iframe HRTok Hback HS
      iright
      iright
      iframe HFfr HPre
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iexists ef; iframe Hfut; ipureintro; rfl
      isplitl [HcmpM HcrevM]
      · iunfold mvcc.muInvLag; simp only [named]; iframe HcmpM HcrevM; iframe #; ipureintro; exact HcM
      iapply (mvcc.compactRightR_iff s γ _).2
      iframe Hcr Hq
      iexists ⟨b, ti, GoInterface.ok sci, sstop⟩
      iframe Hsc Hstc Htok Hstop
      iunfold mvcc.fieldShareAt; simp only [named]; iframe Hcur Hfrst Hph0
      iunfold mvcc.storeFields; simp only [named]; iframe Hfb Hfidx Hfsch Hfstop
    · -- `s.compactMainRev = rev`, under both locks: the field and the revision's authority
      have hrl : sint.Z rev < log.length := by omega
      ihave Hcmpf : (s.[store, go!"compactMainRev"] ↦ (W64 cp : w64) : IProp GF) $$ [Hcmp HcmpM]
      · rw [show (DFrac.own 1 : DFrac) = DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half from
          dfrac_own_half_half 1]
        iapply ((typedPointsto_dfractional (GF := GF) _ _).dfractional _ _).2
        iframe
      wp_auto
      imod mvcc.crevUB_raise γ.idx c' (sint.Z rev) (by omega) $$ Hcr HcrevM Hcrev
        with ⟨Hcr, HcrevM, Hcrev, #Hlb⟩
      have hrw : (W64 (sint.Z rev) : w64) = rev := by word
      ihave Hcmpf2 : (s.[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half}
          (W64 (sint.Z rev) : w64) : IProp GF) $$ [Hcmpf]
      · rw [← dfrac_own_half_half 1, hrw]; iexact Hcmpf
      icases ((typedPointsto_dfractional (GF := GF) _ _).dfractional _ _).1 $$ Hcmpf2 with ⟨Hcmp, HcmpM⟩
      -- `SetScheduledCompact(s.b.BatchTx(), rev)`, over the store's contract with its compaction on
      -- (question 5's core stage, parts (2)-(4): its tokens, lock resource and write right)
      have hcM := mvcc.storeCmp_cmpM γ hcmp
      ihave #Hbk' := mvcc.isKeyBackendG_cmpOn b s γ Dep Ph (mvcc.hookFn γ) hcmp $$ Hbk
      -- (the snapshot image's (a); `KV.Compact.contract`) the store's one-shot loan of the write right
      -- at its values, for the put: the caller's ghost step fired there with the writer's state, the
      -- record updated and the tracked compaction re-pinned
      ihave Hsw := mvcc.compactLend_sched s γ hcM rev log c' cp S Fok Fce Ffr _ _ hS1 hS2 Hgt Hge
        hrl hpos1 $$ [Hlc3 HS Hcur HX Hcb]
      · iframe #; iframe Hlc3 HS Hcur HX Hcb
      icases (mvcc.physCmp_on s γ hcM).1 $$ HmwP with ⟨-, #Hreg⟩
      -- (M2, the storage side, Q1 (a)) the supply from the pre
      ihave #Hsup := (mvcc.kbWTSupplyM_on γ.kb hcM).1 $$ HsupM
      iunfold mvcc.isKeyBackendG at Hbk'
      icases Hbk' with ⟨%bi, %Hbi, -, -, #HB, #HForce, -⟩
      subst Hbi
      (try wp_auto)
      wp_bind (App (Val #(methods bi.ty go!"BatchTx" bi.v)) (Val #()))
      iapply HB $$ [] [-]
      · itrivial
      inext
      iintro %bt #Hbt
      -- a write-back token for the session, from the supply and a step's receipt
      wp_take_receipt as Hr1
      imod mvcc.kbWTSupply_take γ.kb $$ [$Hsup $Hr1] with Hwt1
      (try wp_auto)
      iunfold mvcc.isBatchTxG at Hbt
      icases Hbt with ⟨%Locked, %LockedO, #Hbt, -⟩
      ihave #HbtN := mvcc.batchTxSpecG_noNil _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ $$ Hbt
      have hrev0 : 0 ≤ sint.Z rev := by omega
      -- (`wp_apply` of a triple over `Locked`, a variable from an existential, leaves a synthetic
      -- `sorry`: bind and apply)
      wp_bind (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.SetScheduledCompact))
        (Val #(GoInterface.ok bt))) (Val #rev))
      -- (M2, item 31) by the hook's state: set, the caller's contract; unset (`restore()`'s resumed
      -- compaction), `LockInsideApply`'s nil arm (`batchTxSpecG`'s `lockNilSpec`, the unset hook lent)
      iapply (wp_wand (Φ := fun v => iprop(⌜v = #()⌝ ∗ mvcc.storeRT γ ∗ Post ∗ mvcc.lockBackM γ P hk ∗
        (mvcc.cmpLb γ (sint.Z rev) ∗ mvcc.storeRegd s γ ∗ S ∗
          mvcc.curAt γ (DFrac.own mvcc.q8.half) ⟨GoInterface.ok bi, ti, GoInterface.ok sci, sstop⟩ ∗
          mvcc.slotX γ 1 log (sint.Z rev) ∗ Fok))))
        $$ [Hctx HRTok Hwt1 Hlc2 Hsw]
      · cases hk with
        | some f =>
          rw [mvcc.lockCtxM_some, mvcc.lockBackM_some]
          icases Hctx with ⟨#HhookC, Hcs⟩
          -- the caller's hook is the store's
          imod mvcc.hookP_agree_lc ⊤ γ P Ph f $$ [$Hlc2 $HhookC $Hhook] with ⟨#HPP0, #HP0P⟩
          ihave #HhookC' := HhookC
          iunfold mvcc.hookOk at HhookC'
          icases HhookC' with ⟨-, #Hhf⟩
          iunfold mvcc.csContract at Hcs
          icases Hcs with ⟨HPre, #Htriple, Hupd⟩
          ihave #Htr0 : □ ({{ Ph ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) $$ []
          · iintro !> %Φ' !> ⟨HP0, Hpre⟩ HΦ'
            iapply Htriple $$ %Φ' [HP0 Hpre] HΦ'
            iframe Hpre
            iapply HP0P
            iexact HP0

          -- (question 5's core stage) the store's swap of its lock's resource for the right
          iapply (h3 bt (mvcc.bucketView γ) (mvcc.storeRT γ) (mvcc.storeWT γ) (mvcc.storePutOk γ)
              (mvcc.delKey γ) (mvcc.storeW s γ) Dep Locked Ph (mvcc.hookFn γ) (mvcc.storeRb γ)
              (mvcc.kbMWv γ.kb γ.bucket) iprop(True) (some f) rev Pre Q Post
              iprop(mvcc.cmpLb γ (sint.Z rev) ∗ mvcc.storeRegd s γ ∗ S ∗
                mvcc.curAt γ (DFrac.own mvcc.q8.half) ⟨GoInterface.ok bi, ti, GoInterface.ok sci, sstop⟩ ∗
                mvcc.slotX γ 1 log (sint.Z rev) ∗ Fok)
              hrev0) $$ [HPre Hupd HRTok Hwt1 Hsw]
          · rw [mvcc.lockArmS_some]
            iframe #
            iframe HPre HRTok Hwt1 Hsw
            iintro ⟨HQ, HW⟩
            imod Hupd $$ HQ with ⟨HP, HPost⟩
            ihave HP0 := HPP0 $$ HP
            imodintro
            iframe HP0 HPost HW

          inext
          iintro ⟨HRTok, HPost, HQl⟩
          iframe HRTok HPost HQl HhookC
          ipureintro; rfl
        | none =>
          rw [mvcc.lockCtxM_none, mvcc.lockBackM_none]
          icases Hctx with ⟨#HhP, Hnil, HPre, Hupd⟩
          -- the caller's invariant is the store's
          imod mvcc.hookP_agree_lc2 ⊤ γ P Ph $$ [$Hlc2 $HhP $Hhook] with ⟨#HPP0, #HP0P⟩
          ihave #Hbt' := Hbt
          iunfold mvcc.batchTxSpecG at Hbt'
          icases Hbt' with ⟨-, -, -, -, -, -, -, -, -, #HLN⟩
          iapply (h3 bt (mvcc.bucketView γ) (mvcc.storeRT γ) (mvcc.storeWT γ) (mvcc.storePutOk γ)
              (mvcc.delKey γ) (mvcc.storeW s γ) Dep Locked Ph (mvcc.hookFn γ) (mvcc.storeRb γ)
              (mvcc.kbMWv γ.kb γ.bucket) (mvcc.kbHookNil γ.kb) none rev Pre Q
              iprop(Post ∗ mvcc.kbHookNil γ.kb)
              iprop(mvcc.cmpLb γ (sint.Z rev) ∗ mvcc.storeRegd s γ ∗ S ∗
                mvcc.curAt γ (DFrac.own mvcc.q8.half) ⟨GoInterface.ok bi, ti, GoInterface.ok sci, sstop⟩ ∗
                mvcc.slotX γ 1 log (sint.Z rev) ∗ Fok)
              hrev0)
              $$ [HPre Hupd HRTok Hwt1 Hnil Hsw]
          · rw [mvcc.lockArmS_none]
            iframe #
            iframe HPre HRTok Hwt1 Hnil Hsw
            iintro ⟨HP0, Hpre, Hn⟩
            ihave HP := HP0P $$ HP0
            imod Hupd $$ [$HP $Hpre] with ⟨HP, HPost⟩
            ihave HP0 := HPP0 $$ HP
            imodintro
            iframe HP0 HPost Hn
          inext
          iintro ⟨HRTok, ⟨HPost, Hnil⟩, HQl⟩
          iframe HRTok HPost HQl HhP Hnil
          ipureintro; rfl
      iintro %v ⟨%Hv, HRTok, HPost, Hback, #HQl, #HQr, HS, Hcur, HX, HFok⟩
      subst Hv
      -- `s.b.ForceCommit()`, with a write-back token from the supply
      imod mvcc.kbWTSupply_take γ.kb $$ [$Hsup $Hr2] with Hwt2
      (try wp_auto)
      wp_bind (App (Val #(methods bi.ty go!"ForceCommit" bi.v)) (Val #()))
      iapply HForce $$ %iprop(True) %iprop(True) [HRTok Hwt2] [-]
      · iframe HRTok Hwt2
        isplitr; · itrivial
        iapply mvcc.storeReq_true
      inext
      iintro ⟨HRTok, -⟩
      (try wp_auto)
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hrev Hclog Hbucket Htoks Hlog Hcmp Hcrev HX HrstR]
      · iframe #
        inext
        iapply mvcc.revMuInv_close; iframe HrstR; iunfold mvcc.revMuBody
        iexists log, ntok, sint.Z rev
        simp only [named]
        rw [hrw]
        iframe
        iframe #
        ipureintro; exact ⟨Hne, Hbudget, by omega, by omega⟩
      (try wp_auto)
      iapply HΦ
      iframe HRTok Hback HS
      ileft
      iframe HFok
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl, Hgt, Hge⟩
      isplitl [HcmpM HcrevM]
      · iunfold mvcc.muInvAt; simp only [named]
        rw [hrw]
        iframe
        isplitr
        · iunfold mvcc.crevSafe; iexists log; iframe Hcert; ipureintro; exact hrl
        isplitr
        · iexact HpermR
        ipureintro; omega
      ihave Hq := mvcc.compactQueue_mono γ c' (sint.Z rev) (by omega) $$ Hq
      isplitl [Hcr Hq Hcur Hfb Hfidx Hfsch Hfstop Hfrst Hstc Htok]
      · iapply (mvcc.compactRightR_iff s γ _).2
        iframe Hcr Hq
        iexists ⟨GoInterface.ok bi, ti, GoInterface.ok sci, sstop⟩
        iframe Hsc Hstc Htok Hstop
        iunfold mvcc.fieldShareAt; simp only [named]; iframe Hcur Hfrst Hph0
        iunfold mvcc.storeFields; simp only [named]; iframe Hfb Hfidx Hfsch Hfstop

      iframe HPost
      isplitr [Hlag]
      · iunfold mvcc.compactJobPre
        iframe #
        isplitr
        · ipureintro; exact hcmp
        ipureintro
        exact ⟨by omega, hrl⟩
      iunfold mvcc.lagTok; iexact Hlag

end proof

end EtcdGrove
end Perennial
