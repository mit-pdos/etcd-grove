/-
Proof of the spec of the same name (the mvcc store's compaction, unit 5c).
The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__updateCompactRev
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.NewJob
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__compactBarrier
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.Scheduler__Schedule
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.SetScheduledCompact

@[expose] public section

set_option linter.unusedVariables false

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

/-- The compaction revision's whole authority (the right's half, `s.mu`'s and `s.revMu`'s
quarters) raised from `c` to `c2`, with a lower bound. -/
theorem crevUB_raise (γ : mvcc.IdxNames) (c c2 : Int) (h : c ≤ c2) :
    ⊢ mvcc.crevUB (GF := GF) γ (1 : Qp).half c -∗ mvcc.crevUB γ (1 : Qp).half.half c -∗
      mvcc.crevUB γ (1 : Qp).half.half c ==∗
      mvcc.crevUB γ (1 : Qp).half c2 ∗ mvcc.crevUB γ (1 : Qp).half.half c2 ∗
        mvcc.crevUB γ (1 : Qp).half.half c2 ∗ mvcc.crevLb γ c2 := by
  iintro H1 H2 H3
  ihave H23 := (mvcc.crevUB_split γ (1 : Qp).half.half (1 : Qp).half.half c).2 $$ [H2 H3]
  · iframe
  rw [Qp.half_add_half]
  ihave H := (mvcc.crevUB_split γ (1 : Qp).half (1 : Qp).half c).2 $$ [H1 H23]
  · iframe
  rw [Qp.half_add_half]
  iunfold mvcc.crevUB at H
  imod mono_nat_own_update (mvcc.crevN c2) (mvcc.crevN_mono h) $$ H with ⟨H, #Hlb⟩
  ihave H : mvcc.crevUB γ ((1 : Qp).half + ((1 : Qp).half.half + (1 : Qp).half.half)) c2 $$ [H]
  · rw [Qp.half_add_half, Qp.half_add_half]
    iunfold mvcc.crevUB
    iexact H
  icases (mvcc.crevUB_split γ _ _ c2).1 $$ H with ⟨H1, H23⟩
  icases (mvcc.crevUB_split γ _ _ c2).1 $$ H23 with ⟨H2, H3⟩
  imodintro
  iframe H1 H2 H3
  iunfold mvcc.crevLb
  iexact Hlb

theorem mvcc.store.updateCompactRev.wp_proof
    (h0 : schedule.NewJob.spec (GF := GF) (hG := hG))
    (h1 : mvcc.store.compactBarrier.spec (GF := GF) (hG := hG))
    (h2 : schedule.Scheduler.Schedule.spec (GF := GF) (hG := hG))
    (h3 : mvcc.SetScheduledCompact.spec (GF := GF) (hG := hG)) :
    mvcc.store.updateCompactRev.spec (GF := GF) (hG := hG) := by
  intro s γ rev c P f Pre Q Post logc hcmp
  wp_start as ⟨#Hs, #Hstop, HmuA, Hright, #HcertC, %HndC, #HhookC, Hcs⟩
  ihave #Hs' := Hs
  iunfold mvcc.isStore at Hs'
  iNamed Hs'
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  (try wp_auto)
  ipersist s
  wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$HrevMu] as ⟨Hwl, HR⟩
  wp_auto_lc 2
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.revMuInv s γ 1)) $$ Hlc1 HR with HR
  iunfold mvcc.revMuInv at HR
  icases HR with ⟨%log, %ntok, %c', HR⟩
  iNamed HR
  iunfold mvcc.muInvAt at HmuA
  iNamed HmuA
  iunfold mvcc.compactRight at Hright
  icases Hright with ⟨Hcr, Hq⟩
  ihave %Hcc := mvcc.crevUB_agree γ.idx _ _ c' c Hc.1 HcM $$ Hcrev Hcr
  subst Hcc
  ihave Hinit : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, ⟨%ecp, #Hcomp⟩, ⟨%ef, #Hfut⟩, -⟩
  ihave #Hschp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule $$ []
  · iPkgInit
  ihave #HisS := HisSched
  iunfold schedule.isScheduler at HisS
  icases HisS with ⟨#Hfifo, #Hlive⟩
  ihave #Hfifo' := Hfifo
  iunfold schedule.isFifo at Hfifo'
  icases Hfifo' with ⟨%Hnn, -⟩
  wp_auto
  wp_if_destruct
  · -- `rev <= s.compactMainRev`: `ErrCompacted`, a barrier job
    wp_apply chan.wp_make1 (V := Unit) as %ch %γch ⟨#Hch, %Hchcap, Hchown⟩
    imod alloc_broadcast_chan (E := ⊤) iprop(True) γch ch $$ Hch Hchown with Hbc
    ihave #Hbc0 := ownBroadcastChan_Unknown _ _ _ _ $$ Hbc
    (try wp_auto)
    ipersist ch
    wp_func_lits
    (try wp_auto)
    wp_apply h0 γ.sch _ _ iprop(mvcc.compactCloser ch iprop(True) ∗ □ iprop(True)) iprop(True) iprop(True)
      $$ [] as %j #Hj
    · iframe #
      iunfold schedule.jobFnSpec
      iintro !> %ctx' %cd' !> %Φj ⟨Hrun, ⟨Hcl', -⟩, -, #Hctx'⟩ HΦj
      wp_auto
      wp_apply (h1 s γ ctx' cd' ch iprop(True)) $$ [$Hcl']
      · iframe #
        isplitl []
        · iunfold mvcc.barrierCtx
          iright
          iexact Hctx'
        imodintro; itrivial
      (try wp_auto)
      iapply HΦj
      iframe Hrun
    cases ssched with
    | nil => exact absurd rfl Hnn
    | ok sci =>
      wp_auto
      wp_apply h2 sci γ.sch j iprop(mvcc.compactCloser ch iprop(True) ∗ □ iprop(True)) iprop(True)
          iprop(True) none $$ [Hbc] as -
      · iframe #
        isplitl [Hbc]
        · iunfold mvcc.compactCloser
          isplitl [Hbc]
          · iexists γch; iexact Hbc
          imodintro; itrivial
        simp only [schedule.schedPre]
        iframe #
        ipureintro; trivial
      (try wp_auto)
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hrev Hclog Hbucket Htoks Hlog Hcmp Hcrev]
      · iframe #
        inext
        iunfold mvcc.revMuInv
        iexists log, ntok, c'
        simp only [named]
        iframe
        iframe #
        ipureintro; exact ⟨Hne, Hbudget, Hc⟩
      (try wp_auto)
      iapply HΦ
      iright; ileft
      isplitr
      · ipureintro; exact ⟨by word, rfl⟩
      isplitr
      · iexists ecp; iframe Hcomp; ipureintro; rfl
      isplitl [HcmpM HcrevM]
      · iunfold mvcc.muInvAt; simp only [named]; iframe; iframe #; ipureintro; exact HcM
      isplitl [Hcr Hq]
      · iunfold mvcc.compactRight; iframe
      isplitl [Hcs]
      · iunfold mvcc.csContract at Hcs; icases Hcs with ⟨HPre, -, -⟩; iexact HPre
      iunfold mvcc.compactChan
      iexists γch
      iexact Hbc0
  · ihave #Hcert' := Hcert
    iunfold mvcc.idxCert at Hcert'
    icases Hcert' with ⟨-, -, %Hwf, -⟩
    have hc : sint.Z (W64 c' : w64) = c' := by
      have := Hwf.2.1
      word
    rw [hc] at Hif
    have Hgt : c' < sint.Z rev := by omega
    have hlen0 : 0 < log.length := List.length_pos_iff.mpr Hne
    have hl : sint.Z (W64 ((log.length : Int) - 1) : w64) = (log.length : Int) - 1 := by
      have := Hwf.2.1
      word
    rw [hl]
    wp_if_destruct
    · -- `rev > s.currentRev`: `ErrFutureRev`
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hrev Hclog Hbucket Htoks Hlog Hcmp Hcrev]
      · iframe #
        inext
        iunfold mvcc.revMuInv
        iexists log, ntok, c'
        simp only [named]
        iframe
        iframe #
        ipureintro; exact ⟨Hne, Hbudget, Hc⟩
      (try wp_auto)
      iapply HΦ
      iright; iright
      isplitr
      · ipureintro; exact ⟨Hgt, rfl, rfl⟩
      isplitr
      · iexists ef; iframe Hfut; ipureintro; rfl
      isplitr
      · iexists log; iframe Hcert; ipureintro; omega
      isplitl [HcmpM HcrevM]
      · iunfold mvcc.muInvAt; simp only [named]; iframe; iframe #; ipureintro; exact HcM
      isplitl [Hcr Hq]
      · iunfold mvcc.compactRight; iframe
      iunfold mvcc.csContract at Hcs; icases Hcs with ⟨HPre, -, -⟩; iexact HPre
    · -- `s.compactMainRev = rev`, under both locks: the field and the revision's authority
      have hrl : sint.Z rev < log.length := by omega
      ihave Hcmpf : (s.[store, go!"compactMainRev"] ↦ (W64 c' : w64) : IProp GF) $$ [Hcmp HcmpM]
      · rw [show (DFrac.own 1 : DFrac) = DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half from
          mvcc.own_half_half 1]
        iapply ((typedPointsto_dfractional (GF := GF) _ _).dfractional _ _).2
        iframe
      wp_auto
      imod crevUB_raise γ.idx c' (sint.Z rev) (by omega) $$ Hcr HcrevM Hcrev
        with ⟨Hcr, HcrevM, Hcrev, #Hlb⟩
      have hrw : (W64 (sint.Z rev) : w64) = rev := by word
      ihave Hcmpf2 : (s.[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half}
          (W64 (sint.Z rev) : w64) : IProp GF) $$ [Hcmpf]
      · rw [← mvcc.own_half_half 1, hrw]; iexact Hcmpf
      icases ((typedPointsto_dfractional (GF := GF) _ _).dfractional _ _).1 $$ Hcmpf2 with ⟨Hcmp, HcmpM⟩
      -- the caller's hook is the store's
      imod mvcc.hookIs_agree_lc ⊤ γ P Ph f fh $$ [$Hlc2 $HhookC $Hhook] with ⟨%Hfeq, #HPP0, #HP0P⟩
      subst Hfeq
      iunfold mvcc.csContract at Hcs
      icases Hcs with ⟨HPre, #Htriple, Hupd⟩
      ihave #Htr0 : □ ({{ Ph ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) $$ []
      · iintro !> %Φ' !> ⟨HP0, Hpre⟩ HΦ'
        iapply Htriple $$ %Φ' [HP0 Hpre] HΦ'
        iframe Hpre
        iapply HP0P
        iexact HP0
      -- `SetScheduledCompact(s.b.BatchTx(), rev)`
      ihave #Hbk' := mvcc.isKeyBackendG_cmp b s γ Dep Ph f hcmp $$ Hbk
      iunfold mvcc.isKeyBackendG at Hbk'
      icases Hbk' with ⟨%bi, %Hbi, -, -, #HB, #HForce, -⟩
      subst Hbi
      (try wp_auto)
      wp_bind (App (Val #(methods bi.ty go!"BatchTx" bi.v)) (Val #()))
      iapply HB $$ [] [-]
      · itrivial
      inext
      iintro %bt #Hbt
      (try wp_auto)
      iunfold mvcc.isBatchTxG at Hbt
      icases Hbt with ⟨%Locked, %LockedO, #Hbt, -⟩
      have hrev0 : 0 ≤ sint.Z rev := by omega
      -- (`wp_apply` of a triple over `Locked`, a variable from an existential, leaves a synthetic
      -- `sorry`: bind and apply)
      wp_bind (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.SetScheduledCompact))
        (Val #(GoInterface.ok bt))) (Val #rev))
      iapply (h3 bt (mvcc.bucketView γ) (mvcc.delKey γ) (mvcc.writerRes s γ) Dep Locked Ph f rev Pre Q
          Post hrev0) $$ [HPre Hupd]
      · iframe #
        iframe HPre
        isplitr
        · iunfold mvcc.batchTxSpec; iexact Hbt
        iintro ⟨HQ, HW⟩
        imod Hupd $$ HQ with ⟨HP, HPost⟩
        ihave HP0 := HPP0 $$ HP
        iunfold mvcc.writerRes at HW
        icases HW with ⟨%ilog, %ntok', HW⟩
        iNamed HW
        iunfold mvcc.compactRes at Hcres
        icases Hcres with ⟨%sch, %fin, %n, Hmeta, Hfin, %Hn⟩
        iunfold mvcc.metaCompact at Hmeta
        imod ghostVar_update (some rev, fin) γ.cmeta _ $$ Hmeta with Hmeta
        imodintro
        iframe HP0 HPost
        iunfold mvcc.writerRes
        iexists ilog, ntok'
        simp only [named]
        iframe
        iframe #
        isplitr
        · ipureintro; exact Hbudget
        isplitr
        · ipureintro; exact Hne
        iunfold mvcc.compactRes
        iexists (some rev), fin, n
        iunfold mvcc.metaCompact
        iframe
        ipureintro; exact Hn
      inext
      iintro HPost
      (try wp_auto)
      -- `s.b.ForceCommit()`
      wp_bind (App (Val #(methods bi.ty go!"ForceCommit" bi.v)) (Val #()))
      iapply HForce $$ [] [-]
      · itrivial
      inext
      iintro -
      (try wp_auto)
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hrev Hclog Hbucket Htoks Hlog Hcmp Hcrev]
      · iframe #
        inext
        iunfold mvcc.revMuInv
        iexists log, ntok, sint.Z rev
        simp only [named]
        rw [hrw]
        iframe
        iframe #
        ipureintro; exact ⟨Hne, Hbudget, by omega, by omega⟩
      (try wp_auto)
      iapply HΦ
      ileft
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl, Hgt⟩
      isplitl [HcmpM HcrevM]
      · iunfold mvcc.muInvAt; simp only [named]
        rw [hrw]
        iframe
        isplitr
        · iunfold mvcc.crevSafe; iexists logc; iframe HcertC; ipureintro; exact HndC
        ipureintro; omega
      isplitl [Hcr Hq]
      · iunfold mvcc.compactRight
        iframe Hcr
        iapply mvcc.compactQueue_mono γ c' (sint.Z rev) (by omega) $$ Hq
      iframe HPost
      -- the caller's `NoDelPutAt`, for the committed log (`crevSafe_cert`)
      ihave %Hnd' : ⌜mvcc.NoDelPutAt log (sint.Z rev)⌝ $$ []
      · iapply mvcc.crevSafe_cert γ (sint.Z rev) log hrl $$ [Hcert]
        iframe Hcert
        iunfold mvcc.crevSafe; iexists logc; iframe HcertC; ipureintro; exact HndC
      iunfold mvcc.compactJobPre
      iframe #
      isplitr
      · ipureintro; exact hcmp
      ipureintro; exact ⟨by omega, hrl, Hnd'⟩

end proof

end EtcdGrove
end Perennial
