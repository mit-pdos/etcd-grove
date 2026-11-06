/-
Proof of `Spec/.../mvcc/store__Restore.lean` (`kvstore.go`; the restore plan's R5f; the trust
boundary until then: D22m decided, D22 receiver epochs S6). Lean-first (no Rocq counterpart). By the
mode: in compaction mode `RestoreOn.lean`'s proof (M2's item 15); off, the proof below.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.CmpSteps
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Restore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__restore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreNC
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newTreeIndex
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.Scheduler__Stop
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.NewFIFOScheduler
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreMoves
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreOn
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__compactLockfree

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

omit package_sem in
/-- **The restored store's cut** (track A, 2026-11-06): at the restored log `L`, the image's entries
`ents` cut at its records' compaction revision (`restoreImageM`'s), nothing deleted yet, the image's
records `r` and the job's cursor at the finished record, before every entry, the tracked
compaction's pure fact holds. -/
theorem mvcc.cmpOk_restored (L : mvcc.Log) (hb : mvcc.LogB L) (r : mvcc.CmpRecs)
    (ents : List mvcc.KvEnt) (hrec : mvcc.recsOk L r) (hpos : mvcc.recsPos r)
    (hcut : mvcc.entsCutAt L r.crev ents) :
    mvcc.snap.cmpOk L (mvcc.bucketOfEnts ents) (∅ : backend.VData) r
      (r.finRev, (⟨W64 0, W64 0⟩ : mvcc.Rev)) := by
  have hfb := mvcc.CmpRecs.finRev_bounds L r hrec
  refine ⟨ents, hcut, ?_, hrec, hpos, ?_, ?_, hfb.1, hfb.2, Int.le_refl _⟩
  · intro k
    simp [mvcc.snap.physLookup]
  · intro k h; simp at h
  · intro e he hlt _
    have hbd := mvcc.logEnts_bounds L hb.1 hb.2 0 L.length (Nat.le_refl _) e he
    unfold mvcc.Rev.lt at hlt
    have h0 : sint.Z (W64 0) = 0 := by decide
    simp only [h0] at hlt
    omega

/-- **The restored store's tracked compaction** (track A, 2026-11-06; in place of `cmpTrack_new_M1`
at `store.Restore`): the image's values' halves at its records (`restoreImageM`'s on-arm, from the
open's exact `fkCl`), nothing deleted, and the new names' fresh ghost state at the records (the
compaction revision's half, the job cursor's half at the finished record and the lower bounds'
authority at the compaction revision). -/
theorem mvcc.cmpTrack_restored (γ : mvcc.StoreNames) (d' : mvcc.KBReal) (hk : γ.kb = some d')
    (hon : d'.cm = true) (L : mvcc.Log) (hb : mvcc.LogB L) (r : mvcc.CmpRecs)
    (ents : List mvcc.KvEnt) (hrec : mvcc.recsOk L r) (hpos : mvcc.recsPos r)
    (hcut : mvcc.entsCutAt L r.crev ents) :
    mvcc.kbVals (GF := GF) (some d') (mvcc.recBytes r.fin, mvcc.recBytes r.sched) ∅ ∗
      ghostVar γ.rcv (1 : Qp).half r.crev ∗
      ghostVar γ.jc (1 : Qp).half (r.finRev, (⟨W64 0, W64 0⟩ : mvcc.Rev)) ∗
      monoNatAuthOwn γ.rcl 1 (mvcc.crevN r.crev) ⊢
      mvcc.cmpTrack γ L (mvcc.bucketOfEnts ents) r := by
  unfold mvcc.cmpTrack
  rw [hk]
  simp only [hon, ↓reduceIte, mvcc.kbVals]
  iintro ⟨⟨Hf, Hd⟩, Hr, Hj, Hl⟩
  iframe Hf Hr Hl
  iexists ∅, (r.finRev, (⟨W64 0, W64 0⟩ : mvcc.Rev))
  iframe Hd Hj
  ipureintro; exact mvcc.cmpOk_restored L hb r ents hrec hpos hcut

theorem mvcc.store.Restore.wp_proof
    (hStop : schedule.Scheduler.Stop.spec (GF := GF) (hG := hG))
    (hNewIdx : mvcc.newTreeIndex.spec (GF := GF) (hG := hG))
    (hFifo : schedule.NewFIFOScheduler.spec (GF := GF) (hG := hG))
    (hRestore : mvcc.store.restore.spec (GF := GF) (hG := hG))
    (hCLF : mvcc.store.compactLockfree.spec (GF := GF) (hG := hG)) :
    mvcc.store.Restore.spec (GF := GF) (hG := hG) := by
  intro s γ b' d' γb' P' L R c r Ls Rr hkH dqh PreH QH PostH XH YH hR hcr hwq
  by_cases hon : mvcc.kbCmpM γ.kb
  · -- (M2's item 15) on: both backends compact
    wp_start as ⟨#Hrc0, #HpF, #HpC, #Hs, %Hkb, Hright, Hfs, Hwsd, Hfrag, Hown, #HcL,
      HlogQ, #Hok', HbkT, #HcrT, Himg, -, Hrr, Hreg, Hsr, #Hwts, HrH, Hrts, HLo, %Hlok, Hfr, Hcb⟩
    -- the mode: both backends compact
    obtain ⟨d, hd, hcm⟩ := Hkb
    have hdon : d.cm = true := by rw [hd] at hon; exact hon
    have hd'on : d'.cm = true := by rw [hcm]; exact hdon
    have hj1 : mvcc.nJobRd γ.kb = 1 := by rw [hd]; simp [mvcc.nJobRd, hdon]
    ihave #Hrc := (mvcc.restoreRcptM_on d' _ hd'on).1 $$ Hrc0
    icases (mvcc.restoreImageM_on d' γb' _ r hd'on).1 $$ Himg with
      ⟨%ents, Hview, ⟨Hrecs, Hvals⟩, -, %Himg⟩
    obtain ⟨hrec, hpos, hcut⟩ := Himg
    ihave Hsr := (mvcc.kbSRM_on (some d') hd'on).1 $$ Hsr
    icases (mvcc.writerOwn_on γ hj1).1 $$ Hown with ⟨HrtOld, Htkr⟩
    have hlen := mvcc.restoreLogOk_len hR
    have hlb : mvcc.LogB ([[], []] ++ R) := by
      obtain ⟨-, ⟨-, hlen1, -, hcs⟩⟩ := hR
      exact ⟨by omega, hcs⟩
    have hcl : r.crev < (([[], []] ++ R).length : Int) := mvcc.recsOk_crev_lt _ r hrec hlen.1
    have hcge : -1 ≤ r.crev := mvcc.CmpRecs.crev_ge _ r hrec
    have hfb := mvcc.CmpRecs.finRev_bounds _ r hrec
    ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule $$ []
    · iPkgInit
    ihave #Hs' := Hs
    iunfold mvcc.isStore at Hs'
    iNamed Hs'
    wp_auto
    wp_apply wp_with_defer as %defer defer
    (try wp_auto)
    -- `s.mu.Lock()`: all of `s.mu`'s resource
    wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hwl, HP⟩
    wp_auto_lc 1
    imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.muInv s γ 1)) $$ Hlc1 HP with HP
    iunfold mvcc.muInv at HP
    icases HP with ⟨%c0, Hma, Hwr, Hfs2⟩
    iunfold mvcc.muInvAt at Hma
    iNamed Hma
    -- the right, opened: its half of the compaction revision's authority agrees with `s.mu`'s
    icases mvcc.restoreRightM_openOn s γ c hon $$ Hright
      with ⟨%o, #Hstc, Hstcl, Htok, Hq, Hf8, #HsR, Hcu⟩
    icases (mvcc.crevUB_max γ.idx _ c).1 $$ Hcu with Hcu
    icases mvcc.crevUB_agree' γ.idx _ _ c0 (max c (-1)) HcM (by omega) $$ [HcrevM Hcu]
      with ⟨HcrevM, Hcu, %Hc0⟩
    · iframe HcrevM Hcu
    ihave Hcu : mvcc.crevUB (GF := GF) γ.idx (1 : Qp).half c0 $$ [Hcu]
    · rw [Hc0]; iexact Hcu
    have hc0r : c0 ≤ r.crev := by omega
    -- the closer's eighth reads `s.stopc` and `s.fifoSched`
    icases mvcc.fieldShareAt_acc s γ mvcc.q8 o $$ Hf8 with ⟨Hflds8, #Hph8, Hf8b⟩
    iunfold mvcc.storeFields at Hflds8
    iNamed Hflds8
    ihave #Hph' := Hph8
    iunfold mvcc.physOk at Hph'
    iNamed Hph'
    obtain ⟨b, ti0, ssched, sstop⟩ := o
    try simp only
    (try wp_auto)
    -- `close(s.stopc)`
    iunfold mvcc.stopCloser at Hstcl
    icases Hstcl with ⟨%γc, Hstcl⟩
    wp_apply +noauto wp_broadcast_chan_close _ γc iprop(True) $$ [$Hstcl] as #Hdone
    · imodintro; itrivial
    ihave #Hsp := mvcc.stopPay_of_done γ.sx γ.sch ⟨b, ti0, ssched, sstop⟩ γc $$ [$Hpay $Hdone]
    wp_auto_lc 2
    -- `s.fifoSched.Stop()`: the last job's token comes back, with the old job's budgets
    ihave #Hfifo' := HisSched
    iunfold schedule.isFifo at Hfifo'
    icases Hfifo' with ⟨%Hnn, -⟩
    cases ssched with
    | nil => exact absurd rfl Hnn
    | ok fi =>
    iunfold mvcc.compactQueue at Hq
    icases Hq with ⟨%Ps, %p, %Q, %R', Hq, #HpQ, HR', HQR⟩
    (try wp_auto)
    wp_apply hStop fi γ.sch (Ps ++ [p]) $$ [Htok Hq] as ⟨HlastP, Hsdone⟩
    · iframe; iframe #
    imod mvcc.compactQueue_stopped γ c Ps p Q R' $$ HlastP HpQ HR' HQR Hlc1 with Hct
    iunfold mvcc.compactTok at Hct
    icases Hct with ⟨-, Hjob, -⟩
    -- the fields whole: the closer's eighth back, the jobs' reclaimed
    ihave Hf8 := Hf8b $$ [Hfb Hfidx Hfsch Hfstop]
    · iunfold mvcc.storeFields; simp only [named]; iframe Hfb Hfidx Hfsch Hfstop
    imod mvcc.storeStopR_reclaim s γ _ $$ HsR Hsdone Hlc2 with Hf8'
    have hs8 := (mvcc.fieldShareAt_split (GF := GF) s γ mvcc.q8 mvcc.q8
      ⟨b, ti0, GoInterface.ok fi, sstop⟩).2
    rw [mvcc.q8_add] at hs8
    ihave Hf4 := hs8 $$ [Hf8 Hf8']
    · iframe Hf8 Hf8'
    ihave Hfs := mvcc.fieldShare_gather s γ _ $$ [Hfs2 Hfs Hf4]
    · iframe Hfs2 Hfs Hf4
    iunfold mvcc.fieldShareAt at Hfs
    iNamed Hfs
    iunfold mvcc.storeFields at Hflds
    iNamed Hflds
    (try wp_auto)
    -- `s.kvindex = newTreeIndex(s.lg)`
    imod mvcc.idx_renew γ.idx (mvcc.evsOf (([[], []] ++ R) ++ [[]])).length
      with ⟨%nv, %cm, Hnauth, #Hnlb, Hcm⟩
    imod mvcc.crevLb_neg (⟨γ.idx.hist, nv, γ.idx.log, γ.idx.crev, cm⟩ : mvcc.IdxNames) with #Hclb
    ihave #HcL' := HcL
    iunfold mvcc.idxCert at HcL'
    icases HcL' with ⟨-, -, #Hllb0, -⟩
    wp_apply (hNewIdx ⟨γ.idx.hist, nv, γ.idx.log, γ.idx.crev, cm⟩ lg _ L) $$ [Hnauth Hcm]
      as %ti ⟨Hix, Hig, Hcmp0⟩
    · iframe Hnauth Hcm; iframe #; ipureintro; exact Hlgnn
    (try wp_auto)
    -- the revision round: the takeover at the store's compaction revision `c0`
    wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$HrevMu] as ⟨HwlR, HR⟩
    wp_auto_lc 2
    imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.revMuInv s γ 1)) $$ Hlc1 HR with HR
    ihave Hfr : mvcc.slotFr (GF := GF) γ $$ [Hfr]
    · iunfold mvcc.slotFr; iexact Hfr
    -- (with the client's step, `restoreCb`: `s.revMu`'s slot and the writer's view at the restored
    -- log)
    imod (mvcc.restore_takeover s γ ⟨b, ti0, GoInterface.ok fi, sstop⟩ L ([[], []] ++ R) c0 r.crev Rr
        HcM hwq) $$
        Hlc2 Hwi HR Hfrst Hcur Hwr HcL HlogQ HcrevM HcmpM Hfr Hcb
      with ⟨⟨%v0, Hcr⟩, Hcm, Hrst, Hcur, HcurR, HcurW, HcrevM, Hheld, #Hhlb, HfzK, ⟨%cw, Hwc⟩, %hLR,
        HXn, HYa, HYp, #HnlLb, HRr⟩
    -- (track A, request 2) the writer's compaction revision's ghost, `s.mu`'s half and the old
    -- writer's, moved to the restored compaction revision; `s.mu`'s half goes into its resource
    imod mvcc.api.wcrPart_update γ.api _ _ (Qp.half_add_half 1) c0 cw r.crev $$ [HwcM Hwc]
      with ⟨HwcM, HwcY⟩
    · iframe HwcM Hwc
    (try wp_auto)
    imod dghostVar_update true γ.rst false $$ Hrst with Hrst
    have hrst := (dghostVar_fractional (GF := GF) γ.rst true).fractional (1 : Qp).half (1 : Qp).half
    rw [Qp.half_add_half] at hrst
    icases hrst.1 $$ Hrst with ⟨HrstL, Hrst⟩
    icases (mvcc.typedPointsto_parts _ _ (1 : Qp).half (1 : Qp).half (Qp.half_add_half 1)).1
      $$ Hcr with ⟨HcrL, Hcr⟩
    icases (mvcc.typedPointsto_parts _ _ (1 : Qp).half (1 : Qp).half (Qp.half_add_half 1)).1
      $$ Hcm with ⟨HcmL, Hcm⟩
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$HwlR HrstL HcrL HcmL]
    · inext
      iunfold mvcc.revMuInv
      iexists true
      simp only [↓reduceIte]
      iframe HrstL
      iunfold mvcc.revMuRest
      iexists _, _
      iframe HcrL HcmL
    (try wp_auto)
    -- the compaction revision raised to the restored one (all of its authority is here)
    imod mvcc.restoreHeld_raise γ ([[], []] ++ R) c0 r.crev hc0r $$ Hcu HcrevM Hheld
      with ⟨Hcu, HcrevM, Hheld, #Hclb2, #Hllb⟩
    -- `s.fifoSched = schedule.NewFIFOScheduler(s.lg)`; `s.stopc = make(chan struct{})`
    imod (dghostVar_alloc (GF := GF) (null : Loc)) with ⟨%γx', Hx'⟩
    wp_apply hFifo _ (mvcc.stopPay γx') $$ [] as %sc ⟨%γs, %n₀, %p₀, #HisFifo, HsStop, Hq0, #Hp0, #Hpi⟩
    · ipureintro; exact Hlgnn
    (try wp_auto)
    wp_apply +noauto chan.wp_make1 (V := Unit) as %stopc %γstop ⟨#Hstc', %Hstcap, Hstown⟩
    imod dghostVar_update stopc γx' _ $$ Hx' with Hx'
    imod dghostVar_persist γx' 1 stopc $$ Hx' with #Hx'
    wp_auto_lc 5
    imod alloc_broadcast_chan (E := ⊤) iprop(True) γstop stopc $$ Hstc' Hstown with Hstop
    ihave #Hstop0 := ownBroadcastChan_Unknown _ _ _ _ $$ Hstop
    -- the new backend's names, fresh (the write right's key too: the new store compacts)
    imod (saved_prop_alloc (GF := GF) P' DFrac.discard DFrac.valid_discard) with ⟨%γh', #Hh'⟩
    imod ghostVar_alloc (GF := GF) () with ⟨%γwk', Hwk'⟩
    imod ghostVar_alloc (GF := GF) ([[], []] ++ R) with ⟨%γwv', Hwv'⟩
    -- (track A, 2026-11-06) the meta keys' record and the finished counter at the image's records
    imod ghostVar_alloc (GF := GF) ((r.sched, r.fin) : Option w64 × Option w64) with ⟨%γm', Hmeta'⟩
    imod mono_nat_own_alloc (GF := GF) (mvcc.crevN (mvcc.finRev r.fin)) with ⟨%γfin', Hfin', -⟩
    imod ghostVar_alloc (GF := GF) true with ⟨%γmk', Hmk'⟩
    imod ghostVar_alloc (GF := GF) r.crev with ⟨%γrcv', Hrcv'⟩
    icases ghostVar_halves γrcv' _ $$ Hrcv' with ⟨Hrcv', HrcvY⟩
    -- (the job, 2026-11-06; track A) the job's cursor at the finished record, before every entry,
    -- and the lower bounds' authority at the records' compaction revision
    imod ghostVar_alloc (GF := GF) ((r.finRev, (⟨W64 0, W64 0⟩ : mvcc.Rev)) : Int × mvcc.Rev)
      with ⟨%γjc', Hjc'⟩
    icases ghostVar_halves γjc' _ $$ Hjc' with ⟨Hjc1', Hjc2'⟩
    imod mono_nat_own_alloc (GF := GF) (mvcc.crevN r.crev) with ⟨%γrcl', Hrcl', -⟩
    obtain ⟨p', hnv, hcmn, hb, hh, hk, hm, hfin, hs, hwk, hwv, hmk, hsx, hrcv, hjc, hrcl⟩ :
        ∃ p' : mvcc.PhysNames,
        p'.nev = nv ∧ p'.cmp = cm ∧ p'.bucket = γb' ∧ p'.hook = γh' ∧ p'.kb = some d' ∧
        p'.cmeta = γm' ∧ p'.fin = γfin' ∧ p'.sch = γs ∧ p'.wk = γwk' ∧ p'.wv = γwv' ∧
        p'.mwk = γmk' ∧ p'.sx = γx' ∧ p'.rcv = γrcv' ∧ p'.jc = γjc' ∧ p'.rcl = γrcl' :=
      ⟨⟨nv, cm, γb', γh', γ.hookFn, some d', γm', γfin', γs, γwk', γwv', γmk', γx', γrcv', γjc',
          γrcl'⟩,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hpb : p'.bucket = γb' ∧ p'.kb = some d' := ⟨hb, hk⟩
    have hon' : mvcc.kbCmpM (γ.withPhys p').kb := by
      simp only [mvcc.StoreNames.withPhys_kb, hk]; exact hd'on
    rw [← hnv, ← hcmn, ← hh, ← hm, ← hfin, ← hs, ← hwk, ← hwv, ← hmk]
    rw [show (⟨γ.idx.hist, p'.nev, γ.idx.log, γ.idx.crev, p'.cmp⟩ : mvcc.IdxNames) =
      (γ.withPhys p').idx from rfl]
    -- the new index's lock at the restored compaction revision
    ihave #Hclb3 := mvcc.crevLb_to γ p' r.crev $$ Hclb2
    imod mvcc.idxLockG_raise (γ.withPhys p').idx _ r.crev ([[], []] ++ R) hcl $$ Hig Hcmp0 Hclb3 []
      with ⟨Hig, Hcmp'⟩
    · simp only [mvcc.StoreNames.withPhys_idx_log]; iexact Hllb
    -- the new backend's view of the cut entries: half for `restore`, quarters for the writer and
    -- its pin
    icases mvcc.kbViewC_halves _ _ _ $$ Hview with ⟨HviewR, HviewW⟩
    ihave HviewR : mvcc.bucketViewC (GF := GF) (γ.withPhys p') (1 : Qp).half
        (mvcc.bucketOfEnts ents) $$ [HviewR]
    · iunfold mvcc.bucketViewC
      simp only [mvcc.StoreNames.withPhys_kb, mvcc.StoreNames.withPhys_bucket, hk, hb]
      iexact HviewR
    ihave HviewW : mvcc.bucketView (GF := GF) (γ.withPhys p') (1 : Qp).half
        (mvcc.bucketOfEnts ents) $$ [HviewW]
    · iapply mvcc.bucketViewC_bucketView
      iunfold mvcc.bucketViewC
      simp only [mvcc.StoreNames.withPhys_kb, mvcc.StoreNames.withPhys_bucket, hk, hb]
      iexact HviewW
    icases (mvcc.bucketView_quarters _ _).1 $$ HviewW with ⟨HviewW, HviewP⟩
    -- (the snapshot image's (a)) `writerRes`'s eighth and the compaction's part's
    icases (mvcc.bucketView_halves _ (1 : Qp).half.half _).1 $$ HviewW with ⟨HviewW, HviewC⟩
    ihave #HcrT' := HcrT $$ %p' %hpb
    ihave Hnc : mvcc.kbRecs (GF := GF) (γ.withPhys p').kb (γ.withPhys p').bucket r $$ [Hrecs]
    · simp only [mvcc.StoreNames.withPhys_kb, mvcc.StoreNames.withPhys_bucket, hk, hb]
      iexact Hrecs
    -- the new backend's reader tokens: `restore`'s, the job's, the monitor's and the new pool's
    icases mvcc.rep_take3 _ $$ Hrts with ⟨Hrt1, HjRT, Hnew, Hrts⟩
    ihave Hrt1 : mvcc.storeRT (GF := GF) (γ.withPhys p') $$ [Hrt1]
    · simp only [mvcc.storeRT, mvcc.StoreNames.withPhys_kb, hk]; iexact Hrt1
    ihave Hnew : mvcc.storeRT (GF := GF) (γ.withPhys p') $$ [Hnew]
    · simp only [mvcc.storeRT, mvcc.StoreNames.withPhys_kb, hk]; iexact Hnew
    ihave Hrts : [∗list] _x ∈ List.replicate (mvcc.nReaders - 3) (),
        mvcc.storeRT (GF := GF) (γ.withPhys p') $$ [Hrts]
    · simp only [mvcc.storeRT, mvcc.StoreNames.withPhys_kb, hk]; iexact Hrts
    -- `compactMainRev`: a quarter for `restore`, a quarter kept (the lock's part agrees)
    icases (mvcc.typedPointsto_halves _ _ _).1 $$ Hcm with ⟨HcmR, HcmK⟩
    -- the watchable store's deposit: half for the switch, a quarter for the lag, a quarter kept
    iunfold mvcc.wsDep at Hwsd
    have hw := (ghostVar_fractional (GF := GF) γ.wsd ()).fractional (1 : Qp).half (1 : Qp).half
    rw [Qp.half_add_half] at hw
    icases hw.1 $$ Hwsd with ⟨HwsdS, Hwsd2⟩
    have hw2 := (ghostVar_fractional (GF := GF) γ.wsd ()).fractional (1 : Qp).half.half
      (1 : Qp).half.half
    rw [Qp.half_add_half] at hw2
    icases hw2.1 $$ Hwsd2 with ⟨HwsdL, HwsdK⟩
    ihave #Hiwlb : mvcc.idxWriterLb (GF := GF) (γ.withPhys p').idx ([[], []] ++ R) $$ []
    · iunfold mvcc.idxWriterLb
      simp only [mvcc.StoreNames.withPhys_idx_hist, mvcc.StoreNames.withPhys_idx_nev]
      iframe Hhlb Hnlb
      ipureintro; exact hR.2
    -- the compaction's fresh record and the write right's key
    icases mvcc.mwSlot_alloc (γ.withPhys p') $$ [Hmk'] with ⟨Hslot, Hmwr⟩
    · simp only [mvcc.StoreNames.withPhys_mwk]; iexact Hmk'
    -- the tracked compaction at the image's records (track A: the values' halves from the image)
    ihave HtrC : mvcc.cmpTrack (GF := GF) (γ.withPhys p') ([[], []] ++ R) (mvcc.bucketOfEnts ents)
        r $$ [Hvals Hrcv' Hjc2' Hrcl']
    · iapply mvcc.cmpTrack_restored (γ.withPhys p') d' (by simp only [mvcc.StoreNames.withPhys_kb, hk])
        hd'on _ hlb r ents hrec hpos hcut
      rw [mvcc.StoreNames.withPhys_rcv, mvcc.StoreNames.withPhys_jc, mvcc.StoreNames.withPhys_rcl,
        hrcv, hjc, hrcl]
      iframe Hvals Hrcv' Hjc2' Hrcl'
    ihave Hcres : mvcc.compactRes (GF := GF) (γ.withPhys p') ([[], []] ++ R)
        $$ [Hmeta' Hfin' Hslot HviewC HtrC]
    · iunfold mvcc.compactRes
      iexists r.sched, r.fin, mvcc.crevN (mvcc.finRev r.fin), mvcc.bucketOfEnts ents
      iunfold mvcc.metaCompact
      simp only [mvcc.StoreNames.withPhys_cmeta, mvcc.StoreNames.withPhys_fin]
      iframe Hmeta' Hfin' Hslot HviewC HtrC
      ipureintro; exact Nat.le_refl _
    ihave Hrr : mvcc.kbRegRight (GF := GF) p'.kb $$ [Hrr]
    · rw [hk]; iexact Hrr
    have hx : (W64 r.finRev : w64) = r.fin.getD (W64 (-1)) := by
      rw [← mvcc.CmpRecs.finRev_getD, mvcc.W64_sint']
    have hdq : ∀ x, r.fin = some x →
        DFrac.own (1 : Qp).half.half • (DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half.half) =
          DFrac.own 1 := by
      intro _ _
      rw [DFrac.op_own, DFrac.op_own]
      congr 1
      simp only [Qp.ext_iff, Qp.val_add, Qp.val_half, Qp.val_one]; grind
    -- `s.restore()`
    have hR' := hRestore s (γ.withPhys p') b' le ti lg (1 : Qp).half P' (mvcc.hookFn (γ.withPhys p'))
        iprop(mvcc.storeRT (γ.withPhys p') ∗ mvcc.restoreRegM d') (mvcc.storeWT (γ.withPhys p'))
        (mvcc.storeW s (γ.withPhys p')) (mvcc.kbWi (γ.withPhys p').kb) iprop(True)
        (mvcc.kbRecs (γ.withPhys p').kb (γ.withPhys p').bucket r) (mvcc.storeCmp (γ.withPhys p'))
        (mvcc.storePutOk (γ.withPhys p')) (mvcc.storeRb (γ.withPhys p'))
        (mvcc.storeBt (γ.withPhys p')) (mvcc.kbMWv (γ.withPhys p').kb (γ.withPhys p').bucket)
        (mvcc.kbSR (γ.withPhys p').kb) (mvcc.kbSRh (γ.withPhys p').kb) (DFrac.own 1) (DFrac.own 1) R
        (mvcc.restoreOnP0 s γ) (mvcc.restoreOnP s γ (r.fin.getD (W64 (-1))))
        (mvcc.restoreOnK s γ (r.fin.getD (W64 (-1))))
        (mvcc.restoreOnQ s γ p' ⟨b', ti, sc, stopc⟩ R r ti)
        (DFrac.own (1 : Qp).half.half) (DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half.half)
        (1 : Qp).half (1 : Qp).half r ents (mvcc.restoreOnFin s γ p' ⟨b', ti, sc, stopc⟩ d' R r hkH dqh PostH YH)
        false γ.leases Ls hR (Qp.half_add_half 1) hrec (fun h => absurd h Bool.false_ne_true) hdq hcut
    -- `restore()`'s first round, for the finished record: `compactMainRev` written under the lock
    ihave HFw : mvcc.revFinW (GF := GF) s (DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half.half)
        r.fin (mvcc.restoreOnP0 s γ) (mvcc.restoreOnP s γ (r.fin.getD (W64 (-1)))) $$ []
    · iunfold mvcc.revFinW
      cases hf : r.fin with
      | none =>
        simp only [Option.getD_none]
        iintro H
        iunfold mvcc.restoreOnP0 at H
        iunfold mvcc.restoreOnP
        icases H with ⟨Hr, Hl1, Hl2, -, Hc⟩
        iframe Hr Hl1 Hl2 Hc
      | some x =>
        simp only [Option.getD_some]
        iexists iprop(sync.ownRWMutexWLocked (mvcc.revMuAddr s) (mvcc.revMuInv s γ) ∗
          dghostVar γ.rst (DFrac.own (1 : Qp).half) true ∗ dghostVar γ.rst (DFrac.own (1 : Qp).half) true ∗
          (∃ v : w64, (s.[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half} v : IProp GF)) ∗ £ 1 ∗ £ 1)
        isplitl []
        · iintro %Ψ H HΨ
          iunfold mvcc.restoreOnP0 at H
          icases H with ⟨Hr, Hl1, Hl2, Hl3, HcK⟩
          iapply wp_fupd
          wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$HrevMu] as ⟨Hwl2, HR2⟩
          imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.revMuInv s γ 1)) $$ Hl1 HR2 with HR2
          iunfold mvcc.revMuInv at HR2
          icases HR2 with ⟨%m, Hr2, HR2⟩
          ihave %Hm := dghostVar_agree γ.rst _ _ _ _ $$ Hr Hr2
          subst Hm
          simp only [↓reduceIte]
          iunfold mvcc.revMuRest at HR2
          icases HR2 with ⟨%v, %c', Hcur2, Hcm2⟩
          icombine Hcm2 HcK gives %Hcv
          obtain ⟨-, rfl⟩ := Hcv
          ihave Hcm := ((typedPointsto_dfractional (GF := GF) _ _).dfractional (DFrac.own (1 : Qp).half)
            (DFrac.own (1 : Qp).half.half)).2 $$ [Hcm2 HcK]
          · iframe Hcm2 HcK
          imodintro
          iapply HΨ $$ %_ Hcm [Hwl2 Hr Hr2 Hcur2 Hl2 Hl3]
          iframe Hwl2 Hr Hr2 Hl2 Hl3
          iexists v; iexact Hcur2
        · iintro %Ψ Hcm ⟨Hwl2, Hr, Hr2, ⟨%v, Hcur2⟩, Hl2, Hl3⟩ HΨ
          icases ((typedPointsto_dfractional (GF := GF) _ _).dfractional _ _).1 $$ Hcm
            with ⟨Hcm2, HcK⟩
          wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl2 Hr2 Hcur2 Hcm2]
          · inext
            iunfold mvcc.revMuInv
            iexists true
            simp only [↓reduceIte]
            iframe Hr2
            iunfold mvcc.revMuRest
            iexists _, _
            iframe Hcur2 Hcm2
          iapply HΨ
          iunfold mvcc.restoreOnP
          iframe Hr Hl2 Hl3 HcK
    -- the second round's lock: the restoring mode, `compactMainRev`'s halves agreeing
    ihave HLk : mvcc.revLockW (GF := GF) s (1 : Qp).half (mvcc.restoreOnP s γ (r.fin.getD (W64 (-1))))
        (mvcc.restoreOnK s γ (r.fin.getD (W64 (-1)))) $$ []
    · iunfold mvcc.revLockW
      iintro %Ψ H HΨ
      iunfold mvcc.restoreOnP at H
      icases H with ⟨Hr, Hl3, Hl4, HcmK⟩
      iapply wp_fupd
      wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$HrevMu] as ⟨Hwl2, HR2⟩
      imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.revMuInv s γ 1)) $$ Hl3 HR2 with HR2
      iunfold mvcc.revMuInv at HR2
      icases HR2 with ⟨%m, Hr2, HR2⟩
      ihave %Hm := dghostVar_agree γ.rst _ _ _ _ $$ Hr Hr2
      subst Hm
      simp only [↓reduceIte]
      iunfold mvcc.revMuRest at HR2
      icases HR2 with ⟨%v, %c', Hcur2, Hcm2⟩
      icombine Hcm2 HcmK gives %Hcv
      obtain ⟨-, rfl⟩ := Hcv
      imodintro
      iapply HΨ $$ %v Hcur2 [Hwl2 Hr Hr2 Hcm2 HcmK Hl4]
      iunfold mvcc.restoreOnK
      iframe Hwl2 Hr Hr2 Hcm2 HcmK Hl4
    -- the second round's unlock: the switch to the new objects and names, at the restored revision
    -- with the finished record's lag (`restore_switch`)
    ihave HUl : mvcc.revUnlockW (GF := GF) s (1 : Qp).half ([[], []] ++ R)
        (mvcc.restoreOnK s γ (r.fin.getD (W64 (-1))))
        iprop(mvcc.bucketViewC (γ.withPhys p') (1 : Qp).half (mvcc.bucketOfEnts ents) ∗
          mvcc.isTreeIndex ti (γ.withPhys p').idx ∗
          ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
            mvcc.idxReader ti (γ.withPhys p').idx) ∗
          ⧖ (mvcc.logCh ([[], []] ++ R)))
        (mvcc.restoreOnQ s γ p' ⟨b', ti, sc, stopc⟩ R r ti)
        $$ [Hcur Hfrag HcurR HcurW Htkr Hheld Hrts Hlc4 HwsdS HwsdL HXn]
    · iunfold mvcc.revUnlockW
      iintro %Ψ Hcur2 HK HV HΨ
      iunfold mvcc.restoreOnK at HK
      icases HK with ⟨Hwl2, Hr, Hr2, Hcm2, HcmK, Hl5⟩
      icases HV with ⟨Hv, #Hti', Hrd, #Hrc'⟩
      ihave Hrd := mvcc.rep_nReaders _ $$ Hrd
      ihave Hcm2 : (s.[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half} (W64 r.finRev : w64) :
          IProp GF) $$ [Hcm2]
      · rw [hx]; iexact Hcm2
      ihave Hlg : mvcc.lagTok (GF := GF) γ r.crev r.finRev ∗
          (if r.finRev = r.crev then ghostVar γ.wsd (1 : Qp).half.half () else iprop(True)) $$ [HwsdL]
      · iunfold mvcc.lagTok
        by_cases hfc : r.finRev = r.crev
        · simp only [hfc, ↓reduceIte]; iframe HwsdL
        · simp only [hfc, ↓reduceIte]; iframe HwsdL
      icases Hlg with ⟨Hlag, Hlr⟩
      imod (mvcc.restore_switch s γ ⟨b, ti0, GoInterface.ok fi, sstop⟩ ⟨b', ti, sc, stopc⟩ p' R r.crev
          r.finRev (1 : Qp).half 3 hR hfb hcl (by decide)) $$
          Hl5 Hlc4 Hwi HwsdS Hpool Hcur Hfrag HcurR HcurW Htkr Hr Hr2 Hheld Hcur2 Hcm2 Hlag HpC Hnlb Hok'
          [Hv] Hrd Hrc' [] Hrts HXn
        with ⟨HR, Hrst', Hn1, Hfrag', Hn3, Htkr, Hwsd, Hw, Hrv', HlogQ, Hold, #HcertL⟩
      · iintro #Hc
        iapply mvcc.bucketViewL_ofCutW γ p' (1 : Qp).half ([[], []] ++ R) hlb r.crev ents hcut hcge
        iframe Hc Hclb2
        isplitl [Hv]
        · iapply mvcc.bucketViewC_bucketView $$ Hv
        ipureintro; exact hon'
      · ipureintro; exact Hrb
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl2 HR]
      · inext; iexact HR
      iapply HΨ
      ihave Hrest : mvcc.restoreOnRest (GF := GF) γ R $$ [HlogQ Hold]
      · iunfold mvcc.restoreOnRest; iframe HlogQ Hold
      iunfold mvcc.restoreOnQ
      iframe Hrst' Hn1 Hfrag' Hn3 Htkr Hwsd Hw Hrest Hrv' Hlr HcmK Hti' HcertL
    -- the store at the new names once `restore()` is done: the writer's state at `L'` and its
    -- registration, the new backend's contract, the fields, the new compaction right, `s.mu`'s
    -- resource with the lag
    ihave Hprep : mvcc.restoreDone s b' ti (1 : Qp).half (DFrac.own 1) (DFrac.own 1)
        (DFrac.own (1 : Qp).half.half) ([[], []] ++ R) ents r
        iprop(mvcc.storeRT (γ.withPhys p') ∗ mvcc.restoreRegM d')
        (mvcc.kbRecs (γ.withPhys p').kb (γ.withPhys p').bucket r)
        (mvcc.restoreOnQ s γ p' ⟨b', ti, sc, stopc⟩ R r ti) -∗
        |={⊤}=> mvcc.restoreOnReady s γ p' ⟨b', ti, sc, stopc⟩ R r
        $$ [HbkT Hlc5 Hwk' Hwv' HviewW HviewP Hcres Hrr Hmwr Hfsch Hfstop Hstop HsStop Hq0 Hcu Hcmp' Hsr HjRT
          HfzK HwcM
          HcrevM Hjc1' HYa HYp HrcvY HwcY]
    · iintro HD
      iunfold mvcc.restoreDone at HD
      icases HD with ⟨⟨HrtA, Hreg⟩, Hnc, -, HQ, Hcr, HcmD, Hfb, Hfidx⟩
      iunfold mvcc.restoreOnQ at HQ
      icases HQ with ⟨Hrst', Hn1, Hfrag', Hn3, Htkr, Hwsd, Hw, Hrest, HtoksN, Hlr, HcmK, #Hti',
        #HcertL⟩
      ihave HviewWL := mvcc.bucketViewL_ofCutW γ p' _ _ hlb r.crev ents hcut hcge $$ [HviewW]
      · iframe HviewW Hclb2 HcertL
        ipureintro; exact hon'
      -- (2026-11-06) the writer's pin, its view's quarter thin at the restored revision (the loan:
      -- nothing, the store compacts), and the revision tokens, into the writer's state
      ihave HviewPL := mvcc.bucketViewL_ofCutW γ p' _ _ hlb r.crev ents hcut hcge $$ [HviewP]
      · iframe HviewP Hclb2 HcertL
        ipureintro; exact hon'
      ihave Hloan : mvcc.writerLoan (GF := GF) (γ.withPhys p') $$ []
      · iunfold mvcc.writerLoan; simp only [hon', ↓reduceIte]; itrivial
      ihave HY : mvcc.slotY (GF := GF) (γ.withPhys p') ([[], []] ++ R) $$ [HYa HYp HrcvY HwcY]
      · iunfold mvcc.slotY
        iexists r.crev
        simp only [mvcc.StoreNames.withPhys_api]
        iframe HYa HwcY
        isplitl [HYp]
        · rw [show mvcc.pndW (γ.withPhys p') = mvcc.pndW γ from rfl]; iexact HYp
        unfold mvcc.rcvW
        simp only [mvcc.StoreNames.withPhys_kb, hk, hd'on, ↓reduceIte, mvcc.StoreNames.withPhys_rcv, hrcv]
        iexact HrcvY
      imod (mvcc.restore_finish s γ ⟨b', ti, sc, stopc⟩ p' ([[], []] ++ R) hR.2 (by simp)
          (mvcc.restoreLog_ch R hR.1)) $$
          Hlc5 Hwi Hn3 Hw Hcr Hrc Hnlb Hwk' Hwv' HviewWL Hcres Hrr HfzK HtoksN Hloan HviewPL HY
        with ⟨Hwr, -, #Hreg', Hfr⟩
      -- the new backend's contract, its registration fixed
      imod mvcc.restoreRegM_fix d' (γ.withPhys p') $$ Hreg with #Hfix
      ihave HbkR := HbkT $$ %p' %hpb Hfix
      iunfold mvcc.storeBackendTR at HbkR
      ihave #HbkN := mvcc.isKeyBackendGR_ncFalse _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ $$ HbkR
      -- the write right's invariant, with the records' write right, and the registration
      imod mvcc.physCmp_alloc s (γ.withPhys p') $$ [Hmwr Hnc] with #HmwN
      · iframe Hmwr Hreg'
        simp only [hon', ↓reduceIte]
        iapply mvcc.kbRecs_MWf $$ Hnc
      ihave #Hph2 : mvcc.physOk (GF := GF) s (γ.withPhys p') ⟨b', ti, sc, stopc⟩ $$ []
      · iunfold mvcc.physOk
        iexists P', iprop(True)
        simp only [named]
        isplitl []
        · iunfold mvcc.hookP; simp only [mvcc.StoreNames.withPhys_hook]; iexact Hh'
        isplitl []
        · iexact HbkN
        isplitl []
        · imodintro; itrivial
        isplitl []
        · iexact Hti'
        isplitl []
        · simp only [mvcc.StoreNames.withPhys_sch]; iexact HisFifo
        isplitl []
        · iexact HmwN
        isplitl []
        · iunfold mvcc.stopPayAt
          simp only [mvcc.StoreNames.withPhys_sx, mvcc.StoreNames.withPhys_sch, hsx, hs]
          iframe Hx' Hpi
        ipureintro
        simp only [mvcc.StoreNames.withPhys_kb, mvcc.StoreNames.withPhys_cm, hk]
        exact ⟨fun _ => Hcmt.1 hon, fun _ => hd'on⟩
      -- the fields at the new objects: `s.mu`'s half, the caller's quarter, the closer's and the jobs'
      -- eighths
      ihave Hfs : mvcc.fieldShareAt (GF := GF) s (γ.withPhys p') ((1 : Qp).half + (1 : Qp).half)
          ⟨b', ti, sc, stopc⟩ $$ [Hn1 Hrst' Hfb Hfidx Hfsch Hfstop]
      · rw [Qp.half_add_half]
        iunfold mvcc.fieldShareAt
        simp only [named, mvcc.StoreNames.withPhys_rst]
        iframe Hn1 Hrst' Hph2
        iunfold mvcc.storeFields
        simp only [named]
        iframe Hfb Hfidx Hfsch Hfstop
      icases (mvcc.fieldShareAt_split s _ _ _ _).1 $$ Hfs with ⟨HfsM, Hfs⟩
      have h4 := (mvcc.fieldShareAt_split (GF := GF) s (γ.withPhys p') (1 : Qp).half.half
        (1 : Qp).half.half ⟨b', ti, sc, stopc⟩).1
      rw [Qp.half_add_half] at h4
      icases h4 $$ Hfs with ⟨HfsW, Hfs⟩
      have h8 := (mvcc.fieldShareAt_split (GF := GF) s (γ.withPhys p') mvcc.q8 mvcc.q8
        ⟨b', ti, sc, stopc⟩).1
      rw [mvcc.q8_add] at h8
      icases h8 $$ Hfs with ⟨HfsC, HfsJ⟩
      ihave #HscN : mvcc.isStopChan (GF := GF) stopc $$ []
      · iunfold mvcc.isStopChan; iexists γstop; iexact Hstop0
      imod mvcc.storeStopR_alloc s (γ.withPhys p') ⟨b', ti, sc, stopc⟩ ⊤ $$ HfsJ HscN with #HsRN
      -- the new compaction right at the restored revision: the new queue holds the token
      ihave Hright : mvcc.compactRightR (GF := GF) s (γ.withPhys p') r.crev
          $$ [Hcu Hq0 Hcmp' Hsr HjRT HfsC Hstop HsStop Hjc1']
      · iapply (mvcc.compactRightR_iff _ _ _).2
        isplitl [Hcu]
        · rw [mvcc.crevUB_withPhys]; iexact Hcu
        isplitl [Hq0 Hcmp' Hsr HjRT Hjc1']
        · iunfold mvcc.compactQueue
          iexists [n₀], p₀, iprop(True), mvcc.compactTok (γ.withPhys p') r.crev
          rw [List.singleton_append]
          simp only [mvcc.StoreNames.withPhys_sch]
          iframe Hq0 Hp0
          isplitl [Hcmp' Hsr HjRT Hjc1']
          · iunfold mvcc.compactTok
            isplitl [Hcmp']
            · iexists r.crev; iframe Hcmp'; ipureintro; exact Int.le_refl _
            isplitl [Hsr HjRT]
            · iapply (mvcc.compactJobResM_on _ hon').2
              simp only [mvcc.StoreNames.withPhys_kb, hk]
              iframe HjRT Hsr
            iexists (r.finRev, (⟨W64 0, W64 0⟩ : mvcc.Rev))
            isplitl [Hjc1']
            · iapply mvcc.jobCur_intro
              rw [mvcc.StoreNames.withPhys_jc, hjc]; iexact Hjc1'
            ipureintro
            show r.finRev ≤ r.crev
            exact hfb.2
          iintro ⟨-, H⟩
          iexact H
        iexists ⟨b', ti, sc, stopc⟩
        iframe HfsC HscN HsRN
        isplitl [Hstop]
        · iunfold mvcc.stopCloser; iexists γstop; iexact Hstop
        simp only [mvcc.StoreNames.withPhys_sch]; iexact HsStop
      -- `s.mu`'s resource with the lag: `compactMainRev` at the finished record
      ihave Hmu' : mvcc.muInvLag (GF := GF) s (γ.withPhys p') r.crev r.finRev
          $$ [HcmD HcmK HcrevM HwcM]
      · iunfold mvcc.muInvLag
        simp only [named]
        isplitl [HcmD HcmK]
        · rw [hx]; iapply (mvcc.typedPointsto_halves _ _ _).2; iframe HcmD HcmK
        isplitl [HcrevM]
        · rw [mvcc.crevUB_withPhys]; iexact HcrevM
        isplitl [HwcM]
        · rw [mvcc.StoreNames.withPhys_api]; iexact HwcM
        isplitl []
        · rw [mvcc.crevSafe_withPhys]
          iunfold mvcc.crevSafe
          iexists ([[], []] ++ R)
          iframe HcertL
          ipureintro; exact hcl
        isplitl []
        · rw [mvcc.crevPermAt_withPhys]; iexact HpC
        ipureintro; exact hfb
      imodintro
      iunfold mvcc.restoreOnReady
      iframe Hmu' Hright HrtA Hfrag' Hwr HfsM HfsW Htkr Hwsd Hrest Hlr HcertL Hfr Hreg'
    -- the resume: `compactLockfree` at the scheduled record ends the lag; else there is none
    ihave HK : mvcc.resumeK s r (mvcc.restoreDone s b' ti (1 : Qp).half (DFrac.own 1) (DFrac.own 1)
        (DFrac.own (1 : Qp).half.half) ([[], []] ++ R) ents r
        iprop(mvcc.storeRT (γ.withPhys p') ∗ mvcc.restoreRegM d')
        (mvcc.kbRecs (γ.withPhys p').kb (γ.withPhys p').bucket r)
        (mvcc.restoreOnQ s γ p' ⟨b', ti, sc, stopc⟩ R r ti))
        (mvcc.restoreOnFin s γ p' ⟨b', ti, sc, stopc⟩ d' R r hkH dqh PostH YH) $$ [Hprep HrH]
    · iunfold mvcc.resumeK
      cases hres : r.resumes
      · simp only [Bool.false_eq_true, ↓reduceIte]
        iintro HD
        have hcf := mvcc.CmpRecs.crev_noResume r hres
        iunfold mvcc.restoreOnFin
        imod Hprep $$ HD with HY
        iunfold mvcc.restoreOnReady at HY
        icases HY with ⟨Hmu', Hright, HrtA, Hfrag', Hwr, HfsM, HfsW, Htkr, Hwsd, Hrest, Hlr,
          #HcertL, Hfr, #Hreg'⟩
        ihave Hmu : mvcc.muInvAt (GF := GF) s (γ.withPhys p') 1 r.crev $$ [Hmu']
        · iapply (mvcc.muInvLag_at _ _ _).1
          rw [hcf]; iexact Hmu'
        ihave HwsdL : ghostVar (GF := GF) γ.wsd (1 : Qp).half.half () $$ [Hlr]
        · iapply mvcc.lagTok_rest γ r.crev r.finRev
          iframe Hlr
          iunfold mvcc.lagTok
          simp only [hcf, ↓reduceIte]
          itrivial
        imodintro
        rw [mvcc.resumeBackM_no d' r hkH dqh PostH YH hres]
        iframe Hmu Hwr HfsM Hright HfsW HrtA Hfrag' HwsdL Htkr Hwsd Hrest HcertL Hfr Hreg'
      · simp only [↓reduceIte]
        iintro %Ψ HD HΨ
        obtain ⟨hlt, hcs⟩ := mvcc.CmpRecs.resumes_lt r hres
        have hsr : sint.Z (r.sched.getD (W64 0)) = r.crev := by rw [mvcc.CmpRecs.schedRev_getD, hcs]
        imod Hprep $$ HD with HY
        iunfold mvcc.restoreOnReady at HY
        icases HY with ⟨Hmu', Hright, HrtA, Hfrag', Hwr, HfsM, HfsW, Htkr, Hwsd, Hrest, Hlr,
          #HcertL, Hfr, #Hreg'⟩
        ihave HrH := mvcc.resumeCtxM_lock (γ.withPhys p') d' r P' hkH PreH QH PostH dqh XH YH
          (by simp only [mvcc.StoreNames.withPhys_kb, hk]) hres $$ [HrH]
        · iframe HrH
          iunfold mvcc.hookP; simp only [mvcc.StoreNames.withPhys_hook]; iexact Hh'
        icases HrH with ⟨Hctx, HXH, #HreqH⟩
        -- the resumed revision is past `0` (the records' `recsPos`)
        have h1r : 1 ≤ sint.Z (r.sched.getD (W64 0)) := by
          have hres' := hres
          unfold mvcc.CmpRecs.resumes at hres'
          simp only [decide_eq_true_eq] at hres'
          cases hsch : r.sched with
          | none => simp [mvcc.CmpRecs.schedRev, hsch] at hres'
          | some x => simp only [Option.getD_some]; exact hpos.2 x hsch
        have hlt' : r.finRev < sint.Z (r.sched.getD (W64 0)) := by rw [hsr]; exact hlt
        wp_apply (hCLF s (γ.withPhys p') (r.sched.getD (W64 0)) r.finRev P' hkH PreH QH PostH dqh XH YH
            (by exact hon') hlt' h1r)
          $$ [Hmu' Hright HrtA Hctx Hwr Hfr HXH]
          as %ch %err ⟨HrtA, Hback, Hwr, Hfr, %Herr, Hmu, Hright, -, HPostH, -, Hlag, HYH⟩
        · rw [mvcc.isStore_withPhys, mvcc.crevPermAt_withPhys, hsr, mvcc.StoreNames.withPhys_wr,
            show mvcc.slotFr (GF := GF) (γ.withPhys p') = mvcc.slotFr γ from rfl]
          iframe Hmu' Hright HrtA Hs HpC Hwr Hfr Hctx HXH HreqH
          simp only [mvcc.StoreNames.withPhys_kb, hk]
          iframe Hwts
          repeat' (first | isplitl [] | (ipureintro; exact hcl) | itrivial)
        rw [show mvcc.slotFr (GF := GF) (γ.withPhys p') = mvcc.slotFr γ from rfl]
        ihave HrB := mvcc.resumeBackM_of (γ.withPhys p') d' r P' hkH dqh PostH YH
          (by simp only [mvcc.StoreNames.withPhys_kb, hk]) hres $$ [Hback HPostH HYH]
        · iframe Hback HPostH HYH
        ihave Hmu : mvcc.muInvAt (GF := GF) s (γ.withPhys p') 1 r.crev $$ [Hmu]
        · rw [← hsr]; iexact Hmu
        ihave Hright : mvcc.compactRightR (GF := GF) s (γ.withPhys p') r.crev $$ [Hright]
        · rw [← hsr]; iexact Hright
        rw [mvcc.lagTok_withPhys]
        ihave Hlag : mvcc.lagTok (GF := GF) γ r.crev r.finRev $$ [Hlag]
        · rw [← hsr]; iexact Hlag
        ihave HwsdL := mvcc.lagTok_rest γ r.crev r.finRev $$ [Hlag Hlr]
        · iframe Hlag Hlr
        iapply HΨ
        iunfold mvcc.restoreOnFin
        imodintro
        iframe Hmu Hwr HfsM Hright HfsW HrtA Hfrag' HwsdL Htkr Hwsd Hrest HcertL Hfr Hreg'
        iexact HrB
    -- `s.restore()`
    wp_apply +noauto hR' $$ [$Hfb $Hfidx $Hix $Hig $Hcr $HcmR Hrt1 Hreg Hnc HviewR Hrst Hlc1 Hlc2 Hlc3
        HcmK HFw HLk HUl HK HLo] as ⟨HFin, HLo⟩
    · iframe #
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe Hrt1 Hreg Hnc HFw HLk HUl HK HLo
      isplitl [HviewR]
      · iunfold mvcc.restoreViewR
        simp only [Bool.false_eq_true, ↓reduceIte]
        iframe HviewR HcrT'
      iunfold mvcc.restoreOnP0
      iframe Hrst Hlc1 Hlc2 Hlc3 HcmK
      isplitr
      · ipureintro; exact Hlgnn
      isplitr
      · iexact Hlessor
      ipureintro; exact Hlok
    iunfold mvcc.restoreOnFin at HFin
    imod HFin with ⟨Hmu, Hwr, HfsM, Hright, HfsW, HrtA, Hfrag', HrH, HwsdL, Htkr, Hwsd, Hrest,
      #HcertL, Hfr, #Hreg'⟩
    iunfold mvcc.restoreOnRest at Hrest
    icases Hrest with ⟨HlogQ, Hold⟩
    (try wp_auto)
    -- `defer s.mu.Unlock()`: `s.mu`'s resource at the new objects and the restored revision
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hmu Hwr HfsM]
    · inext
      iunfold mvcc.muInv
      iexists r.crev
      iframe Hwr
      isplitl [Hmu]
      · rw [← mvcc.muInvAt_withPhys s γ p']; iexact Hmu
      iunfold mvcc.fieldShare
      iexists p', ⟨b', ti, sc, stopc⟩
      iexact HfsM
    (try wp_auto)
    iapply HΦ
    iexists p'
    isplitl []
    · ipureintro; exact ⟨hb, hk⟩
    isplitl [Hright]
    · iapply (mvcc.storeCloserM_on _ _ _ hon').2; iexact Hright
    isplitl [HfsW]
    · iunfold mvcc.fieldShare; iexists p', ⟨b', ti, sc, stopc⟩; iexact HfsW
    isplitl [Hwsd HwsdL HwsdK]
    · iunfold mvcc.wsDep
      iapply hw.2
      iframe Hwsd
      iapply hw2.2
      iframe HwsdL HwsdK
    isplitl [Hfrag']
    · iexact Hfrag'
    isplitl [HrtA Htkr]
    · iapply (mvcc.writerOwn_on (γ.withPhys p') (by
        simp only [mvcc.StoreNames.withPhys_kb, hk, mvcc.nJobRd, hd'on, ↓reduceIte])).2
      unfold mvcc.retiredAt; simp only [mvcc.StoreNames.withPhys_tkr]
      iframe HrtA Htkr
    isplitl []
    · iunfold mvcc.hookP; simp only [mvcc.StoreNames.withPhys_hook]; iexact Hh'
    isplitl []
    · iexact Hreg'
    isplitl []
    · iexact HcertL
    isplitl [HlogQ]
    · iexact HlogQ
    isplitl [HrH]
    · iexact HrH
    isplitl [Hjob]
    · iexact Hjob
    isplitl [HrtOld Hold]
    · rw [hj1]; iapply mvcc.rep_back3; iframe HrtOld Hold
    iunfold mvcc.slotFr at Hfr
    iframe Hnew HLo Hfr HnlLb HRr
    ipureintro; exact hLR
  -- off: neither backend compacts; `store.restore` at no record and the whole bucket, over the
  -- clean read
  have hRestore := mvcc.store.restore.specNCc_of_spec hRestore
  rw [mvcc.nJobRd_off _ hon, Nat.sub_zero, mvcc.compactJobResM_off _ hon]
  wp_start as ⟨-, -, -, #Hs, %Hkbm, Hright, Hfs, Hwsd, Hfrag, Hown, #HcL, HlogQ, #Hok',
    HbkT, #HcrT, Himg, #HndO, Hrr, Hreg, -, -, Hres, Hrts, HLo, %Hlok, Hfr, Hcb⟩
  obtain ⟨d0, hd0, hcm0⟩ := Hkbm
  have hd0off : d0.cm = false := by
    rw [hd0] at hon; simp only [mvcc.kbCmpM] at hon; simpa using hon
  have Hcm' : d'.cm = false := by rw [hcm0]; exact hd0off
  have Hkb : ∃ d, γ.kb = some d ∧ d.cm = false := ⟨d0, hd0, hd0off⟩
  icases (mvcc.restoreRightM_off s γ c hon).1 $$ Hright with ⟨Hcl, #Hfrz, %hc⟩
  icases (mvcc.restoreImageM_off d' γb' _ r Hcm').1 $$ Himg with ⟨Hview, Hnc, %hr⟩
  subst hc hr
  ihave #Hnd : mvcc.kbNoDel (GF := GF) (some d') $$ [HndO]
  · rw [mvcc.kbNoDelOff_off _ (by simp [mvcc.kbCmpM, Hcm'])]; iexact HndO
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule $$ []
  · iPkgInit
  ihave #Hs' := Hs
  iunfold mvcc.isStore at Hs'
  iNamed Hs'
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  -- `s.mu.Lock()`: all of `s.mu`'s resource
  wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hwl, HP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.muInv s γ 1)) $$ Hlc1 HP with HP
  iunfold mvcc.muInv at HP
  icases HP with ⟨%c, Hma, Hwr, Hfs2⟩
  iunfold mvcc.muInvAt at Hma
  iNamed Hma
  -- the store is never compacted: `-1`
  imod mvcc.crevFrozen_agree γ _ c HcM $$ Hfrz HcrevM with ⟨HcrevM, %Hc⟩
  subst Hc
  -- the fields, whole: `s.mu`'s half, the closer's quarter, the caller's quarter
  iunfold mvcc.storeCloser at Hcl
  icases Hcl with ⟨%o, Hfs3, #Hstc, Hstcl, Htok, Hq⟩
  ihave Hfs := mvcc.fieldShare_gather s γ o $$ [Hfs2 Hfs Hfs3]
  · iframe Hfs2 Hfs Hfs3
  iunfold mvcc.fieldShareAt at Hfs
  iNamed Hfs
  ihave #Hph' := Hph
  iunfold mvcc.physOk at Hph'
  iNamed Hph'
  iunfold mvcc.storeFields at Hflds
  iNamed Hflds
  obtain ⟨b, ti0, ssched, sstop⟩ := o
  try simp only
  (try wp_auto)
  -- `close(s.stopc)`
  iunfold mvcc.stopCloser at Hstcl
  icases Hstcl with ⟨%γc, Hstcl⟩
  wp_apply wp_broadcast_chan_close _ γc iprop(True) $$ [$Hstcl] as #Hdone
  · imodintro; itrivial
  -- (M2, the storage side, item 34) the scheduler's payload: its stop channel closed
  ihave #Hsp := mvcc.stopPay_of_done γ.sx γ.sch ⟨b, ti0, ssched, sstop⟩ γc $$ [$Hpay $Hdone]
  (try wp_auto)
  -- `s.fifoSched.Stop()`
  ihave #Hfifo' := HisSched
  iunfold schedule.isFifo at Hfifo'
  icases Hfifo' with ⟨%Hnn, -⟩
  cases ssched with
  | nil => exact absurd rfl Hnn
  | ok fi =>
  iunfold mvcc.compactQueue at Hq
  icases Hq with ⟨%Ps, %p, %Q, %R', Hq, -, -, -⟩
  (try wp_auto)
  wp_apply hStop fi γ.sch (Ps ++ [p]) $$ [Htok Hq] as -
  · iframe; iframe #
  (try wp_auto)
  -- `s.kvindex = newTreeIndex(s.lg)`: fresh event-count and compactor names over the store's
  -- history, committed log and compaction revision (the restore plan's R5d)
  imod mvcc.idx_renew γ.idx (mvcc.evsOf (([[], []] ++ R) ++ [[]])).length
    with ⟨%nv, %cm, Hnauth, #Hnlb, Hcm⟩
  imod mvcc.crevLb_neg (⟨γ.idx.hist, nv, γ.idx.log, γ.idx.crev, cm⟩ : mvcc.IdxNames) with #Hclb
  ihave #HcL' := HcL
  iunfold mvcc.idxCert at HcL'
  icases HcL' with ⟨-, -, #Hllb0, -⟩
  wp_apply (hNewIdx ⟨γ.idx.hist, nv, γ.idx.log, γ.idx.crev, cm⟩ lg _ L) $$ [Hnauth Hcm]
    as %ti ⟨Hix, Hig, Hcmp0⟩
  · iframe Hnauth Hcm; iframe #; ipureintro; exact Hlgnn
  (try wp_auto)
  -- `s.revMu.Lock()`; `currentRev = 1`; `compactMainRev = -1`; `s.revMu.Unlock()`: the takeover
  -- (`restore_takeover`), the lock released in restoring mode
  wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$HrevMu] as ⟨HwlR, HR⟩
  wp_auto_lc 2
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.revMuInv s γ 1)) $$ Hlc1 HR with HR
  ihave Hfr : mvcc.slotFr (GF := GF) γ $$ [Hfr]
  · iunfold mvcc.slotFr; iexact Hfr
  -- (with the client's step, `restoreCb`: `s.revMu`'s slot and the writer's view at the restored log)
  rw [mvcc.CmpRecs.crev_empty]
  imod (mvcc.restore_takeover s γ ⟨b, ti0, GoInterface.ok fi, sstop⟩ L ([[], []] ++ R) (-1) (-1) Rr
      (by decide) hwq) $$
      Hlc2 Hwi HR Hfrst Hcur Hwr HcL HlogQ HcrevM HcmpM Hfr Hcb
    with ⟨⟨%v0, Hcr⟩, Hcm, Hrst, Hcur, HcurR, HcurW, HcrevM, Hheld, #Hhlb, HfzK, ⟨%cw, Hwc⟩, %hLR,
      HXn, HYa, HYp, #HnlLb, HRr⟩
  -- (track A, request 2) the writer's compaction revision's ghost, `s.mu`'s half and the old
  -- writer's, at the fresh store's `-1`
  imod mvcc.api.wcrPart_update γ.api _ _ (Qp.half_add_half 1) (-1) cw (-1) $$ [HwcM Hwc]
    with ⟨HwcM, HwcY⟩
  · iframe HwcM Hwc
  (try wp_auto)
  imod dghostVar_update true γ.rst false $$ Hrst with Hrst
  have hrst := (dghostVar_fractional (GF := GF) γ.rst true).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hrst
  icases hrst.1 $$ Hrst with ⟨HrstL, Hrst⟩
  icases (mvcc.typedPointsto_parts _ _ (1 : Qp).half (1 : Qp).half (Qp.half_add_half 1)).1
    $$ Hcr with ⟨HcrL, Hcr⟩
  icases (mvcc.typedPointsto_parts _ _ (1 : Qp).half (1 : Qp).half (Qp.half_add_half 1)).1
    $$ Hcm with ⟨HcmL, Hcm⟩
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$HwlR HrstL HcrL HcmL]
  · inext
    iunfold mvcc.revMuInv
    iexists true
    simp only [↓reduceIte]
    iframe HrstL
    iunfold mvcc.revMuRest
    iexists _, _
    iframe HcrL HcmL
  (try wp_auto)
  -- `s.fifoSched = schedule.NewFIFOScheduler(s.lg)`; `s.stopc = make(chan struct{})`
  -- (M2, the storage side, item 34) the new scheduler's payload's name, fresh
  imod (dghostVar_alloc (GF := GF) (null : Loc)) with ⟨%γx', Hx'⟩
  wp_apply hFifo _ (mvcc.stopPay γx') $$ [] as %sc ⟨%γs, %n₀, %p₀, #HisFifo, HsStop, Hq0, #Hp0, #Hpi⟩
  · ipureintro; exact Hlgnn
  (try wp_auto)
  wp_apply +noauto chan.wp_make1 (V := Unit) as %stopc %γstop ⟨#Hstc', %Hstcap, Hstown⟩
  imod dghostVar_update stopc γx' _ $$ Hx' with Hx'
  imod dghostVar_persist γx' 1 stopc $$ Hx' with #Hx'
  wp_auto_lc 3
  imod alloc_broadcast_chan (E := ⊤) iprop(True) γstop stopc $$ Hstc' Hstown with Hstop
  ihave #Hstop0 := ownBroadcastChan_Unknown _ _ _ _ $$ Hstop
  -- the new backend's names, fresh: the batch lock's invariant `P'`, its key and view log, the
  -- compaction's record
  imod (saved_prop_alloc (GF := GF) P' DFrac.discard DFrac.valid_discard) with ⟨%γh', #Hh'⟩
  imod ghostVar_alloc (GF := GF) () with ⟨%γwk', Hwk'⟩
  imod ghostVar_alloc (GF := GF) ([[], []] ++ R) with ⟨%γwv', Hwv'⟩
  imod ghostVar_alloc (GF := GF) ((none, none) : Option w64 × Option w64) with ⟨%γm', Hmeta'⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γfin', Hfin', -⟩
  imod ghostVar_alloc (GF := GF) (-1 : Int) with ⟨%γrcv', Hrcv'⟩
  icases ghostVar_halves γrcv' _ $$ Hrcv' with ⟨Hrcv', -⟩
  obtain ⟨p', hnv, hcm, hb, hh, hk, hm, hfin, hs, hwk, hwv, hsx, hrcv⟩ : ∃ p' : mvcc.PhysNames,
      p'.nev = nv ∧ p'.cmp = cm ∧ p'.bucket = γb' ∧ p'.hook = γh' ∧ p'.kb = some d' ∧
      p'.cmeta = γm' ∧ p'.fin = γfin' ∧ p'.sch = γs ∧ p'.wk = γwk' ∧ p'.wv = γwv' ∧ p'.sx = γx' ∧
      p'.rcv = γrcv' :=
    ⟨⟨nv, cm, γb', γh', γ.hookFn, some d', γm', γfin', γs, γwk', γwv', γ.mwk, γx', γrcv', γ.jc,
        γ.rcl⟩,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hpb : p'.bucket = γb' ∧ p'.kb = some d' := ⟨hb, hk⟩
  rw [← hnv, ← hcm, ← hh, ← hm, ← hfin, ← hs, ← hwk, ← hwv]
  rw [show (⟨γ.idx.hist, p'.nev, γ.idx.log, γ.idx.crev, p'.cmp⟩ : mvcc.IdxNames) =
    (γ.withPhys p').idx from rfl]
  -- the new backend's view: half for `restore`, half for its batch lock's resource
  icases mvcc.kbViewC_halves _ _ _ $$ Hview with ⟨HviewR, HviewW⟩
  ihave HviewR : mvcc.bucketViewC (GF := GF) (γ.withPhys p') (1 : Qp).half
      (mvcc.bucketMap ([[], []] ++ R)) $$ [HviewR]
  · iunfold mvcc.bucketViewC
    simp only [mvcc.StoreNames.withPhys_kb, mvcc.StoreNames.withPhys_bucket, hk, hb]
    iexact HviewR
  ihave HviewW : mvcc.bucketView (GF := GF) (γ.withPhys p') (1 : Qp).half
      (mvcc.bucketMap ([[], []] ++ R)) $$ [HviewW]
  · iapply mvcc.bucketViewC_bucketView
    iunfold mvcc.bucketViewC
    simp only [mvcc.StoreNames.withPhys_kb, mvcc.StoreNames.withPhys_bucket, hk, hb]
    iexact HviewW
  -- the writer's half of it: `writerRes`'s quarter and the new pin's (M2's item 37)
  icases (mvcc.bucketView_quarters _ _).1 $$ HviewW with ⟨HviewW, HviewP⟩
  -- (the snapshot image's (a)) `writerRes`'s eighth and the compaction's part's
  icases (mvcc.bucketView_halves _ (1 : Qp).half.half _).1 $$ HviewW with ⟨HviewW, HviewC⟩
  ihave HviewW := mvcc.bucketViewL_exact _ _ _ $$ HviewW
  ihave HviewP := mvcc.bucketViewL_exact _ _ _ $$ HviewP
  ihave #HcrT' := HcrT $$ %p' %hpb
  ihave #HcrN : mvcc.keyCleanRead (GF := GF) b' (mvcc.bucketViewC (γ.withPhys p'))
      iprop(mvcc.storeRT (γ.withPhys p') ∗ mvcc.restoreRegM d')
      (mvcc.kbNoCmpF (γ.withPhys p').kb (γ.withPhys p').bucket) $$ []
  · rw [← mvcc.kbRecs_empty (γ.withPhys p').kb (γ.withPhys p').bucket, ← mvcc.keyCleanReadR_empty]
    iexact HcrT'
  ihave #HbkT' : mvcc.storeBackendT (GF := GF) b' s (γ.withPhys p') P' $$ [HbkT]
  · rw [← mvcc.storeBackendTR_empty]
    iapply HbkT $$ %p' %hpb
    rw [mvcc.restoreFixM_off d' Hcm']
    itrivial
  iunfold mvcc.storeBackendT at HbkT'
  ihave #HbkW := mvcc.isKeyBackendG_wand $$ HbkT'
  -- the new backend's reader tokens: one lent to `restore`
  icases mvcc.rep_take1 _ $$ Hrts with ⟨Hrt1, Hrts⟩
  ihave Hrt1 : mvcc.storeRT (GF := GF) (γ.withPhys p') $$ [Hrt1]
  · simp only [mvcc.storeRT, mvcc.StoreNames.withPhys_kb, hk]; iexact Hrt1
  -- (M2's item 15) the clean read's token comes with the new backend's registration (off, nothing)
  ihave Hrt1 : iprop(mvcc.storeRT (GF := GF) (γ.withPhys p') ∗ mvcc.restoreRegM d') $$ [Hrt1 Hreg]
  · iframe Hrt1 Hreg
  ihave Hrts : [∗list] _x ∈ List.replicate (mvcc.nReaders - 1) (), mvcc.storeRT (GF := GF) (γ.withPhys p')
      $$ [Hrts]
  · simp only [mvcc.storeRT, mvcc.StoreNames.withPhys_kb, hk]; iexact Hrts
  -- the new pool's tokens, and the writer's
  rw [show mvcc.nReaders - 1 = (mvcc.nReaders - 2) + (2 - 1) by
    rw [mvcc.nReaders_val]]
  icases (mvcc.rep_split _ _ _).1 $$ Hrts with ⟨Hrts, Hnew⟩
  ihave Hnew := mvcc.rep_one _ $$ Hnew
  ihave Hnc : mvcc.kbNoCmp (GF := GF) (γ.withPhys p').kb (γ.withPhys p').bucket $$ [Hnc]
  · simp only [mvcc.StoreNames.withPhys_kb, mvcc.StoreNames.withPhys_bucket, hk, hb]; iexact Hnc
  -- (M3) `restore` reads with the flag alone; the values' halves kept for the writer's loan
  icases (mvcc.kbNoCmp_split _ _).1 $$ Hnc with ⟨Hnc, HncV⟩
  -- the writer's old backend token, and its retired ticket
  have hj0 : mvcc.nJobRd γ.kb = 0 := by
    obtain ⟨d0, hd0, hc0⟩ := Hkb
    rw [hd0]; exact (mvcc.cmOff_res (GF := GF) d0 hc0).2.1
  icases (mvcc.writerOwn_off γ hj0).1 $$ Hown with ⟨HrtOld, Htkr⟩
  -- `compactMainRev`: a quarter for `restore`, a quarter kept (the restoring lock's part agrees)
  icases (mvcc.typedPointsto_halves _ _ _).1 $$ Hcm with ⟨HcmR, HcmK⟩
  ihave #Hiwlb : mvcc.idxWriterLb (GF := GF) (γ.withPhys p').idx ([[], []] ++ R) $$ []
  · iunfold mvcc.idxWriterLb
    simp only [mvcc.StoreNames.withPhys_idx_hist, mvcc.StoreNames.withPhys_idx_nev]
    iframe Hhlb Hnlb
    ipureintro; exact hR.2
  -- `s.restore()`: its lock of `s.revMu` finds the restoring mode (`RevP`: the flag's half and two
  -- later credits), its unlock switches the store to the new objects and names (`restore_switch`)
  have hR' := hRestore s (γ.withPhys p') b' le ti lg (1 : Qp).half
      iprop(mvcc.storeRT (γ.withPhys p') ∗ mvcc.restoreRegM d') (DFrac.own 1) (DFrac.own 1) R
      iprop(dghostVar γ.rst (DFrac.own (1 : Qp).half) true ∗ £ 1 ∗ £ 1)
      iprop(sync.ownRWMutexWLocked (mvcc.revMuAddr s) (mvcc.revMuInv s γ) ∗
        dghostVar γ.rst (DFrac.own (1 : Qp).half) true ∗ dghostVar γ.rst (DFrac.own (1 : Qp).half) true ∗
        (s.[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half} (W64 (-1) : w64) : IProp GF) ∗
        (s.[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half.half} (W64 (-1) : w64) : IProp GF) ∗
        £ 1)
      iprop(dghostVar γ.rst (DFrac.own (1 : Qp).half) false ∗
        mvcc.curAt (γ.withPhys p') (DFrac.own (1 : Qp).half) ⟨b', ti, sc, stopc⟩ ∗
        mvcc.writerFrag (γ.withPhys p') ∗
        mvcc.curAt (γ.withPhys p') (DFrac.own (1 : Qp).half.half.half) ⟨b', ti, sc, stopc⟩ ∗
        mvcc.retiredAt γ 2 ∗ mvcc.wsDep γ ∗ mvcc.restoreWriter γ ([[], []] ++ R) ∗
        ownToks γ.revs (2 ^ 63 - 3 - ([[], []] ++ R).length) ∗
        (if γ.watchQ then mvcc.logQ γ ([[], []] ++ R) else iprop(True)) ∗
        ([∗list] _x ∈ List.replicate (mvcc.nReaders - 2) (), mvcc.storeRT γ) ∗
        mvcc.storeRT (γ.withPhys p') ∗
        (s.[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half.half} (W64 (-1) : w64) : IProp GF) ∗
        mvcc.isTreeIndex ti (γ.withPhys p').idx)
      (DFrac.own (1 : Qp).half.half) (1 : Qp).half (1 : Qp).half γ.leases Ls hR (Qp.half_add_half 1)
  -- `restore`'s lock: the restoring mode's halves of the counters (`compactMainRev`'s at `-1`: the
  -- kept quarter agrees)
  ihave HLk : mvcc.revLockW (GF := GF) s (1 : Qp).half
      iprop(dghostVar γ.rst (DFrac.own (1 : Qp).half) true ∗ £ 1 ∗ £ 1)
      iprop(sync.ownRWMutexWLocked (mvcc.revMuAddr s) (mvcc.revMuInv s γ) ∗
        dghostVar γ.rst (DFrac.own (1 : Qp).half) true ∗ dghostVar γ.rst (DFrac.own (1 : Qp).half) true ∗
        (s.[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half} (W64 (-1) : w64) : IProp GF) ∗
        (s.[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half.half} (W64 (-1) : w64) : IProp GF) ∗
        £ 1) $$ [HcmK]
  · iunfold mvcc.revLockW
    iintro %Ψ ⟨Hr, Hlc3, Hlc4⟩ HΨ
    iapply wp_fupd
    wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$HrevMu] as ⟨Hwl2, HR2⟩
    imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.revMuInv s γ 1)) $$ Hlc3 HR2 with HR2
    iunfold mvcc.revMuInv at HR2
    icases HR2 with ⟨%m, Hr2, HR2⟩
    ihave %Hm := dghostVar_agree γ.rst _ _ _ _ $$ Hr Hr2
    subst Hm
    simp only [↓reduceIte]
    iunfold mvcc.revMuRest at HR2
    icases HR2 with ⟨%v, %c', Hcur2, Hcm2⟩
    icombine Hcm2 HcmK gives %Hcv
    obtain ⟨-, rfl⟩ := Hcv
    imodintro
    iapply HΨ $$ %v Hcur2 [Hwl2 Hr Hr2 Hcm2 HcmK Hlc4]
    iframe Hwl2 Hr Hr2 Hcm2 HcmK Hlc4
  -- `restore`'s unlock: the switch to the new objects and names (`restore_switch`)
  ihave HUl : mvcc.revUnlockW (GF := GF) s (1 : Qp).half ([[], []] ++ R)
      iprop(sync.ownRWMutexWLocked (mvcc.revMuAddr s) (mvcc.revMuInv s γ) ∗
        dghostVar γ.rst (DFrac.own (1 : Qp).half) true ∗ dghostVar γ.rst (DFrac.own (1 : Qp).half) true ∗
        (s.[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half} (W64 (-1) : w64) : IProp GF) ∗
        (s.[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half.half} (W64 (-1) : w64) : IProp GF) ∗
        £ 1)
      iprop(mvcc.bucketViewC (γ.withPhys p') (1 : Qp).half (mvcc.bucketMap ([[], []] ++ R)) ∗
        mvcc.isTreeIndex ti (γ.withPhys p').idx ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          mvcc.idxReader ti (γ.withPhys p').idx) ∗
        ⧖ (mvcc.logCh ([[], []] ++ R)))
      iprop(dghostVar γ.rst (DFrac.own (1 : Qp).half) false ∗
        mvcc.curAt (γ.withPhys p') (DFrac.own (1 : Qp).half) ⟨b', ti, sc, stopc⟩ ∗
        mvcc.writerFrag (γ.withPhys p') ∗
        mvcc.curAt (γ.withPhys p') (DFrac.own (1 : Qp).half.half.half) ⟨b', ti, sc, stopc⟩ ∗
        mvcc.retiredAt γ 2 ∗ mvcc.wsDep γ ∗ mvcc.restoreWriter γ ([[], []] ++ R) ∗
        ownToks γ.revs (2 ^ 63 - 3 - ([[], []] ++ R).length) ∗
        (if γ.watchQ then mvcc.logQ γ ([[], []] ++ R) else iprop(True)) ∗
        ([∗list] _x ∈ List.replicate (mvcc.nReaders - 2) (), mvcc.storeRT γ) ∗
        mvcc.storeRT (γ.withPhys p') ∗
        (s.[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half.half} (W64 (-1) : w64) : IProp GF) ∗
        mvcc.isTreeIndex ti (γ.withPhys p').idx)
      $$ [Hcur Hfrag HcurR HcurW Htkr Hheld Hrts Hlc3 Hwsd Hnew HXn]
  · iunfold mvcc.revUnlockW
    iintro %Ψ Hcur2 ⟨Hwl2, Hr, Hr2, Hcm2, HcmK, Hlc4⟩ ⟨Hv, #Hti', Hrd, #Hrc⟩ HΨ
    iunfold mvcc.wsDep at Hwsd
    ihave Hrd := mvcc.rep_nReaders _ $$ Hrd
    imod (mvcc.restore_switch s γ ⟨b, ti0, GoInterface.ok fi, sstop⟩ ⟨b', ti, sc, stopc⟩ p' R (-1) (-1)
        1 2 hR (by decide) (by simp; omega) (Nat.le_refl 2)) $$
        Hlc4 Hlc3 Hwi Hwsd Hpool Hcur Hfrag HcurR HcurW Htkr Hr Hr2 Hheld Hcur2 Hcm2 [] [] Hnlb Hok'
        [Hv] Hrd [] [] Hrts HXn
      with ⟨HR, Hrst', Hn1, Hfrag', Hn3, Htkr, Hwsd, Hw, Hrv', HlogQ, Hold, -⟩
    · iunfold mvcc.lagTok; simp only [↓reduceIte]; itrivial
    · iapply mvcc.crevPermAt_none
    · iintro -
      iapply mvcc.bucketViewL_exact
      iapply mvcc.bucketViewC_bucketView
      iexact Hv
    · iexact Hrc
    · ipureintro; exact Hrb
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl2 HR]
    · inext; iexact HR
    iapply HΨ
    iunfold mvcc.wsDep
    iframe Hrst' Hn1 Hfrag' Hn3 Htkr Hwsd Hw Hrv' HlogQ Hold Hnew HcmK Hti'
  wp_apply +noauto hR' $$ [$Hfb $Hrt1 $Hnc $HviewR $Hfidx $Hix $Hig $Hcr $HcmR $HLk $HUl Hrst Hlc1 Hlc2
      HLo]
    as ⟨⟨⟨Hrt1, -⟩, Hnc, Hrc, HRevQ, Hcr, HcmR, Hfb, Hfidx⟩, HLo⟩
  · iframe #; iframe Hrst Hlc1 Hlc2 HLo
    isplitr
    · ipureintro; exact Hlgnn
    ipureintro; exact Hlok
  wp_auto_lc 1
  icases HRevQ with ⟨Hrst', Hn1, Hfrag', Hn3, Htkr, Hwsd, Hw, Hrv, HlogQ, Hold, Hnew, HcmK,
    #Hti'⟩
  -- the writer's state at `L'`, the new backend's registration pending (`restore_finish`)
  -- (question 5's core stage, part (1)) the new store does not compact (Q5-3): no write right's key,
  -- no compaction facts
  have hnc : ¬ mvcc.kbCmpM (γ.withPhys p').kb := by
    simp only [mvcc.StoreNames.withPhys_kb, hk]; exact (mvcc.cmOff_res (GF := GF) d' Hcm').1
  ihave HtrC : mvcc.cmpTrack (GF := GF) (γ.withPhys p') ([[], []] ++ R)
      (mvcc.bucketMap ([[], []] ++ R)) ⟨none, none⟩ $$ []
  · iapply mvcc.cmpTrack_off _ hnc
  ihave Hcres : mvcc.compactRes (GF := GF) (γ.withPhys p') ([[], []] ++ R) $$ [Hmeta' Hfin' HviewC HtrC]
  · iunfold mvcc.compactRes
    iexists none, none, 0, mvcc.bucketMap ([[], []] ++ R)
    iunfold mvcc.metaCompact
    simp only [mvcc.StoreNames.withPhys_cmeta, mvcc.StoreNames.withPhys_fin]
    iframe Hmeta' Hfin' HviewC HtrC
    isplitr
    · ipureintro; exact Nat.le_refl _
    iapply mvcc.mwSlot_off _ hnc
  ihave Hrr : mvcc.kbRegRight (GF := GF) p'.kb $$ [Hrr]
  · rw [hk]; iexact Hrr
  imod receipt_snapshot _ $$ Hrc with ⟨-, #Hrc⟩
  -- (2026-11-06) the writer's loan (the new backend's no-compaction token, nothing deletable), its
  -- pin's view and the revision tokens, into the writer's state
  ihave Hloan : mvcc.writerLoan (GF := GF) (γ.withPhys p') $$ [Hnc HncV]
  · iunfold mvcc.writerLoan
    rw [if_neg hnc]
    isplitl [Hnc HncV]
    · rw [← mvcc.StoreNames.withPhys_kb γ p', ← mvcc.StoreNames.withPhys_bucket γ p']
      iapply (mvcc.kbNoCmp_split _ _).2
      iframe Hnc HncV
    simp only [mvcc.kbNoDel, mvcc.StoreNames.withPhys_kb, hk]; iexact Hnd
  ihave HY : mvcc.slotY (GF := GF) (γ.withPhys p') ([[], []] ++ R) $$ [HYa HYp HwcY]
  · iunfold mvcc.slotY
    iexists (-1)
    simp only [mvcc.StoreNames.withPhys_api]
    iframe HYa HwcY
    isplitl [HYp]
    · rw [show mvcc.pndW (γ.withPhys p') = mvcc.pndW γ from rfl]; iexact HYp
    unfold mvcc.rcvW
    simp only [mvcc.StoreNames.withPhys_kb, hk, Hcm', Bool.false_eq_true, ↓reduceIte]
    itrivial
  imod (mvcc.restore_finish s γ ⟨b', ti, sc, stopc⟩ p' ([[], []] ++ R) hR.2 (by simp)
      (mvcc.restoreLog_ch R hR.1)) $$
      Hlc1 Hwi Hn3 Hw Hcr Hrc Hnlb Hwk' Hwv' HviewW Hcres Hrr HfzK Hrv Hloan HviewP HY
    with ⟨Hwr, #HcertL, #Hreg', Hfr⟩
  -- the fields' shares at the new objects and names, with what they are (`physOk`)
  ihave #Hph2 : mvcc.physOk (GF := GF) s (γ.withPhys p') ⟨b', ti, sc, stopc⟩ $$ []
  · iunfold mvcc.physOk
    iexists P', iprop(True)
    simp only [named]
    isplitl []
    · iunfold mvcc.hookP; simp only [mvcc.StoreNames.withPhys_hook]; iexact Hh'
    isplitl []
    · iapply mvcc.isKeyBackendG_ncFalse $$ HbkT'
    isplitl []
    · imodintro; itrivial
    isplitl []
    · rw [show (γ.withPhys p').idx = (⟨γ.idx.hist, p'.nev, γ.idx.log, γ.idx.crev, p'.cmp⟩ :
        mvcc.IdxNames) from rfl]
      iexact Hti'
    isplitl []
    · simp only [mvcc.StoreNames.withPhys_sch]; iexact HisFifo
    isplitl []
    · iapply mvcc.physCmp_off _ _ hnc
    isplitl []
    · iunfold mvcc.stopPayAt
      simp only [mvcc.StoreNames.withPhys_sx, mvcc.StoreNames.withPhys_sch, hsx, hs]
      iframe Hx' Hpi
    ipureintro
    simp only [mvcc.StoreNames.withPhys_kb, mvcc.StoreNames.withPhys_cm, hk]
    obtain ⟨d0, hd0, hc0⟩ := Hkb
    rw [hd0] at Hcmt
    show d'.cm = true ↔ γ.cm = true
    rw [Hcm']
    have : ¬ (γ.cm = true) := fun h => by have := Hcmt.2 h; simp [mvcc.kbCmpM, hc0] at this
    simpa using this
  ihave Hfs : mvcc.fieldShareAt (GF := GF) s (γ.withPhys p')
      ((1 : Qp).half + ((1 : Qp).half.half + (1 : Qp).half.half)) ⟨b', ti, sc, stopc⟩
      $$ [Hn1 Hrst' Hfb Hfidx Hfsch Hfstop]
  · rw [Qp.half_add_half, Qp.half_add_half]
    iunfold mvcc.fieldShareAt
    simp only [named, mvcc.StoreNames.withPhys_rst]
    iframe Hn1 Hrst' Hph2
    iunfold mvcc.storeFields
    simp only [named]
    iframe Hfb Hfidx Hfsch Hfstop
  icases (mvcc.fieldShareAt_split s _ _ _ _).1 $$ Hfs with ⟨HfsM, Hfs⟩
  icases (mvcc.fieldShareAt_split s _ _ _ _).1 $$ Hfs with ⟨HfsC, HfsW⟩
  -- `defer s.mu.Unlock()`: `s.mu`'s resource at the new objects
  ihave Hcm : (s.[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half} (W64 (-1) : w64) : IProp GF)
      $$ [HcmR HcmK]
  · iapply (mvcc.typedPointsto_halves _ _ _).2; iframe HcmR HcmK
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl HcrevM Hcm Hwr HfsM HwcM]
  · inext
    iunfold mvcc.muInv
    iexists (-1)
    iframe Hwr
    isplitl [Hcm HcrevM HwcM]
    · iunfold mvcc.muInvAt; simp only [named]; iframe Hcm HcrevM; iframe #
      isplitl [HwcM]
      · (try rw [mvcc.StoreNames.withPhys_api]); iexact HwcM
      ipureintro; decide
    iunfold mvcc.fieldShare
    iexists p', ⟨b', ti, sc, stopc⟩
    iexact HfsM
  (try wp_auto)
  iapply HΦ
  iexists p'
  iunfold mvcc.slotFr at Hfr
  rw [mvcc.resumeBackM_no _ _ _ _ _ _ mvcc.CmpRecs.resumes_empty]
  iframe Hwsd Hfrag' HcertL HlogQ Hfr HnlLb HRr
  isplitl []
  · ipureintro; exact ⟨hb, hk⟩
  isplitl [HfsC Hstop HsStop Hq0 Hcmp0]
  · iapply (mvcc.storeCloserM_off s (γ.withPhys p') _ hnc).2
    iunfold mvcc.storeCloser
    iexists ⟨b', ti, sc, stopc⟩
    iframe HfsC
    isplitl []
    · iunfold mvcc.isStopChan; iexists γstop; iexact Hstop0
    isplitl [Hstop]
    · iunfold mvcc.stopCloser; iexists γstop; iexact Hstop
    simp only [mvcc.StoreNames.withPhys_sch]
    iframe HsStop
    iunfold mvcc.compactQueue
    iexists [n₀], p₀, iprop(True), mvcc.compactTok (γ.withPhys p') (-1)
    rw [List.singleton_append]
    simp only [mvcc.StoreNames.withPhys_sch]
    iframe Hq0 Hp0
    isplitl [Hcmp0]
    · iunfold mvcc.compactTok
      isplitl [Hcmp0]
      · iexists -1
        iframe Hcmp0
        ipureintro; exact Int.le_refl _
      -- no restore in compaction mode (Q5-3): the new store's job has no budgets, no cursor
      isplitr
      · simp only [mvcc.StoreNames.withPhys_kb, hk]
        iapply (mvcc.cmOff_res d' Hcm').2.2.1.2
        itrivial
      iexists ((-1 : Int), (⟨W64 0, W64 0⟩ : mvcc.Rev))
      isplitr
      · iapply mvcc.jobCur_off _ hnc
      ipureintro; exact Int.le_refl _
    iintro ⟨-, H⟩
    iexact H
  isplitl [HfsW]
  · iunfold mvcc.fieldShare; iexists p', ⟨b', ti, sc, stopc⟩; iexact HfsW
  isplitl [Hrt1 Htkr]
  · iapply (mvcc.writerOwn_off (γ.withPhys p') (by
      simp only [mvcc.StoreNames.withPhys_kb, hk]; exact (mvcc.cmOff_res (GF := GF) d' Hcm').2.1)).2
    unfold mvcc.retiredAt; simp only [mvcc.StoreNames.withPhys_tkr]
    iframe Hrt1 Htkr
  isplitl []
  · iunfold mvcc.hookP; simp only [mvcc.StoreNames.withPhys_hook]; iexact Hh'
  isplitl []
  · iexact Hreg'
  isplitl [HrtOld Hold]
  · have h2 := sync.actualMaxReaders_ge_2
    rw [show mvcc.nReaders - 2 + (2 - 1) = (mvcc.nReaders - 2) + 1 from rfl, List.replicate_succ]
    iapply BigSepL.bigSepL_cons.2
    iframe HrtOld Hold
  iframe Hnew HLo
  ipureintro; exact hLR

end proof

end EtcdGrove
end Perennial
