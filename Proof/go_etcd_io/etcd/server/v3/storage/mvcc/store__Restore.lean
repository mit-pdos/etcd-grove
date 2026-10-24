/-
Proof of `Spec/.../mvcc/store__Restore.lean` (`kvstore.go`; the restore plan's R5f; the trust
boundary until then: D22m decided, D22 receiver epochs S6). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Restore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__restore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newTreeIndex
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.Scheduler__Stop
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.NewFIFOScheduler
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreMoves

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

theorem mvcc.store.Restore.wp_proof
    (hStop : schedule.Scheduler.Stop.spec (GF := GF) (hG := hG))
    (hNewIdx : mvcc.newTreeIndex.spec (GF := GF) (hG := hG))
    (hFifo : schedule.NewFIFOScheduler.spec (GF := GF) (hG := hG))
    (hRestore : mvcc.store.restore.spec (GF := GF) (hG := hG)) :
    mvcc.store.Restore.spec (GF := GF) (hG := hG) := by
  intro s γ b' d' γb' P' L R hLR hR
  wp_start as ⟨#Hs, %Hkb, Hcl, Hfs, Hwsd, Hfrag, Hown, #Hfrz, #HcL, Htoks, HlogQ, #Hok', #HbkT,
    #HcrT, Hview, Hnc, Hrr, Hrts⟩
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule $$ []
  · iPkgInit
  ihave #Hs' := Hs
  iunfold mvcc.isStore at Hs'
  iNamed Hs'
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
  wp_apply wp_broadcast_chan_close _ γc iprop(True) $$ [$Hstcl] as -
  · imodintro; itrivial
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
  wp_apply hStop fi γ.sch (Ps ++ [p]) $$ [Htok Hq]
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
  imod (mvcc.restore_takeover s γ ⟨b, ti0, GoInterface.ok fi, sstop⟩ L ([[], []] ++ R) hLR) $$
      Hlc2 Hwi HR Hfrst Hcur Hwr HcL Htoks HlogQ HcrevM HcmpM
    with ⟨⟨%v0, Hcr⟩, Hcm, Hrst, Hcur, HcurR, HcurW, HcrevM, Hheld, #Hhlb⟩
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
  wp_apply hFifo $$ [] as %sc ⟨%γs, %n₀, %p₀, #HisFifo, HsStop, Hq0, #Hp0⟩
  · ipureintro; exact Hlgnn
  (try wp_auto)
  wp_apply +noauto chan.wp_make1 (V := Unit) as %stopc %γstop ⟨#Hstc', %Hstcap, Hstown⟩
  wp_auto_lc 2
  imod alloc_broadcast_chan (E := ⊤) iprop(True) γstop stopc $$ Hstc' Hstown with Hstop
  ihave #Hstop0 := ownBroadcastChan_Unknown _ _ _ _ $$ Hstop
  -- the new backend's names, fresh: the batch lock's invariant `P'`, its key and view log, the
  -- compaction's record
  imod (saved_prop_alloc (GF := GF) P' DFrac.discard DFrac.valid_discard) with ⟨%γh', #Hh'⟩
  imod ghostVar_alloc (GF := GF) () with ⟨%γwk', Hwk'⟩
  imod ghostVar_alloc (GF := GF) ([[], []] ++ R) with ⟨%γwv', Hwv'⟩
  imod ghostVar_alloc (GF := GF) ((none, none) : Option w64 × Option w64) with ⟨%γm', Hmeta'⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γfin', Hfin', -⟩
  obtain ⟨p', hnv, hcm, hb, hh, hk, hm, hfin, hs, hwk, hwv⟩ : ∃ p' : mvcc.PhysNames,
      p'.nev = nv ∧ p'.cmp = cm ∧ p'.bucket = γb' ∧ p'.hook = γh' ∧ p'.kb = some d' ∧
      p'.cmeta = γm' ∧ p'.fin = γfin' ∧ p'.sch = γs ∧ p'.wk = γwk' ∧ p'.wv = γwv' :=
    ⟨⟨nv, cm, γb', γh', γ.hookFn, some d', γm', γfin', γs, γwk', γwv'⟩,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
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
  ihave #HcrT' := HcrT $$ %p' %hpb
  ihave Hrv := mvcc.restoreView_of b' (γ.withPhys p') (mvcc.storeRT (γ.withPhys p')) (1 : Qp).half R
    $$ [HviewR]
  · iframe HviewR; iexact HcrT'
  ihave #HbkT' := HbkT $$ %p' %hpb
  iunfold mvcc.storeBackendT at HbkT'
  ihave #HbkW := mvcc.isKeyBackendG_wand $$ HbkT'
  -- the new backend's reader tokens: one lent to `restore`
  icases mvcc.rep_take1 _ $$ Hrts with ⟨Hrt1, Hrts⟩
  ihave Hrt1 : mvcc.storeRT (GF := GF) (γ.withPhys p') $$ [Hrt1]
  · simp only [mvcc.storeRT, mvcc.StoreNames.withPhys_kb, hk]; iexact Hrt1
  ihave Hrts : [∗list] _x ∈ List.replicate (mvcc.nReaders - 1) (), mvcc.storeRT (GF := GF) (γ.withPhys p')
      $$ [Hrts]
  · simp only [mvcc.storeRT, mvcc.StoreNames.withPhys_kb, hk]; iexact Hrts
  ihave Hnc : mvcc.kbNoCmp (GF := GF) (γ.withPhys p').kb (γ.withPhys p').bucket $$ [Hnc]
  · simp only [mvcc.StoreNames.withPhys_kb, mvcc.StoreNames.withPhys_bucket, hk, hb]; iexact Hnc
  -- the writer's old backend token, and its retired ticket
  iunfold mvcc.writerOwn at Hown
  icases Hown with ⟨HrtOld, Htkr⟩
  -- `compactMainRev`: a quarter for `restore`, a quarter kept (the restoring lock's part agrees)
  icases (mvcc.typedPointsto_halves _ _ _).1 $$ Hcm with ⟨HcmR, HcmK⟩
  ihave #Hiwlb : mvcc.idxWriterLb (GF := GF) (γ.withPhys p').idx ([[], []] ++ R) $$ []
  · iunfold mvcc.idxWriterLb
    simp only [mvcc.StoreNames.withPhys_idx_hist, mvcc.StoreNames.withPhys_idx_nev]
    iframe Hhlb Hnlb
    ipureintro; exact hR.2.1
  -- `s.restore()`: its lock of `s.revMu` finds the restoring mode (`RevP`: the flag's half and two
  -- later credits), its unlock switches the store to the new objects and names (`restore_switch`)
  have hR' := hRestore s (γ.withPhys p') b' le ti lg (1 : Qp).half P' (mvcc.hookFn (γ.withPhys p'))
      (mvcc.storeRT (γ.withPhys p')) (mvcc.storeWT (γ.withPhys p')) (mvcc.storeW s (γ.withPhys p'))
      (mvcc.kbWi (γ.withPhys p').kb) iprop(True) (mvcc.storeCmp (γ.withPhys p'))
      (mvcc.storePutOk (γ.withPhys p')) (DFrac.own 1) (DFrac.own 1) R
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
        ownToks γ.tkr 1 ∗ mvcc.restoreWriter γ ([[], []] ++ R) ∗
        ownToks γ.revs (2 ^ 63 - 3 - ([[], []] ++ R).length) ∗
        (if γ.watchQ then mvcc.logQ γ ([[], []] ++ R) else iprop(True)) ∗
        (∃ k : Nat, ⌜k + 1 ≤ mvcc.nReaders⌝ ∗ ([∗list] _x ∈ List.replicate k (), mvcc.storeRT γ) ∗
          ([∗list] _x ∈ List.replicate (mvcc.nReaders - 1 - k) (), mvcc.storeRT (γ.withPhys p'))) ∗
        (s.[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half.half} (W64 (-1) : w64) : IProp GF) ∗
        mvcc.isTreeIndex ti (γ.withPhys p').idx)
      (DFrac.own (1 : Qp).half.half) (1 : Qp).half (1 : Qp).half hR (Qp.half_add_half 1)
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
      iprop(mvcc.restoreViewOut (γ.withPhys p') (1 : Qp).half R ∗
        mvcc.isTreeIndex ti (γ.withPhys p').idx ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          mvcc.idxReader ti (γ.withPhys p').idx) ∗
        ⌜mvcc.logCh ([[], []] ++ R) < receiptBound GF⌝)
      iprop(dghostVar γ.rst (DFrac.own (1 : Qp).half) false ∗
        mvcc.curAt (γ.withPhys p') (DFrac.own (1 : Qp).half) ⟨b', ti, sc, stopc⟩ ∗
        mvcc.writerFrag (γ.withPhys p') ∗
        mvcc.curAt (γ.withPhys p') (DFrac.own (1 : Qp).half.half.half) ⟨b', ti, sc, stopc⟩ ∗
        ownToks γ.tkr 1 ∗ mvcc.restoreWriter γ ([[], []] ++ R) ∗
        ownToks γ.revs (2 ^ 63 - 3 - ([[], []] ++ R).length) ∗
        (if γ.watchQ then mvcc.logQ γ ([[], []] ++ R) else iprop(True)) ∗
        (∃ k : Nat, ⌜k + 1 ≤ mvcc.nReaders⌝ ∗ ([∗list] _x ∈ List.replicate k (), mvcc.storeRT γ) ∗
          ([∗list] _x ∈ List.replicate (mvcc.nReaders - 1 - k) (), mvcc.storeRT (γ.withPhys p'))) ∗
        (s.[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half.half} (W64 (-1) : w64) : IProp GF) ∗
        mvcc.isTreeIndex ti (γ.withPhys p').idx)
      $$ [Hcur Hfrag HcurR HcurW Htkr Hheld Hrts]
  · iunfold mvcc.revUnlockW
    iintro %Ψ Hcur2 ⟨Hwl2, Hr, Hr2, Hcm2, HcmK, Hlc4⟩ ⟨Hv, #Hti', Hrd, %Hrc⟩ HΨ
    imod (mvcc.restore_switch s γ ⟨b, ti0, GoInterface.ok fi, sstop⟩ ⟨b', ti, sc, stopc⟩ p' R hR) $$
        Hlc4 Hpool Hcur Hfrag HcurR HcurW Htkr Hr Hr2 Hheld Hcur2 Hcm2 Hnlb Hok' Hv Hrd [] [] Hrts
      with ⟨HR, Hrst', Hn1, Hfrag', Hn3, Htkr, Hw, Hrv', HlogQ, Hks⟩
    · ipureintro; exact Hrc
    · ipureintro; exact Hrb
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl2 HR]
    · inext; iexact HR
    iapply HΨ
    iframe Hrst' Hn1 Hfrag' Hn3 Htkr Hw Hrv' HlogQ Hks HcmK Hti'
  wp_apply +noauto hR' $$ [$Hfb $Hrt1 $Hnc $Hrv $Hfidx $Hix $Hig $Hcr $HcmR $HLk $HUl Hrst Hlc1 Hlc2]
    as ⟨Hrt1, Hrc, HRevQ, Hcr, HcmR, Hfb, Hfidx⟩
  · iframe #; iframe Hrst Hlc1 Hlc2; ipureintro; exact Hlgnn
  wp_auto_lc 1
  icases HRevQ with ⟨Hrst', Hn1, Hfrag', Hn3, Htkr, Hw, Hrv, HlogQ, ⟨%k, %Hk1, Hold, Hnew⟩, HcmK,
    #Hti'⟩
  -- the writer's state at `L'`, the new backend's registration pending (`restore_finish`)
  ihave Hcres : mvcc.compactRes (GF := GF) (γ.withPhys p') $$ [Hmeta' Hfin']
  · iunfold mvcc.compactRes
    iexists none, none, 0
    iunfold mvcc.metaCompact
    simp only [mvcc.StoreNames.withPhys_cmeta, mvcc.StoreNames.withPhys_fin]
    iframe Hmeta' Hfin'
    ipureintro; exact Nat.le_refl _
  ihave Hrr : mvcc.kbRegRight (GF := GF) p'.kb $$ [Hrr]
  · rw [hk]; iexact Hrr
  imod (mvcc.restore_finish s γ ⟨b', ti, sc, stopc⟩ p' ([[], []] ++ R) hR.2.1 (by simp)) $$
      Hlc1 Hwi Hn3 Hw Hcr Hrc Hnlb Hwk' Hwv' HviewW Hcres Hrr with ⟨Hwr, #HcertL⟩
  -- the fields' shares at the new objects and names, with what they are (`physOk`)
  ihave #Hph2 : mvcc.physOk (GF := GF) s (γ.withPhys p') ⟨b', ti, sc, stopc⟩ $$ []
  · iunfold mvcc.physOk
    iexists P', iprop(True)
    simp only [named]
    isplitl []
    · iunfold mvcc.hookP; simp only [mvcc.StoreNames.withPhys_hook]; iexact Hh'
    iframe HbkT'
    isplitl []
    · imodintro; itrivial
    isplitl []
    · rw [show (γ.withPhys p').idx = (⟨γ.idx.hist, p'.nev, γ.idx.log, γ.idx.crev, p'.cmp⟩ :
        mvcc.IdxNames) from rfl]
      iexact Hti'
    simp only [mvcc.StoreNames.withPhys_sch]; iexact HisFifo
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
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl HcrevM Hcm Hwr HfsM]
  · inext
    iunfold mvcc.muInv
    iexists (-1)
    iframe Hwr
    isplitl [Hcm HcrevM]
    · iunfold mvcc.muInvAt; simp only [named]; iframe Hcm HcrevM; iframe #; ipureintro; decide
    iunfold mvcc.fieldShare
    iexists p', ⟨b', ti, sc, stopc⟩
    iexact HfsM
  (try wp_auto)
  iapply HΦ
  iexists p', k
  iframe Hwsd Hfrag' HcertL Hrv HlogQ
  isplitl []
  · ipureintro; exact ⟨hb, hk, Hk1⟩
  isplitl [HfsC Hstop HsStop Hq0 Hcmp0]
  · iunfold mvcc.storeCloser
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
      iexists -1
      iframe Hcmp0
      ipureintro; exact Int.le_refl _
    iintro ⟨-, H⟩
    iexact H
  isplitl [HfsW]
  · iunfold mvcc.fieldShare; iexists p', ⟨b', ti, sc, stopc⟩; iexact HfsW
  isplitl [Hrt1 Htkr]
  · iunfold mvcc.writerOwn; simp only [mvcc.StoreNames.withPhys_tkr]; iframe Hrt1 Htkr
  isplitl []
  · iunfold mvcc.hookP; simp only [mvcc.StoreNames.withPhys_hook]; iexact Hh'
  isplitl [HrtOld Hold]
  · rw [List.replicate_succ]
    iapply BigSepL.bigSepL_cons.2
    iframe HrtOld Hold
  rw [show mvcc.nReaders - (k + 1) = mvcc.nReaders - 1 - k by omega]
  iexact Hnew

end proof

end EtcdGrove
end Perennial
