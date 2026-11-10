/-
**B3 (mvccfull F1): `NewStore` over a backend holding an image** (`kvstore.go` l.87-133): the proof of
`mvcc.NewStore.spec` (`NewStore.lean`'s `wp_proof` is this theorem). The fresh proof's (commit
`ae30739dde`) batch session and allocations, with:
* the session over the session contract (`storeSessT`), its `Unlock` given the unregistered `Wi`
  (`sess_W_of_Wi`): the registration stays pending (`writerReg_allocP`, as `store.Restore`);
* the caller's index names grown to the image's log (`idxFresh_image`);
* `restore()` at `ns = false` over the clean read, lent the reader's token and the unfixed
  registration, both back in its `restoreDone`, where the store is made at the restored log (the
  registration fixed, `storeSess_fix`), and, when the records resume a compaction, the resumed
  `compactLockfree` (`hCLF`), as `store.Restore`'s on-arm;
* `s.mu` locked as private memory and made a lock at once from the write-locked memory
  (`init_RWMutex_wlocked`, `RWMutexWLocked.lean`), so that the resumed compaction finds the store.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewStore
public import Spec.go_uber_org.zap.NewNop
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newTreeIndex
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.NewFIFOScheduler
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewHashStorage
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.UnsafeCreateMetaBucket
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__restore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__compactLockfree
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreNC
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.CmpSteps
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.NewStoreImage
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.NewStoreLineup
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RWMutexWLocked

@[expose] public section

set_option linter.unusedSectionVars false
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
variable [go_etcd_io.etcd.cache.v3.Assumptions]


/-- One of the backend's reader tokens the store takes (`nReaders`, the backend's stock), and the
rest back from it. -/
theorem mvcc.nsr_slot_take (Q : IProp GF) :
    ([∗list] _x ∈ List.replicate mvcc.nReaders (), Q) ⊢
      Q ∗ (Q -∗ [∗list] _x ∈ List.replicate mvcc.nReaders (), Q) := by
  obtain ⟨m, hm⟩ : ∃ m, mvcc.nReaders = m + 1 := ⟨mvcc.nReaders - 1, by rw [mvcc.nReaders_val]⟩
  rw [hm, List.replicate_succ]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, Hs⟩
  iframe H1
  iintro H1
  iapply BigSepL.bigSepL_cons.2
  iframe H1 Hs

/-- The store's reader handles (of a store that may be compacted) from the reader slots of its
two locks and the readers' tickets (D22 receiver epochs, S4: the index's slots are in the readers'
pool; S5a: so are the backend's reader tokens). -/
theorem mvcc.nsr_storeReaders_of_slots (s : Loc) (γ : mvcc.StoreNames) : ∀ (n : Nat),
    ([∗list] _x ∈ List.replicate n (), sync.ownRWMutex (mvcc.muAddr s) (mvcc.muInv (GF := GF) s γ)) ∗
      ([∗list] _x ∈ List.replicate n (), sync.ownRWMutex (mvcc.revMuAddr s) (mvcc.revMuInv s γ)) ∗
      ([∗list] _x ∈ List.replicate n (), ownToks γ.tk 1) ⊢
      [∗list] _x ∈ List.replicate n (), mvcc.storeReaderC s γ
  | 0 => by rw [List.replicate_zero]; iintro _; iapply BigSepL.bigSepL_nil_intro; iempintro
  | n + 1 => by
    rw [List.replicate_succ]
    iintro ⟨Hm, Hr, Hk⟩
    icases BigSepL.bigSepL_cons.1 $$ Hm with ⟨Hm1, Hm⟩
    icases BigSepL.bigSepL_cons.1 $$ Hr with ⟨Hr1, Hr⟩
    icases BigSepL.bigSepL_cons.1 $$ Hk with ⟨Hk1, Hk⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hm1 Hr1 Hk1]
    · iunfold mvcc.storeReaderC
      simp only [named]
      iframe Hm1 Hr1 Hk1
    · iapply mvcc.nsr_storeReaders_of_slots s γ n
      iframe Hm Hr Hk

/-- `n` tokens, one by one. -/
theorem mvcc.nsr_ownToks_ones (γ : GName) : ∀ (n : Nat),
    ownToks (GF := GF) γ n ⊢ [∗list] _x ∈ List.replicate n (), ownToks γ 1
  | 0 => by rw [List.replicate_zero]; iintro _; iapply BigSepL.bigSepL_nil_intro; iempintro
  | n + 1 => by
    rw [List.replicate_succ]
    iintro H
    icases (ownToks_add 1 n γ).1 $$ H with ⟨Hn, H1⟩
    iapply BigSepL.bigSepL_cons.2
    iframe H1
    iapply mvcc.nsr_ownToks_ones γ n
    iexact Hn

theorem mvcc.NewStore.wp_proofR
    (hNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (hNewIdx : mvcc.newTreeIndex.spec (GF := GF) (hG := hG))
    (hFifo : schedule.NewFIFOScheduler.spec (GF := GF) (hG := hG))
    (hHash : mvcc.NewHashStorage.spec (GF := GF) (hG := hG))
    (hMeta : schema.UnsafeCreateMetaBucket.spec (GF := GF) (hG := hG))
    (hRestore : mvcc.store.restore.spec (GF := GF) (hG := hG))
    (hCLF : mvcc.store.compactLockfree.spec (GF := GF) (hG := hG)) :
    mvcc.NewStore.spec (GF := GF) (hG := hG) := by
  intro _ lg b le cfg d γb γl P rd0 wq γi γok M Perm R r Ls hkH PreH QH PostH XH YH dqh
  have Hrb0 : receiptBound GF ≤ 2 ^ 48 := ReceiptBoundLe.le (GF := GF) _
  wp_start as ⟨⟨%Hcfg0, %hR⟩, #Hpkg, #HbkS, HbkT, #HcrT, Hreg, Himg, #Hrc0, #Hnd, Hrg, Hwt1, Hwt2,
    Hsrm, Hrts, Hlrd, #Hlessor, Hro, Hlown, %Hlok, Hifresh, Hok, #HokC, #HpF, #HpC, HrH, Hsup⟩
  -- the image, in either mode: the clean view of the cut entries, the records, the values' halves
  icases mvcc.restoreImageM_norm d γb _ r $$ Himg with ⟨%ents, Hview, Hnc, Hvals, %Himg⟩
  obtain ⟨hrec, hpos, hcut, hoff⟩ := Himg
  have hlen := mvcc.restoreLogOk_len hR
  have hlb : mvcc.LogB ([[], []] ++ R) := by
    obtain ⟨-, ⟨-, hlen1, -, hcs⟩⟩ := hR
    exact ⟨by omega, hcs⟩
  have hcl : r.crev < (([[], []] ++ R).length : Int) := mvcc.recsOk_crev_lt _ r hrec hlen.1
  have hcge : -1 ≤ r.crev := mvcc.CmpRecs.crev_ge _ r hrec
  have hfb := mvcc.CmpRecs.finRev_bounds _ r hrec
  have hnr : 3 ≤ mvcc.nReaders := mvcc.nReaders_ge_3
  have hjr : mvcc.nJobRd (some d) ≤ 1 := mvcc.nJobRd_le (some d)
  -- package facts: the configuration defaults, the `Key` bucket, zap, schedule, schema
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, #Hdbl, ⟨%dsi, #Hdsi⟩, -⟩
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hsch
  icases Hsi with ⟨-, -, -, ⟨%bK, #HKeyG, -⟩, -⟩
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hsched : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule $$ []
  · iPkgInit
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto_lc 1
  wp_apply wp_with_defer
  iintro %defer Hdefer
  (try wp_auto)
  -- `if lg == nil { lg = zap.NewNop() }`
  wp_join iprop(∃ lg' : Loc, lg_ptr ↦ lg' ∗ ⌜lg' ≠ null⌝) with [lg] as ⟨%lg', lg, %Hlgnn⟩
  · wp_apply hNop as %l #Hlz
    ihave %Hl := zapLoggerOk_ne_null l $$ Hlz
    (try wp_auto)
    wp_join_done
    iexists l; iframe lg; ipureintro; exact Hl
  · iexists lg; iframe lg; ipureintro; exact Hif
  -- the configuration's defaults: a zero batch limit is the default's (`1000`), so positive, and
  -- at most `rangeLimitMax` (the premise `batchLimitOk`)
  wp_join iprop(∃ c : StoreConfig, cfg_ptr ↦ c ∗
      ⌜0 < sint.Z c.CompactionBatchLimit' ∧ sint.Z c.CompactionBatchLimit' ≤ rangeLimitMax⌝) with [cfg]
    as ⟨%cfg1, cfg, %Hcfg1⟩
  · iexists _; iframe cfg; ipureintro; simp only; decide
  · iexists _; iframe cfg; ipureintro
    have h0 : sint.Z cfg.CompactionBatchLimit' ≠ 0 := by intro h; apply Hif; word
    unfold batchLimitOk at Hcfg0
    omega
  wp_join iprop(∃ c : StoreConfig, cfg_ptr ↦ c ∗
      ⌜0 < sint.Z c.CompactionBatchLimit' ∧ sint.Z c.CompactionBatchLimit' ≤ rangeLimitMax⌝) with [cfg]
    as ⟨%cfg2, cfg, %Hcfg2⟩
  · iexists _; iframe cfg; ipureintro; exact Hcfg1
  · iexists _; iframe cfg; ipureintro; exact Hcfg1
  -- the store's struct
  -- (B3) the caller's index names grown to the image's log, the compaction revision at the records'
  imod mvcc.idxFresh_image γi ([[], []] ++ R) r.crev hR.2 hcge $$ Hifresh
    with ⟨Hnauth0, Hcmpf, #Hclb0, #Hllb0, HiwNR, Hil, Hcu, #Hclbc, #Hiwlb⟩
  wp_apply (hNewIdx γi lg' _ ([[], []] ++ R)) $$ [Hnauth0 Hcmpf] as %ti ⟨Hix, Hig, Hcmp0⟩
  · iframe Hnauth0 Hcmpf; iframe #; ipureintro; exact Hlgnn
  -- the new index's lock at the records' compaction revision
  imod mvcc.idxLockG_raise γi _ r.crev ([[], []] ++ R) hcl $$ Hig Hcmp0 Hclbc Hllb0
    with ⟨Hig, Hcmp0⟩
  (try wp_auto)
  -- (M2, the storage side, item 34) the scheduler's payload, the stop channel closed, through an
  -- agreement name allocated first (the channel is made after the scheduler)
  imod (dghostVar_alloc (GF := GF) (null : Loc)) with ⟨%γx, Hx⟩
  wp_apply hFifo _ (mvcc.stopPay γx) $$ [] as %sc ⟨%γs, %n₀, %p₀, #HisFifo, HsStop, Hq0, #Hp0, #Hpi⟩
  · ipureintro; exact Hlgnn
  -- the scheduler's stop token goes to the closer (`storeCloser`, D19m (C), 2026-10-18): the
  -- caller gives it up when the store will not be closed (until then given up here)
  (try wp_auto)
  wp_apply chan.wp_make1 (V := Unit) as %stopc %γstop ⟨#Hstc, %Hstcap, Hstown⟩
  imod dghostVar_update stopc γx _ $$ Hx with Hx
  imod dghostVar_persist γx 1 stopc $$ Hx with #Hx
  (try wp_auto)
  iStructNamed «$r0»
  wp_apply hHash as %hp #Hhs
  · ipureintro; exact Hlgnn
  (try wp_auto)
  wp_alloc rv as Hrv
  (try wp_auto)
  wp_alloc wv as Hwv
  (try wp_auto)
  -- `s.le.SetRangeDeleter(...)`: the lessor is not nil
  ihave #Hlessor0 : mvcc.isLessor le γl $$ []
  · iexact Hlessor
  iunfold mvcc.isLessor at Hlessor
  icases Hlessor with ⟨%lp, %Hli, -, -, -, -, #HSetRD⟩
  subst Hli
  -- the store's variable, for good: the deleter closure reads it (`rdCalls`)
  ipersist s
  (try wp_auto)
  wp_apply HSetRD $$ [$Hro] as Hro
  (try wp_auto)
  -- the ghost state: the committed log at the image's `L'`, the revision budget's tokens of `L'`
  imod ghostVar_alloc (GF := GF) ([[], []] ++ R) with ⟨%γc, Hc⟩
  icases ghostVar_halves γc _ $$ Hc with ⟨Hc1, Hc2⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γr, Hauth⟩
  imod ownTokAuth_add (2 ^ 63 - 3 - ([[], []] ++ R).length) γr 0 $$ Hauth with ⟨Hauth, Htoks⟩
  rw [Nat.zero_add]
  icases (mvcc.ownTokAuth_halves γr _).1 $$ Hauth with ⟨Hauth, HauthR⟩
  -- the post-lock hook's names: the lock's invariant (the hook is the real backend's slot)
  imod (saved_prop_alloc (GF := GF) P DFrac.discard DFrac.valid_discard) with ⟨%γh, #Hh⟩
  imod ghostVar_alloc (GF := GF) () with ⟨%γhf, -⟩
  -- compaction's: the meta keys' record and the finished counter at the image's records
  imod ghostVar_alloc (GF := GF) ((r.sched, r.fin) : Option w64 × Option w64) with ⟨%γm, Hmeta⟩
  imod mono_nat_own_alloc (GF := GF) (mvcc.crevN (mvcc.finRev r.fin)) with ⟨%γfin, Hfin, -⟩
  -- the writer's: `s.mu`'s deposit ghost, the batch lock's key, the ghost of the view's log
  imod ghostVar_alloc (GF := GF) () with ⟨%γwr, Hwr⟩
  imod ghostVar_alloc (GF := GF) () with ⟨%γwk, Hwk⟩
  imod ghostVar_alloc (GF := GF) ([[], []] ++ R) with ⟨%γwv, Hwvg⟩
  icases ghostVar_halves γwv _ $$ Hwvg with ⟨Hwv1, Hwv2⟩
  imod ghostVar_alloc (GF := GF) true with ⟨%γmk, Hmk⟩
  -- the records' compaction revision, the job's cursor at the finished record and the lower bounds'
  -- authority at the records' revision
  imod ghostVar_alloc (GF := GF) r.crev with ⟨%γrcv, Hrcv⟩
  icases ghostVar_halves γrcv _ $$ Hrcv with ⟨Hrcv1, Hrcv2⟩
  imod ghostVar_alloc (GF := GF) ((r.finRev, (⟨W64 0, W64 0⟩ : mvcc.Rev)) : Int × mvcc.Rev)
    with ⟨%γjc, Hjc⟩
  icases ghostVar_halves γjc _ $$ Hjc with ⟨Hjc1, Hjc2⟩
  imod mono_nat_own_alloc (GF := GF) (mvcc.crevN r.crev) with ⟨%γrcl, Hrcl, -⟩
  -- the store's current objects and physical names
  imod (dghostVar_alloc (GF := GF) (((⟨b, ti, sc, stopc⟩ : mvcc.StoreObjs),
      (⟨γi.nev, γi.cmp, γb, γh, γhf, some d, γm, γfin, γs, γwk, γwv, γmk, γx, γrcv, γjc, γrcl⟩ :
        mvcc.PhysNames)) : mvcc.StoreObjs × mvcc.PhysNames)) with ⟨%γcur, Hcur1⟩
  imod (dghostVar_alloc (GF := GF) false) with ⟨%γrst, Hrst⟩
  icases ((dghostVar_fractional (GF := GF) γrst false).fractional (1 : Qp).half (1 : Qp).half).1
    $$ [Hrst] with ⟨HrstF, HrstR⟩
  · rw [Qp.half_add_half]; iexact Hrst
  imod ownTokAuth_alloc (GF := GF) with ⟨%γtk, Htka⟩
  imod ownTokAuth_add (mvcc.nReaders - mvcc.nJobRd (some d)) γtk 0 $$ Htka with ⟨Htka, Htks⟩
  rw [Nat.zero_add]
  imod ownTokAuth_alloc (GF := GF) with ⟨%γtko, Htkoa⟩
  imod ghostVar_alloc (GF := GF) () with ⟨%γwsd, Hwsd⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γtkw, Htkwa⟩
  imod ghostVar_alloc (GF := GF) (mvcc.nJobRd (some d)) with ⟨%γtkr, Htkr0⟩
  icases ghostVar_halves γtkr _ $$ Htkr0 with ⟨Htkra, Hret0⟩
  imod mvcc.crevPermIs_alloc Perm with ⟨%γcp, #Hcp⟩
  -- the API's ghost names at the image's log and compaction revision
  obtain ⟨pr, hpr⟩ := mvcc.pndW_compl wq
  imod (mvcc.api.absNames_alloc_store (GF := GF) ([[], []] ++ R) r.crev _ pr hpr «$r0_ptr»)
    with ⟨%γa, HXa, HYa, HFla, HCa, HCp, HCc1, HCc4, #HClb, HCt, HCn, #HCl0, HwY, HwM, HCrdk⟩
  obtain ⟨γ, hγi, hγb, hγc, hγl, hγr, hγh, hγhf, hγk, hγm, hγfin, hγs, hγok, hγw, hγwr, hγwk,
      hγwv, hγcur, hγrst, hγtk, hγtko, hγwsd, hγtkw, hγtkr, hγmk, hγcm, hγsx, hγcp, hγapi, hγrcv,
      hγjc, hγrcl⟩ :
      ∃ γ : mvcc.StoreNames,
      γ.idx = γi ∧ γ.bucket = γb ∧ γ.clog = γc ∧ γ.leases = γl ∧ γ.revs = γr ∧ γ.hook = γh ∧
      γ.hookFn = γhf ∧ γ.kb = some d ∧ γ.cmeta = γm ∧ γ.fin = γfin ∧ γ.sch = γs ∧ γ.cok = γok ∧
      γ.watchQ = wq ∧ γ.wr = γwr ∧ γ.wk = γwk ∧ γ.wv = γwv ∧ γ.cur = γcur ∧ γ.rst = γrst ∧
      γ.tk = γtk ∧ γ.tko = γtko ∧ γ.wsd = γwsd ∧ γ.tkw = γtkw ∧ γ.tkr = γtkr ∧ γ.mwk = γmk ∧
      γ.cm = d.cm ∧ γ.sx = γx ∧ γ.cperm = γcp ∧ γ.api = γa ∧ γ.rcv = γrcv ∧
      γ.jc = γjc ∧ γ.rcl = γrcl :=
    ⟨⟨γi, γb, γc, γl, γr, γh, γhf, some d, γm, γfin, γs, γok, wq, γwr, γwk, γwv, γcur, γrst, γtk,
        γtko, γwsd, γtkw, γtkr, γmk, d.cm, γx, γcp, γa, γrcv, γjc, γrcl⟩,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hkγ : γ.kb = some d := hγk
  have hcmγ : mvcc.kbCmpM γ.kb ↔ d.cm = true := by rw [hγk]; simp [mvcc.kbCmpM]
  ihave #HcpIs : mvcc.crevPermIs γ Perm $$ []
  · iunfold mvcc.crevPermIs; rw [hγcp]; iexact Hcp
  rw [← hγrst] at *
  rw [← hγtk, ← hγtko, ← hγtkw, ← hγtkr]
  ihave Hwsd : mvcc.wsDep γ $$ [Hwsd]
  · iunfold mvcc.wsDep; rw [hγwsd]; iexact Hwsd
  rw [← hγwr] at *
  rw [← hγwk] at *
  rw [← hγwv] at *
  ihave Hcur1 : ∃ v : mvcc.StoreObjs × mvcc.PhysNames, dghostVar (GF := GF) γ.cur (DFrac.own 1) v
      $$ [Hcur1]
  · iexists _; rw [hγcur]; iexact Hcur1
  icases Hcur1 with ⟨%v0, Hcur1⟩
  imod dghostVar_update (((⟨b, ti, sc, stopc⟩ : mvcc.StoreObjs), γ.phys) :
    mvcc.StoreObjs × mvcc.PhysNames) γ.cur _ $$ Hcur1 with Hcur1
  ihave Hcur1 : mvcc.curAt γ (DFrac.own 1) ⟨b, ti, sc, stopc⟩ $$ [Hcur1]
  · iunfold mvcc.curAt; iexact Hcur1
  icases (mvcc.curAt_halves γ 1 _).1 $$ Hcur1 with ⟨HcurF, HcurR⟩
  icases (mvcc.curAt_halves γ _ _).1 $$ HcurR with ⟨HcurR1, HcurR2⟩
  icases (mvcc.curAt_halves γ _ _).1 $$ HcurR1 with ⟨HcurRev, HcurWi⟩
  icases (mvcc.curAt_halves γ _ _).1 $$ HcurR2 with ⟨HcurPool, HcurFrag⟩
  ihave #HhookP : mvcc.hookP γ P $$ []
  · iunfold mvcc.hookP; rw [hγh]; iexact Hh
  ihave Hmk : ghostVar (GF := GF) γ.mwk 1 true $$ [Hmk]
  · rw [hγmk]; iexact Hmk
  icases mvcc.mwSlot_alloc γ $$ Hmk with ⟨Hslot, Hmrest⟩
  rw [← hγrcv, ← hγjc, ← hγrcl] at *
  ihave #HisSched' : schedule.isFifo sc γ.sch $$ []
  · rw [hγs]; iexact HisFifo
  rw [← hγi, ← hγc, ← hγr]
  -- the image's view: half for `restore` (clean), a quarter for the writer's pin, an eighth each for
  -- the batch lock's resource and the compaction's part
  icases mvcc.kbViewC_halves _ _ _ $$ Hview with ⟨HviewR, HviewW⟩
  ihave HviewR : mvcc.bucketViewC (GF := GF) γ (1 : Qp).half (mvcc.bucketOfEnts ents) $$ [HviewR]
  · iunfold mvcc.bucketViewC; rw [hγk, hγb]; iexact HviewR
  ihave HviewW : mvcc.bucketView (GF := GF) γ (1 : Qp).half (mvcc.bucketOfEnts ents) $$ [HviewW]
  · iapply mvcc.bucketViewC_bucketView
    iunfold mvcc.bucketViewC; rw [hγk, hγb]; iexact HviewW
  icases (mvcc.bucketView_quarters _ _).1 $$ HviewW with ⟨HviewW, HviewP⟩
  icases (mvcc.bucketView_halves _ (1 : Qp).half.half _).1 $$ HviewW with ⟨HviewW, HviewC⟩
  -- the tracked compaction at the image's records
  icases mvcc.cmpTrack_image γ d hkγ _ hlb r ents hrec hpos hcut $$ [Hvals Hrcv2 Hjc2 Hrcl]
    with ⟨HtrC, HvalsL⟩
  · iframe Hvals Hrcv2 Hjc2 Hrcl
  ihave Hcres : mvcc.compactRes γ ([[], []] ++ R) $$ [Hmeta Hfin Hslot HviewC HtrC]
  · iunfold mvcc.compactRes
    iexists r.sched, r.fin, mvcc.crevN (mvcc.finRev r.fin), mvcc.bucketOfEnts ents
    iunfold mvcc.metaCompact
    rw [hγm, hγfin]
    iframe Hmeta Hfin Hslot HviewC HtrC
    ipureintro; exact Nat.le_refl _
  -- the compaction revision's authority: half the compaction right's, a quarter for each lock
  icases (mvcc.crevUB_split γ.idx (1 : Qp).half (1 : Qp).half r.crev).1 $$ [Hcu] with ⟨Hright, Hcu⟩
  · rw [Qp.half_add_half]; iexact Hcu
  icases (mvcc.crevUB_split γ.idx (1 : Qp).half.half (1 : Qp).half.half r.crev).1 $$ [Hcu]
    with ⟨HcuM, HcuR⟩
  · rw [Qp.half_add_half]; iexact Hcu
  -- the stop channel
  imod alloc_broadcast_chan (E := ⊤) iprop(True) γstop stopc $$ Hstc Hstown with Hstop
  ihave #Hstop0 := ownBroadcastChan_Unknown _ _ _ _ $$ Hstop
  -- the fixed fields, and the views' `kv`
  iStructNamedPrefix Hrv "R"
  iStructNamedPrefix Hwv "W"
  ipersist le
  ipersist lg
  ipersist Rkv
  ipersist Wkv
  ipersist cfg
  ipersist hashes
  -- `tx := s.b.BatchTx()`: the session's contract at the store's names (no registration)
  ihave #Hsess : mvcc.storeSessT b «$r0_ptr» γ P $$ []
  · iapply HbkS $$ %«$r0_ptr» %γ
    ipureintro; exact ⟨hγb, hγk, rfl⟩
  icases mvcc.storeSessT_session b «$r0_ptr» γ P $$ Hsess with ⟨%bi, %Hbi, #HB, #HForce⟩
  subst Hbi
  (try wp_auto)
  wp_apply HB as %bt ⟨%LockedO, #Hinit⟩
  (try wp_auto)
  iunfold mvcc.batchTxInitSpec at Hinit
  icases Hinit with ⟨#HLockOut, #HCreate, #HUnlock0⟩
  -- the backend's tokens at the store's names
  ihave Hrts : [∗list] _x ∈ List.replicate mvcc.nReaders (), mvcc.storeRT (GF := GF) γ $$ [Hrts]
  · unfold mvcc.storeRT; rw [hγk]; iexact Hrts
  ihave Hwt1 : mvcc.storeWT (GF := GF) γ $$ [Hwt1]
  · unfold mvcc.storeWT; rw [hγk]; iexact Hwt1
  ihave Hwt2 : mvcc.storeWT (GF := GF) γ $$ [Hwt2]
  · unfold mvcc.storeWT; rw [hγk]; iexact Hwt2
  -- `tx.LockOutsideApply()`, the buckets created
  icases mvcc.nsr_slot_take _ $$ Hrts with ⟨Hrt1, Hrts⟩
  wp_bind (App (Val #(methods bt.ty _ bt.v)) (Val #()))
  iapply HLockOut $$ [Hrt1 Hwt1]
  · iframe Hrt1 Hwt1
  inext
  iintro ⟨Hlocked, HWi, HP, Hrt1⟩
  (try wp_auto)
  wp_bind (App (Val #(methods bt.ty _ bt.v)) (Val #bK))
  iapply HCreate $$ %0 %bK [Hlocked]
  · iframe Hlocked
    isplitr
    · ipureintro; omega
    ileft; iexact HKeyG
  inext
  iintro Hlocked
  (try wp_auto)
  wp_bind (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.UnsafeCreateMetaBucket))
    (Val #(GoInterface.ok bt)))
  iapply (hMeta bt (LockedO (0 + 1)) (LockedO (0 + 1 + 1))) $$ [Hlocked]
  · iframe Hlocked
    isplitr
    · iPkgInit
    imodintro
    iintro %b' !> %Φ' ⟨Hl, #HM⟩ HΦ'
    iapply HCreate $$ %(0 + 1) %b' %Φ' [Hl] HΦ'
    iframe Hl
    isplitr
    · ipureintro; omega
    iright; iexact HM
  inext
  iintro Hlocked
  (try wp_auto)
  -- `tx.Unlock()`: (B3) the lock's initial resource back, unregistered (the registration stays
  -- pending, `writerReg_allocP` after `restore()`, as `store.Restore`)
  ihave HW := mvcc.NewStore.sess_W_of_Wi «$r0_ptr» γ d hkγ $$ HWi
  wp_bind (App (Val #(methods bt.ty _ bt.v)) (Val #()))
  iapply HUnlock0 $$ %(0 + 1 + 1) [Hlocked HW HP]
  · iframe Hlocked HW HP
  inext
  iintro -
  (try wp_auto)
  -- `s.b.ForceCommit()`
  ihave #Hrq0 := mvcc.storeReq_true (GF := GF) γ
  wp_apply HForce $$ %iprop(True) %iprop(True) [$Hrt1 $Hwt2] as ⟨Hrt1, -⟩
  · iframe #
  ispecialize Hrts $$ Hrt1
  (try wp_auto)
  -- `s.mu.Lock()` on private memory, made a lock at once from the write-locked memory (B3: the
  -- resumed compaction inside `restore()` needs the store)
  wp_apply (plain.wp_Lock sync.atomic.Int32.wp_Add (mvcc.muAddr «$r0_ptr»)) $$ [$mu] as mu
  imod init_RWMutex_wlocked (mvcc.muInv «$r0_ptr» γ) (E := ⊤) (mvcc.muAddr «$r0_ptr») $$ mu
    with ⟨HmuW, Hmus⟩
  icases sync.ownRWMutex_slots_guard _ _ $$ Hmus with ⟨Hmus, #Hmug⟩
  (try wp_auto)
  sorry

end proof

end EtcdGrove
end Perennial
