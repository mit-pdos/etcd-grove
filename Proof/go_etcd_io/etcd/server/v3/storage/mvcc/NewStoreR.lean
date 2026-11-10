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
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.NewStorePool

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

/-! ### `NewStore`'s private `s.revMu` rounds inside `restore()`, and what the store is after it -/

/-- `restore()`'s first round's start: `s.revMu` unlocked, the lock's halves of the counters. -/
def mvcc.nsRevP0 (s : Loc) : IProp GF :=
  iprop(s.[store, go!"revMu"] ↦ (zero_val sync.RWMutex) ∗
    s.[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half} (W64 1 : w64) ∗
    s.[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half} (W64 (-1) : w64))

/-- After the first round: `compactMainRev` at the finished record. -/
def mvcc.nsRevP (s : Loc) (r : mvcc.CmpRecs) : IProp GF :=
  iprop(s.[store, go!"revMu"] ↦ (zero_val sync.RWMutex) ∗
    s.[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half} (W64 1 : w64) ∗
    s.[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half} (r.fin.getD (W64 (-1))))

/-- The second round, locked. -/
def mvcc.nsRevK (s : Loc) (r : mvcc.CmpRecs) : IProp GF :=
  iprop(s.[store, go!"revMu"] ↦ rwW ∗
    s.[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half} (r.fin.getD (W64 (-1))))

/-- What `restore()` returns its second round's unlock with (`V` of `revUnlockW`). -/
def mvcc.nsRevV (γ : mvcc.StoreNames) (L : mvcc.Log) (ents : List mvcc.KvEnt) (ti : Loc) : IProp GF :=
  iprop(mvcc.bucketViewC γ (1 : Qp).half (mvcc.bucketOfEnts ents) ∗ mvcc.isTreeIndex ti γ.idx ∗
    ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
      mvcc.idxReader ti γ.idx) ∗ ⧖ (mvcc.logCh L))

/-- After the second round: unlocked, `currentRev`'s lock half at the restored log, with `V`. -/
def mvcc.nsRevQ (s : Loc) (γ : mvcc.StoreNames) (r : mvcc.CmpRecs) (L : mvcc.Log)
    (ents : List mvcc.KvEnt) (ti : Loc) : IProp GF :=
  iprop(s.[store, go!"revMu"] ↦ (zero_val sync.RWMutex) ∗
    s.[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half} (W64 ((L.length : Int) - 1) : w64) ∗
    s.[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half} (r.fin.getD (W64 (-1))) ∗
    mvcc.nsRevV γ L ents ti)

/-- **The store once `restore()` has read the image** (before the compaction it may resume): the
store, `s.mu`'s resource with the compaction revision's lag, the right by the mode, the shares, the
reader slots of `s.revMu`, the restored log's certificate, the registration, the lent reader token
(with its index slot, to go back in the pool), and the lag's part of the watchable deposit. -/
def mvcc.nsReady (s : Loc) (γ : mvcc.StoreNames) (d : mvcc.KBReal) (r : mvcc.CmpRecs)
    (L : mvcc.Log) (ti : Loc) : IProp GF :=
  iprop(mvcc.isStore s γ ∗ mvcc.muInvLag s γ r.crev r.finRev ∗ ghostVar γ.wr 1 () ∗
    mvcc.fieldShare s γ (1 : Qp).half ∗ mvcc.storeCloserM s γ r.crev ∗
    (if d.cm then iprop(True) else mvcc.crevUB γ.idx (1 : Qp).half (-1)) ∗
    mvcc.fieldShare s γ (1 : Qp).half.half ∗
    ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
      sync.ownRWMutex (mvcc.revMuAddr s) (mvcc.revMuInv s γ)) ∗
    mvcc.idxCert γ.idx L ∗ (if γ.watchQ then mvcc.logQ γ L else iprop(True)) ∗
    mvcc.writerReg s γ ∗ mvcc.storeRT γ ∗ mvcc.idxReader ti γ.idx ∗ mvcc.crevPermAt γ r.crev ∗
    (if r.finRev = r.crev then ghostVar γ.wsd (1 : Qp).half.half () else iprop(True)))

/-- **The store when `restore()` returns**: `s.mu`'s resource (for the deferred unlock), the right
by the mode, the shares, `s.revMu`'s slots, the certificate, the registration, the lent token with
its index slot, the lag's part of the watchable deposit, the share token and the resumed
compaction's results. -/
def mvcc.nsFin (s : Loc) (γ : mvcc.StoreNames) (d : mvcc.KBReal) (r : mvcc.CmpRecs)
    (L : mvcc.Log) (ti : Loc) (hk : Option val) (dq : DFrac) (Post Y : IProp GF) : IProp GF :=
  iprop(mvcc.isStore s γ ∗ mvcc.muInv s γ 1 ∗ mvcc.storeCloserM s γ r.crev ∗
    (if d.cm then iprop(True) else mvcc.crevUB γ.idx (1 : Qp).half (-1)) ∗
    mvcc.fieldShare s γ (1 : Qp).half.half ∗
    ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
      sync.ownRWMutex (mvcc.revMuAddr s) (mvcc.revMuInv s γ)) ∗
    mvcc.idxCert γ.idx L ∗ (if γ.watchQ then mvcc.logQ γ L else iprop(True)) ∗
    mvcc.writerReg s γ ∗ mvcc.storeRT γ ∗ mvcc.idxReader ti γ.idx ∗
    ghostVar γ.wsd (1 : Qp).half.half () ∗ mvcc.slotFr γ ∗ mvcc.resumeBackM d r hk dq Post Y)

/-- A token back. -/
theorem mvcc.nsr_ownToks_back (γ : GName) (n : Nat) (h : 1 ≤ n) :
    ownToks (GF := GF) γ (n - 1) ∗ ownToks γ 1 ⊢ ownToks γ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact (ownToks_add 1 m γ).2

/-- The certificate of a restored log certifies the initial log (`isStore`'s). -/
theorem mvcc.nsr_idxCert_init (γ : mvcc.IdxNames) (R : mvcc.Log) :
    mvcc.idxCert (GF := GF) γ ([[], []] ++ R) ⊢ mvcc.idxCert γ [[], []] := by
  have hp : ([[], []] : mvcc.Log) <+: [[], []] ++ R := List.prefix_append _ _
  have hwf2 : mvcc.LogWf' ([[], []] : mvcc.Log) := by
    refine ⟨fun _ => rfl, fun rv cs i k hr hi => ?_⟩
    have hcs : cs = [] := by
      match rv, hr with
      | 0, hr => simpa using hr.symm
      | 1, hr => simpa using hr.symm
      | n + 2, hr => simp at hr
    subst hcs; simp at hi
  unfold mvcc.idxCert
  iintro ⟨#Hh, -, #Hl, #Hr⟩
  isplitl []
  · iapply monoListLbOwn_le _ (mvcc.histOf_mono hp) $$ Hh
  isplitl []
  · ipureintro
    refine ⟨hwf2, by decide, ?_⟩
    intro cs hcs; simp at hcs; subst hcs; decide
  isplitl []
  · iapply monoListLbOwn_le _ hp $$ Hl
  iapply preceipt_mono (by simp [mvcc.logCh]) $$ Hr

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
  wp_auto_lc 2
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
  -- (B3) the tickets of every slot but the one `restore()` lends its compaction: counted retired
  -- until it is back (`readerPool_unretire`)
  imod ownTokAuth_add (mvcc.nReaders - mvcc.nJobRd (some d) - 1) γtk 0 $$ Htka with ⟨Htka, Htks⟩
  rw [Nat.zero_add]
  imod ownTokAuth_alloc (GF := GF) with ⟨%γtko, Htkoa⟩
  imod ghostVar_alloc (GF := GF) () with ⟨%γwsd, Hwsd⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γtkw, Htkwa⟩
  imod ghostVar_alloc (GF := GF) (mvcc.nJobRd (some d) + 1) with ⟨%γtkr, Htkr0⟩
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
  -- `currentRev` and `compactMainRev`: half each for `restore` itself, half for its rounds
  icases (mvcc.typedPointsto_parts _ _ (1 : Qp).half (1 : Qp).half (Qp.half_add_half 1)).1
    $$ currentRev with ⟨HcurA, HcurB⟩
  icases (mvcc.typedPointsto_parts _ _ (1 : Qp).half (1 : Qp).half (Qp.half_add_half 1)).1
    $$ compactMainRev with ⟨HcmA, HcmB⟩
  -- `restore()`'s rounds of `s.revMu`, on private memory
  ihave HP0 : mvcc.nsRevP0 (GF := GF) «$r0_ptr» $$ [revMu HcurB HcmB]
  · iunfold mvcc.nsRevP0; iframe revMu HcurB HcmB
  ihave HFw : mvcc.revFinW (GF := GF) «$r0_ptr» (DFrac.own (1 : Qp).half) r.fin
      (mvcc.nsRevP0 «$r0_ptr») (mvcc.nsRevP «$r0_ptr» r) $$ []
  · iunfold mvcc.revFinW
    cases hf : r.fin with
    | none =>
      iintro H
      iunfold mvcc.nsRevP0 at H
      iunfold mvcc.nsRevP
      simp only [hf, Option.getD_none]
      iexact H
    | some x =>
      iexists iprop(«$r0_ptr».[store, go!"revMu"] ↦ rwW ∗
        «$r0_ptr».[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half} (W64 1 : w64))
      isplitl []
      · iintro %Ψ H HΨ
        iunfold mvcc.nsRevP0 at H
        icases H with ⟨HrevMu, Hc, Hcm⟩
        wp_apply (plain.wp_Lock sync.atomic.Int32.wp_Add _) $$ [$HrevMu] as HrevMu
        iapply HΨ $$ %_ Hcm [HrevMu Hc]
        iframe HrevMu Hc
      · iintro %Ψ Hcm ⟨HrevMu, Hc⟩ HΨ
        wp_apply (plain.wp_Unlock sync.atomic.Int32.wp_Add _) $$ [$HrevMu] as HrevMu
        iapply HΨ
        iunfold mvcc.nsRevP
        simp only [hf, Option.getD_some]
        iframe HrevMu Hc Hcm
  ihave HLk : mvcc.revLockW (GF := GF) «$r0_ptr» (1 : Qp).half (mvcc.nsRevP «$r0_ptr» r)
      (mvcc.nsRevK «$r0_ptr» r) $$ []
  · iunfold mvcc.revLockW
    iintro %Ψ H HΨ
    iunfold mvcc.nsRevP at H
    icases H with ⟨HrevMu, Hc, Hcm⟩
    wp_apply (plain.wp_Lock sync.atomic.Int32.wp_Add _) $$ [$HrevMu] as HrevMu
    iapply HΨ $$ %_ Hc [HrevMu Hcm]
    iunfold mvcc.nsRevK
    iframe HrevMu Hcm
  ihave HUl : mvcc.revUnlockW (GF := GF) «$r0_ptr» (1 : Qp).half ([[], []] ++ R)
      (mvcc.nsRevK «$r0_ptr» r)
      iprop(mvcc.bucketViewC γ (1 : Qp).half (mvcc.bucketOfEnts ents) ∗ mvcc.isTreeIndex ti γ.idx ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          mvcc.idxReader ti γ.idx) ∗ ⧖ (mvcc.logCh ([[], []] ++ R)))
      (mvcc.nsRevQ «$r0_ptr» γ r ([[], []] ++ R) ents ti) $$ []
  · iunfold mvcc.revUnlockW
    iintro %Ψ Hc HK Hv HΨ
    iunfold mvcc.nsRevK at HK
    icases HK with ⟨HrevMu, Hcm⟩
    wp_apply (plain.wp_Unlock sync.atomic.Int32.wp_Add _) $$ [$HrevMu] as HrevMu
    iapply HΨ
    iunfold mvcc.nsRevQ
    iunfold mvcc.nsRevV
    iframe HrevMu Hc Hcm Hv
  -- the clean read and the reader's token, lent with the unfixed registration
  ihave #HcrT' : mvcc.keyCleanReadR (GF := GF) (GoInterface.ok bi) (mvcc.bucketViewC γ)
      iprop(mvcc.storeRT γ ∗ mvcc.restoreRegM d) (mvcc.kbRecs γ.kb γ.bucket r) r $$ []
  · iapply HcrT
    ipureintro; exact ⟨hγb, hγk, rfl⟩
  icases mvcc.nsr_slot_take _ $$ Hrts with ⟨Hrt1, Hrts⟩
  ihave Hnc : mvcc.kbRecs (GF := GF) γ.kb γ.bucket r $$ [Hnc]
  · rw [hγk, hγb]; iexact Hnc
  -- the watchable store's deposit: half and a quarter kept, a quarter for the compaction's lag
  iunfold mvcc.wsDep at Hwsd
  have hw := (ghostVar_fractional (GF := GF) γ.wsd ()).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hw
  icases hw.1 $$ Hwsd with ⟨HwsdS, Hwsd2⟩
  have hw2 := (ghostVar_fractional (GF := GF) γ.wsd ()).fractional (1 : Qp).half.half
    (1 : Qp).half.half
  rw [Qp.half_add_half] at hw2
  icases hw2.1 $$ Hwsd2 with ⟨HwsdL, HwsdK⟩
  -- (B3) the store once `restore()` has read the image
  ihave Hready : mvcc.restoreDone (GF := GF) «$r0_ptr» (GoInterface.ok bi) ti (1 : Qp).half
      (DFrac.own 1) (DFrac.own 1) (DFrac.own (1 : Qp).half) ([[], []] ++ R) ents r
      iprop(mvcc.storeRT γ ∗ mvcc.restoreRegM d) (mvcc.kbRecs γ.kb γ.bucket r)
      (mvcc.nsRevQ «$r0_ptr» γ r ([[], []] ++ R) ents ti) -∗
      |={⊤}=> mvcc.nsReady «$r0_ptr» γ d r ([[], []] ++ R) ti $$ []
  · sorry
  -- the resume: `compactLockfree` at the scheduled record, else nothing
  ihave HK : mvcc.resumeK (GF := GF) «$r0_ptr» r (mvcc.restoreDone «$r0_ptr» (GoInterface.ok bi) ti
      (1 : Qp).half (DFrac.own 1) (DFrac.own 1) (DFrac.own (1 : Qp).half) ([[], []] ++ R) ents r
      iprop(mvcc.storeRT γ ∗ mvcc.restoreRegM d) (mvcc.kbRecs γ.kb γ.bucket r)
      (mvcc.nsRevQ «$r0_ptr» γ r ([[], []] ++ R) ents ti))
      iprop(|={⊤}=> mvcc.nsFin «$r0_ptr» γ d r ([[], []] ++ R) ti hkH dqh PostH YH) $$ [Hready]
  · sorry
  have hdq : ∀ x, r.fin = some x →
      DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half = DFrac.own 1 := by
    intro _ _; rw [DFrac.op_own, Qp.half_add_half]
  -- `s.restore()`
  have hR' := hRestore «$r0_ptr» γ (GoInterface.ok bi) (lease.lessorIface lp) ti lg' (1 : Qp).half P
      (mvcc.hookFn γ) iprop(mvcc.storeRT γ ∗ mvcc.restoreRegM d) (mvcc.storeWT γ)
      (mvcc.storeW «$r0_ptr» γ) (mvcc.kbWi γ.kb) iprop(True) (mvcc.kbRecs γ.kb γ.bucket r)
      (mvcc.storeCmp γ) (mvcc.storePutOk γ) (mvcc.storeRb γ) (mvcc.storeBt γ)
      (mvcc.kbMWv γ.kb γ.bucket) (mvcc.kbSR γ.kb) (mvcc.kbSRh γ.kb) (DFrac.own 1) (DFrac.own 1) R
      (mvcc.nsRevP0 «$r0_ptr») (mvcc.nsRevP «$r0_ptr» r) (mvcc.nsRevK «$r0_ptr» r)
      (mvcc.nsRevQ «$r0_ptr» γ r ([[], []] ++ R) ents ti)
      (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half) (1 : Qp).half (1 : Qp).half r ents
      iprop(|={⊤}=> mvcc.nsFin «$r0_ptr» γ d r ([[], []] ++ R) ti hkH dqh PostH YH) false γl Ls
      hR (Qp.half_add_half 1) hrec (fun h => absurd h (by decide)) hdq hcut
  simp only [Bool.false_eq_true, ↓reduceIte] at hR'
  ihave HviewR := mvcc.storeSess_restoreView _ γ d _ _ r $$ [$HviewR $HcrT']
  ihave Hdisj : iprop(⌜ents = mvcc.logEnts ([[], []] ++ R) 0 ([[], []] ++ R).length⌝ ∨
      ⧖ (mvcc.logCh ([[], []] ++ R))) $$ []
  · cases hcm : d.cm
    · ileft; ipureintro; exact (hoff hcm).2
    · iright; iapply (mvcc.restoreRcptM_on d _ hcm).1 $$ Hrc0
  wp_apply hR' $$ [$b $Hrt1 $Hreg $Hnc $HviewR $kvindex $Hix $Hig $Hiwlb $HcurA $HcmA $HP0 $HFw $HLk
      $HUl $HK $Hdisj $Hlown] as ⟨HFin, HLo⟩
  · iframe #
    ipureintro; exact ⟨Hlgnn, Hlok⟩
  imod HFin with HFin
  iunfold mvcc.nsFin at HFin
  icases HFin with ⟨#Hs, HmuI, Hright, Hcrf, Hfw, Hrevs, #Hcert, HlogQ, #HrgI, Hrt1, Hird1, HwsdL, HCt,
    HrB⟩
  -- the lent reader's slot back in the pool, the retired count at the job's
  ihave #Hs' := Hs
  iunfold mvcc.isStore at Hs'
  iNamed Hs'
  imod mvcc.readerPool_unretire γ _ _ (mvcc.nJobRd (some d)) $$ Hlc2 Hpool HcurFrag [Hird1 Hrt1]
    [Hret0] with ⟨Htk1, Hret0, HcurFrag⟩
  · iunfold mvcc.idxSlot; iframe Hird1 Hrt1
  · iunfold mvcc.retiredAt; rw [hγtkr]; iexact Hret0
  -- the deferred `s.mu.Unlock()`, with `s.mu`'s resource
  wp_apply +noauto sync.RWMutex.wp_Unlock_guard $$ [$HmuW HmuI]
  · iframe #; inext; iexact HmuI
  (try wp_auto)
  iapply HΦ
  iexists γ
  isplitr
  · ipureintro; refine ⟨hγb, hγl, hγk, hγw, ?_, ?_, hγcm⟩ <;> first | rfl | assumption
  iframe Hs Hcert HhookP HcpIs HrgI Hlc1 Hright Hcrf Hfw HLo HrB
  isplitl [Hro]
  · iexists _; iframe Hro
    iunfold mvcc.rdCalls
    isplitr
    · ipureintro; intro h; injection h with _ _ h3; cases h3
    iintro !> %Pre' %Ψ %hTODO #Hw %Φ' !> HPre HΦ'
    ihave #Htpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
    · iPkgInit
    wp_auto
    wp_apply hTODO as %tr ⟨%Htrnn, Htr⟩
    wp_apply Hw $$ [$HPre $Htr] as %t Ht
    · ipureintro; exact Htrnn
    (try wp_auto)
    iapply HΦ'; iexact Ht
  isplitl [Hok]
  · rw [hγok]; iexact Hok
  isplitl [ReadView WriteView]
  · iexists rv, wv
    iunfold mvcc.isReadView
    iunfold mvcc.isWriteView
    simp only [named]
    iframe ReadView WriteView
    iframe #
    iunfold mvcc.kvOver; ileft; ipureintro; rfl
  have hjr' : mvcc.nJobRd (some d) ≤ mvcc.nReaders := by omega
  ihave Hmus := mvcc.rep_nReaders _ $$ Hmus
  ihave Hrevs := mvcc.rep_nReaders _ $$ Hrevs
  icases mvcc.rep_sub _ (mvcc.nJobRd (some d)) _ hjr' $$ Hmus with ⟨Hmus, -⟩
  icases mvcc.rep_sub _ (mvcc.nJobRd (some d)) _ hjr' $$ Hrevs with ⟨Hrevs, -⟩
  isplitl [Hmus Hrevs Htks Htk1]
  · iapply mvcc.nsr_storeReaders_of_slots «$r0_ptr» γ
    iframe Hmus Hrevs
    iapply mvcc.nsr_ownToks_ones
    iapply mvcc.nsr_ownToks_back γ.tk _ (by omega)
    iframe Htks Htk1
  isplitl [HlogQ]
  · rw [← hγw]; iexact HlogQ
  isplitl [HwsdS HwsdL HwsdK]
  · iunfold mvcc.wsDep
    iapply hw.2
    iframe HwsdS
    iapply hw2.2
    iframe HwsdL HwsdK
  isplitl [HcurFrag]
  · iunfold mvcc.writerFrag; iexists _; iexact HcurFrag
  isplitl [Hret0]
  · iexact Hret0
  iexists pr
  isplitr
  · ipureintro; unfold mvcc.pndW; rw [hγw]; exact hpr
  iunfold mvcc.slotFr at HCt
  rw [hγapi]
  iunfold mvcc.api.newClient
  iframe HCa HCp HCc1 HCc4 HClb HCt HCn HCl0 HCrdk

end proof

end EtcdGrove
end Perennial
