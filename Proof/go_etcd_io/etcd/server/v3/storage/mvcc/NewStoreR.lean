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

/-- A resource out of `n` copies. -/
theorem mvcc.nsr_rep_take1 (Q : IProp GF) (n : Nat) (h : 1 ≤ n) :
    ([∗list] _x ∈ List.replicate n (), Q) ⊢ Q ∗ [∗list] _x ∈ List.replicate (n - 1) (), Q := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, List.replicate_succ]
  exact BigSepL.bigSepL_cons.1

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
  icases mvcc.nsr_rep_take1 _ _ (by omega) $$ Hrts with ⟨Hrt1, Hrts⟩
  ihave #HpCr : mvcc.crevPermAt (GF := GF) γ r.crev $$ []
  · icases HpC with (%h | #Hp)
    · rw [h]; iapply mvcc.crevPermAt_none
    · iapply mvcc.crevPermAt_of γ Perm r.crev; iframe HcpIs Hp
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
      |={⊤}=> mvcc.nsReady «$r0_ptr» γ d r ([[], []] ++ R) ti
      $$ [HiwNR Hil Hc1 Hc2 Hauth HauthR Htoks Hwv1 Hwv2 Hwk HviewW HviewP Hcres Hrg Hmrest HvalsL HbkT
        Hlrd HYa HwY Hrcv1 HXa HFla HcurWi HcurRev HcurPool HcurF HrstF HrstR Htka Htkoa Htkwa Htkra
        Hrts fifoSched stopc HcuR HcuM Hright Hcmp0 Hjc1 Hsrm Hq0 HsStop Hstop Hwr HwM HwsdL]
  · iintro HD
    iunfold mvcc.restoreDone at HD
    icases HD with ⟨⟨Hrt, Hreg⟩, Hnc, -, HQ, HcurA, HcmA, Hfb, Hfidx⟩
    iunfold mvcc.nsRevQ at HQ
    icases HQ with ⟨HrevMu, HcurB, HcmB, HV⟩
    iunfold mvcc.nsRevV at HV
    icases HV with ⟨HvR, #Hti, Hird, #Hrc⟩
    ihave %Hrclt := preceipt_lt _ $$ Hrc
    have hsmall : ([[], []] ++ R).length + 3 ≤ 2 ^ 63 := by have := hlen.2; omega
    have hx : (W64 r.finRev : w64) = r.fin.getD (W64 (-1)) := by
      rw [← mvcc.CmpRecs.finRev_getD, mvcc.W64_sint']
    -- the restored log's certificate
    ihave #Hcert : mvcc.idxCert (GF := GF) γ.idx ([[], []] ++ R) $$ []
    · iunfold mvcc.idxWriterLb at Hiwlb
      icases Hiwlb with ⟨#Hhlb, -, -⟩
      iunfold mvcc.idxCert
      rw [← mvcc.histShape_nil]
      iframe Hhlb Hllb0 Hrc
      ipureintro
      exact ⟨hR.2.1.prefix, by have := hR.2.2.1; omega, hR.2.2.2.2⟩
    -- the backend's contract at the records, the registration fixed
    ihave Hw : (mvcc.restoreFixM d γ -∗ mvcc.storeBackendTR (GoInterface.ok bi) «$r0_ptr» γ P r)
        $$ [HbkT]
    · iapply HbkT; ipureintro; exact ⟨hγb, hγk, rfl⟩
    imod mvcc.storeSess_fix _ _ γ P d r $$ [$Hreg $Hw] with HbkR
    iunfold mvcc.storeBackendTR at HbkR
    ihave #HbkN := mvcc.isKeyBackendGR_ncFalse _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ $$ HbkR
    -- the writer's index handle with its receipt
    ihave Hiw : mvcc.idxWriter (GF := GF) γ.idx ([[], []] ++ R) [] $$ [HiwNR]
    · iapply (mvcc.idxWriter_split _ _ _).2
      iframe HiwNR
      simp only [List.length_nil, Nat.add_zero]
      iexact Hrc
    -- the writer's loan (off: the records are none, the no-compaction token) and, on, the records'
    -- write right
    ihave Hloan : mvcc.writerLoan (GF := GF) γ ∗
        (if mvcc.kbCmpM γ.kb then mvcc.kbMWf γ.kb γ.bucket else iprop(True)) $$ [Hnc HvalsL]
    · iunfold mvcc.writerLoan
      cases hcm : d.cm
      · have hnc : ¬ mvcc.kbCmpM γ.kb := fun h => by rw [hcmγ, hcm] at h; cases h
        obtain ⟨hre, -⟩ := hoff hcm
        subst hre
        simp only [hnc, ↓reduceIte]
        isplitl
        · isplitl
          · iapply (mvcc.kbNoCmp_split _ _).2
            rw [mvcc.kbRecs_empty] at *
            iframe Hnc
            rw [hγk]
            ihave Hv := HvalsL $$ []
            · ipureintro; first | exact hcm | rfl | trivial
            simp only [mvcc.CmpRecs.empty, mvcc.recBytes, Option.map_none] at *
            iexact Hv
          iapply (show mvcc.kbNoDelOff (GF := GF) γ.kb ⊢ mvcc.kbNoDel γ.kb from by
            unfold mvcc.kbNoDelOff; rw [if_neg hnc]) $$ [Hnd]
          rw [hγk]; iexact Hnd
        itrivial
      · have hon : mvcc.kbCmpM γ.kb := hcmγ.2 hcm
        simp only [hon, ↓reduceIte]
        isplitl []
        · itrivial
        iapply mvcc.kbRecs_MWf $$ Hnc
    icases Hloan with ⟨Hloan, Hmw⟩
    -- the writer's state at `L'`
    ihave Hrtk : mvcc.wrState (GF := GF) γ (2 ^ 63 - 3 - ([[], []] ++ R).length) ([[], []] ++ R)
        $$ [Htoks Hloan]
    · unfold mvcc.wrState
      iframe Hloan Htoks
      ipureintro; exact hlen.2
    ihave HY : mvcc.slotY γ ([[], []] ++ R) $$ [HYa Hrcv1 HwY]
    · unfold mvcc.slotY mvcc.pndW; rw [hγapi, hγw]
      iexists r.crev
      icases HYa with ⟨HYa1, HYa2⟩
      iframe HYa1 HYa2 HwY
      iapply mvcc.rcvW_intro; iexact Hrcv1
    ihave Hlrd : lease.lessorRdOf γ.leases $$ [Hlrd]
    · rw [hγl]; iexact Hlrd
    ihave HL : mvcc.writerL «$r0_ptr» γ $$ [Hauth Hiw Hc1 Hwv1 HcurA Hlrd HY Hrtk]
    · iunfold mvcc.writerL
      iexists ([[], []] ++ R), 2 ^ 63 - 3 - ([[], []] ++ R).length
      simp only [named]
      iframe Hauth Hiw Hc1 Hwv1 HcurA Hlrd HY Hrtk
      iframe #
      ipureintro
      exact ⟨by omega, by simp⟩
    -- the batch lock's resource at `L'`, its registration pending
    ihave HviewW := mvcc.bucketViewL_image γ d hkγ _ _ hlb r ents hcut hoff hcge $$ [HviewW]
    · iframe HviewW Hclbc Hcert
    ihave HviewP := mvcc.bucketViewL_image γ d hkγ _ _ hlb r ents hcut hoff hcge $$ [HviewP]
    · iframe HviewP Hclbc Hcert
    ihave HwPin : mvcc.wrPin (GF := GF) γ ([[], []] ++ R) $$ [HviewP]
    · iunfold mvcc.wrPin; iexact HviewP
    ihave HW : mvcc.writerRes «$r0_ptr» γ $$ [Hwk Hwv2 HviewW Hcres HwPin]
    · iunfold mvcc.writerRes
      iexists ([[], []] ++ R)
      simp only [named]
      iunfold mvcc.writerKey
      iframe Hwk Hwv2 HviewW Hcres HwPin
      iframe #
      ipureintro; simp
    ihave Hrg : mvcc.kbRegRight (GF := GF) γ.kb $$ [Hrg]
    · rw [hγk]; iexact Hrg
    imod mvcc.writerReg_allocP «$r0_ptr» γ ⊤ $$ [Hrg HW] with #HrgI
    · iframe Hrg HW
    -- the writer's invariant
    imod (inv_alloc mvcc.writerN ⊤ (mvcc.writerInvBody «$r0_ptr» γ))
      $$ [HL HcurWi HFla] with #Hwi
    · inext; iunfold mvcc.writerInvBody; ileft
      iexists γ.phys, _; rw [mvcc.StoreNames.withPhys_self]; iframe HcurWi; ileft
      isplitl [HFla]
      · unfold mvcc.slotFl; rw [hγapi]; iexact HFla
      ileft; iframe HL
      iexact HrgI
    ihave #Hwi : mvcc.writerInv «$r0_ptr» γ $$ []
    · iunfold mvcc.writerInv; iexact Hwi
    -- the readers' pool: every slot but the one lent to the compaction `restore()` resumes
    have hk1 : 1 ≤ mvcc.nReaders - mvcc.nJobRd (some d) := by omega
    ihave Hird := mvcc.rep_nReaders _ $$ Hird
    icases mvcc.rep_sub _ (mvcc.nJobRd (some d)) _ (by omega) $$ Hird with ⟨Hird, -⟩
    icases mvcc.nsr_rep_take1 _ _ hk1 $$ Hird with ⟨Hird1, Hird⟩
    icases mvcc.rep_sub _ (mvcc.nJobRd (some d)) _ (by omega) $$ Hrts with ⟨Hrts, HjRT⟩
    rw [show mvcc.nReaders - 1 - mvcc.nJobRd (some d) = mvcc.nReaders - mvcc.nJobRd (some d) - 1
      by omega]
    ihave Hslots := mvcc.idxSlots_of γ (⟨GoInterface.ok bi, ti, sc, stopc⟩ : mvcc.StoreObjs) _
      $$ [Hird Hrts]
    · iframe Hird Hrts
    imod (inv_alloc mvcc.poolN ⊤ iprop(∃ (p : mvcc.PhysNames) (o : mvcc.StoreObjs),
        mvcc.curAt (γ.withPhys p) (DFrac.own (1 : Qp).half.half.half) o ∗
          mvcc.poolBody (γ.withPhys p) o))
      $$ [Htka Htkoa Htkwa Htkra Hslots HcurPool] with #Hpool
    · inext
      iexists γ.phys, _
      rw [mvcc.StoreNames.withPhys_self]
      iframe HcurPool
      iunfold mvcc.poolBody
      iexists mvcc.nReaders - mvcc.nJobRd (some d) - 1, 0, 0, mvcc.nJobRd (some d) + 1
      rw [List.replicate_zero]
      iframe Htka Htkoa Htkwa Htkra Hslots
      isplitl []
      · iapply BigSepL.bigSepL_nil_intro; iempintro
      isplitl []
      · iapply BigSepL.bigSepL_nil_intro; iempintro
      ipureintro; omega
    ihave #Hpool : mvcc.readerPool γ $$ []
    · iunfold mvcc.readerPool; iexact Hpool
    -- `s.revMu` made a lock at the restored log, with the compaction revision's lag
    ihave Hsplit : mvcc.idxLogAuth γ.idx (mvcc.revQ γ 1) ([[], []] ++ R) ∗
        (if γ.watchQ then mvcc.logQ γ ([[], []] ++ R) else iprop(True)) $$ [Hil]
    · have hq := (monoListAuthOwn_fractional (GF := GF) γ.idx.log ([[], []] ++ R)).fractional
        (1 : Qp).half.half (1 : Qp).half.half
      rw [Qp.half_add_half] at hq
      cases hwq : γ.watchQ
      · simp only [mvcc.revQ, hwq, Bool.false_eq_true, ↓reduceIte]; iframe Hil
      · simp only [mvcc.revQ, mvcc.logQ, mvcc.idxLogAuth, hwq, ↓reduceIte]; iapply hq.1 $$ Hil
    icases Hsplit with ⟨Hil, HlogQ⟩
    ihave HvR : mvcc.bucketView (GF := GF) γ (1 : Qp).half (mvcc.bucketOfEnts ents) $$ [HvR]
    · iapply mvcc.bucketViewC_bucketView $$ HvR
    ihave HvR := mvcc.bucketViewL_image γ d hkγ _ _ hlb r ents hcut hoff hcge $$ [HvR]
    · iframe HvR Hclbc Hcert
    ihave Hlag : mvcc.revLag (GF := GF) γ 1 r.crev r.finRev ∗
        (if r.finRev = r.crev then ghostVar γ.wsd (1 : Qp).half.half () else iprop(True)) $$ [HwsdL]
    · iunfold mvcc.revLag
      by_cases hfc : r.finRev = r.crev
      · simp only [hfc, ↓reduceIte]
        iframe HwsdL
        ipureintro; exact ⟨⟨hcge, Int.le_refl _⟩, trivial⟩
      · simp only [hfc, ↓reduceIte]
        iframe HwsdL
        ipureintro; exact hfb
    icases Hlag with ⟨Hlag, Hlr⟩
    ihave HcmB : («$r0_ptr».[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half}
        (W64 r.finRev : w64) : IProp GF) $$ [HcmB]
    · rw [hx]; iexact HcmB
    have hevs : (mvcc.evsOf (([[], []] ++ R) ++ [[]])).length =
        (mvcc.evsOf ([[], []] ++ R)).length := by
      rw [mvcc.evsOf_append ([[], []] ++ R) []]; simp [mvcc.evsOfRev]
    ihave #Hnv : mvcc.idxNevLb (GF := GF) γ.idx ([[], []] ++ R) $$ []
    · iunfold mvcc.idxWriterLb at Hiwlb
      icases Hiwlb with ⟨-, #Hn, -⟩
      iunfold mvcc.idxNevLb
      rw [← hevs]; iexact Hn
    imod sync.init_RWMutex (mvcc.revMuInv «$r0_ptr» γ) (mvcc.revMuAddr «$r0_ptr»)
      $$ [HcurB Hc2 HvR HauthR Hil HcmB HcuR Hlag HXa HrstR HcurRev] HrevMu with Hrevs
    · inext
      iapply (mvcc.revMuInv_closeL «$r0_ptr» γ γ 1)
      isplitr [HrstR HcurRev]
      rotate_left
      · iunfold mvcc.revMuTok; iframe HrstR
        isplitl
        · iexists _; iexact HcurRev
        ipureintro; rw [mvcc.StoreNames.withPhys_self]
      iunfold mvcc.revMuBodyL
      iexists ([[], []] ++ R), 2 ^ 63 - 3 - ([[], []] ++ R).length, r.crev, r.finRev
      simp only [named]
      iframe HcurB Hc2 HvR HauthR Hil HcmB HcuR Hlag
      iframe #
      isplitl []
      · iunfold mvcc.certOk; rw [hγok]; iexact HokC
      isplitl []
      · ipureintro; simp
      isplitl []
      · ipureintro; omega
      isplitl []
      · ipureintro; exact ⟨hcge, hcl⟩
      unfold mvcc.slotX; rw [hγapi]; iexact HXa
    icases sync.ownRWMutex_slots_guard _ _ $$ Hrevs with ⟨Hrevs, #Hrevg⟩
    -- the write right's invariant and the registration (on); the objects' facts
    imod mvcc.physCmp_alloc «$r0_ptr» γ $$ [$Hmrest $Hmw $HrgI] with #HmwP
    ihave #Hpay : mvcc.stopPayAt γ.sx γ.sch (⟨GoInterface.ok bi, ti, sc, stopc⟩ : mvcc.StoreObjs) $$ []
    · iunfold mvcc.stopPayAt; rw [hγsx, hγs]; iframe Hx Hpi
    ihave #Hph : mvcc.physOk «$r0_ptr» γ (⟨GoInterface.ok bi, ti, sc, stopc⟩ : mvcc.StoreObjs) $$ []
    · iunfold mvcc.physOk
      iexists P, iprop(True)
      simp only [named]
      iframe #
      isplitl []
      · imodintro; itrivial
      ipureintro; rw [hγcm]; exact hcmγ
    ihave Hfs : mvcc.fieldShareAt «$r0_ptr» γ ((1 : Qp).half + (1 : Qp).half)
        (⟨GoInterface.ok bi, ti, sc, stopc⟩ : mvcc.StoreObjs) $$ [Hfb Hfidx fifoSched stopc HrstF HcurF]
    · rw [Qp.half_add_half]
      iunfold mvcc.fieldShareAt
      simp only [named]
      iframe HrstF HcurF Hph
      iunfold mvcc.storeFields
      iframe Hfb Hfidx fifoSched stopc
    icases (mvcc.fieldShareAt_split «$r0_ptr» γ _ _ _).1 $$ Hfs with ⟨Hfm, Hfr⟩
    ihave Hfm := mvcc.fieldShare_of_at «$r0_ptr» γ _ _ $$ Hfm
    have h4 := (mvcc.fieldShareAt_split (GF := GF) «$r0_ptr» γ (1 : Qp).half.half (1 : Qp).half.half
      (⟨GoInterface.ok bi, ti, sc, stopc⟩ : mvcc.StoreObjs)).1
    rw [Qp.half_add_half] at h4
    icases h4 $$ Hfr with ⟨Hfc, Hfw⟩
    ihave Hfw := mvcc.fieldShare_of_at «$r0_ptr» γ _ _ $$ Hfw
    -- the store
    ihave #Hlessor1 : mvcc.isLessor (lease.lessorIface lp) γ.leases $$ []
    · rw [hγl]; iexact Hlessor0
    ihave #Hc0 := mvcc.nsr_idxCert_init γ.idx R $$ Hcert
    ihave #Hs : mvcc.isStore «$r0_ptr» γ $$ []
    · iunfold mvcc.isStore
      iexists (lease.lessorIface lp), lg', cfg2, hp
      simp only [named]
      iframe #
      ipureintro; exact ⟨Hlgnn, Hcfg2, Hrb0⟩
    -- `s.mu`'s resource with the lag
    ihave Hmu' : mvcc.muInvLag (GF := GF) «$r0_ptr» γ r.crev r.finRev $$ [HcmA HcuM HwM]
    · iunfold mvcc.muInvLag
      simp only [named]
      isplitl [HcmA]
      · rw [hx]; iexact HcmA
      iframe HcuM
      isplitl [HwM]
      · rw [hγapi]; iexact HwM
      isplitl []
      · iunfold mvcc.crevSafe
        iexists ([[], []] ++ R)
        iframe Hcert
        ipureintro; exact hcl
      iframe HpCr
      ipureintro; exact hfb
    -- the right, by the mode
    ihave #HscN : mvcc.isStopChan (GF := GF) stopc $$ []
    · iunfold mvcc.isStopChan; iexists γstop; iexact Hstop0
    ihave Hjob : mvcc.compactTok (GF := GF) γ r.crev $$ [Hcmp0 HjRT Hsrm Hjc1]
    · iunfold mvcc.compactTok
      isplitl [Hcmp0]
      · iexists r.crev
        rw [hγi]
        iframe Hcmp0
        ipureintro; exact Int.le_refl _
      isplitl [HjRT Hsrm]
      · iapply mvcc.compactJobResM_of
        unfold mvcc.storeRT
        rw [hγk]
        iframe HjRT Hsrm
      iexists (r.finRev, (⟨W64 0, W64 0⟩ : mvcc.Rev))
      isplitl [Hjc1]
      · iapply mvcc.jobCur_intro; iexact Hjc1
      ipureintro; exact hfb.2
    ihave Hcq : mvcc.compactQueue (GF := GF) γ r.crev $$ [Hq0 Hjob]
    · iunfold mvcc.compactQueue
      iexists [n₀], p₀, iprop(True), mvcc.compactTok γ r.crev
      rw [hγs, List.singleton_append]
      iframe Hq0 Hp0 Hjob
      iintro ⟨-, H⟩
      iexact H
    ihave HrightM : |={⊤}=> (mvcc.storeCloserM (GF := GF) «$r0_ptr» γ r.crev ∗
        (if d.cm then iprop(True) else mvcc.crevUB γ.idx (1 : Qp).half (-1)))
        $$ [Hright Hcq Hfc Hstop HsStop]
    · cases hcm : d.cm
      · have hnc : ¬ mvcc.kbCmpM γ.kb := fun h => by rw [hcmγ, hcm] at h; cases h
        obtain ⟨hre, -⟩ := hoff hcm
        subst hre
        rw [mvcc.CmpRecs.crev_empty] at *
        simp only [Bool.false_eq_true, ↓reduceIte]
        imodintro
        iframe Hright
        iapply (mvcc.storeCloserM_off _ _ _ hnc).2
        iunfold mvcc.storeCloser
        iexists _
        iframe Hcq Hfc HscN
        isplitl [Hstop]
        · iunfold mvcc.stopCloser; iexists γstop; iexact Hstop
        rw [hγs]; iexact HsStop
      · have hon : mvcc.kbCmpM γ.kb := hcmγ.2 hcm
        simp only [↓reduceIte]
        have h8 := (mvcc.fieldShareAt_split (GF := GF) «$r0_ptr» γ mvcc.q8 mvcc.q8
          (⟨GoInterface.ok bi, ti, sc, stopc⟩ : mvcc.StoreObjs)).1
        rw [mvcc.q8_add] at h8
        icases h8 $$ Hfc with ⟨HfsC, HfsJ⟩
        imod mvcc.storeStopR_alloc «$r0_ptr» γ _ ⊤ $$ HfsJ HscN with #HsR
        imodintro
        isplitl
        · iapply (mvcc.storeCloserM_on _ _ _ hon).2
          iapply (mvcc.compactRightR_iff _ _ _).2
          iframe Hright Hcq
          iexists _
          iframe HfsC HscN HsR
          isplitl [Hstop]
          · iunfold mvcc.stopCloser; iexists γstop; iexact Hstop
          rw [hγs]; iexact HsStop
        itrivial
    imod HrightM with ⟨HrightM, Hcrf⟩
    imodintro
    iunfold mvcc.nsReady
    iframe Hs Hmu' Hwr Hfm HrightM Hcrf Hfw Hrevs Hcert HlogQ HrgI Hrt Hird1 HpCr Hlr
  -- the resume: `compactLockfree` at the scheduled record, else nothing
  ihave HCt : mvcc.slotFr (GF := GF) γ $$ [HCt]
  · iunfold mvcc.slotFr; rw [hγapi]; iexact HCt
  ihave HK : mvcc.resumeK (GF := GF) «$r0_ptr» r (mvcc.restoreDone «$r0_ptr» (GoInterface.ok bi) ti
      (1 : Qp).half (DFrac.own 1) (DFrac.own 1) (DFrac.own (1 : Qp).half) ([[], []] ++ R) ents r
      iprop(mvcc.storeRT γ ∗ mvcc.restoreRegM d) (mvcc.kbRecs γ.kb γ.bucket r)
      (mvcc.nsRevQ «$r0_ptr» γ r ([[], []] ++ R) ents ti))
      iprop(|={⊤}=> mvcc.nsFin «$r0_ptr» γ d r ([[], []] ++ R) ti hkH dqh PostH YH)
      $$ [Hready HCt HrH Hsup]
  · iunfold mvcc.resumeK
    cases hres : r.resumes
    · -- no resume: the lag is none
      simp only [Bool.false_eq_true, ↓reduceIte]
      iintro HD
      have hcf := mvcc.CmpRecs.crev_noResume r hres
      imod Hready $$ HD with HY
      iunfold mvcc.nsReady at HY
      icases HY with ⟨#Hs, Hmu', Hwr, HfsM, Hright, Hcrf, Hfw, Hrevs, #Hcert, HlogQ, #Hrg, Hrt, Hird,
        #HpCr, Hlr⟩
      imodintro
      iunfold mvcc.nsFin
      rw [mvcc.resumeBackM_no d r hkH dqh PostH YH hres]
      iframe Hs Hright Hcrf Hfw Hrevs Hcert HlogQ Hrg Hrt Hird HCt
      isplitl [Hmu' Hwr HfsM]
      · iunfold mvcc.muInv
        iexists r.crev
        iframe Hwr HfsM
        iapply (mvcc.muInvLag_at _ _ _).1
        rw [← hcf] at *
        iexact Hmu'
      iapply mvcc.lagTok_rest γ r.crev r.finRev
      iframe Hlr
      iunfold mvcc.lagTok
      simp only [hcf, ↓reduceIte]
      itrivial
    · -- the resumed compaction (compaction mode: an image at no record resumes none)
      simp only [↓reduceIte]
      iintro %Ψ HD HΨ
      have hcmT : d.cm = true := by
        cases hcm : d.cm
        · have := (hoff hcm).1; subst this; rw [mvcc.CmpRecs.resumes_empty] at hres; cases hres
        · rfl
      have hon : mvcc.kbCmpM γ.kb := hcmγ.2 hcmT
      obtain ⟨hlt, hcs⟩ := mvcc.CmpRecs.resumes_lt r hres
      have hsr : sint.Z (r.sched.getD (W64 0)) = r.crev := by
        rw [mvcc.CmpRecs.schedRev_getD, hcs]
      have h1r : 1 ≤ sint.Z (r.sched.getD (W64 0)) := by
        have hres' := hres
        unfold mvcc.CmpRecs.resumes at hres'
        simp only [decide_eq_true_eq] at hres'
        cases hsch : r.sched with
        | none => simp [mvcc.CmpRecs.schedRev, hsch] at hres'
        | some x => simp only [Option.getD_some]; exact hpos.2 x hsch
      have hlt' : r.finRev < sint.Z (r.sched.getD (W64 0)) := by rw [hsr]; exact hlt
      imod Hready $$ HD with HY
      iunfold mvcc.nsReady at HY
      icases HY with ⟨#Hs, Hmu', Hwr, HfsM, Hright, Hcrf, Hfw, Hrevs, #Hcert, HlogQ, #Hrg, Hrt, Hird,
        #HpCr, Hlr⟩
      ihave HrH := mvcc.resumeCtxM_lock γ d r P hkH PreH QH PostH dqh XH YH hkγ hres $$ [HrH]
      · iframe HrH HhookP
      icases HrH with ⟨Hctx, HXH, #HreqH⟩
      ihave Hright := (mvcc.storeCloserM_on _ _ _ hon).1 $$ Hright
      ihave Hsup : mvcc.kbWTSupplyM (GF := GF) γ.kb $$ [Hsup]
      · rw [hγk]; first | iexact Hsup | (simp only [hres, ↓reduceIte]; iexact Hsup)
      ihave Hmu' : mvcc.muInvLag (GF := GF) «$r0_ptr» γ (sint.Z (r.sched.getD (W64 0))) r.finRev
          $$ [Hmu']
      · rw [hsr]; iexact Hmu'
      ihave Hright : mvcc.compactRightR (GF := GF) «$r0_ptr» γ (sint.Z (r.sched.getD (W64 0)))
          $$ [Hright]
      · rw [hsr]; iexact Hright
      ihave #HpCr : mvcc.crevPermAt (GF := GF) γ (sint.Z (r.sched.getD (W64 0))) $$ []
      · rw [hsr]; iexact HpCr
      wp_apply (hCLF «$r0_ptr» γ (r.sched.getD (W64 0)) r.finRev P hkH PreH QH PostH dqh XH YH
          hon hlt' h1r) $$ [Hmu' Hright Hrt Hctx Hwr HCt HXH Hsup]
        as %ch %err ⟨Hrt, Hback, Hwr, HCt, %Herr, Hmu, Hright, -, HPostH, -, Hlag, HYH⟩
      · iframe Hs Hmu' Hright Hrt Hctx Hwr HCt HXH Hsup HreqH HpCr
      ihave HrB := mvcc.resumeBackM_of γ d r P hkH dqh PostH YH hkγ hres $$ [Hback HPostH HYH]
      · iframe Hback HPostH HYH
      iapply HΨ
      imodintro
      iunfold mvcc.nsFin
      iframe Hs Hcrf Hfw Hrevs Hcert HlogQ Hrg Hrt Hird HCt HrB
      isplitl [Hmu Hwr HfsM]
      · iunfold mvcc.muInv
        iexists _
        iframe Hmu Hwr HfsM
      isplitl [Hright]
      · iapply (mvcc.storeCloserM_on _ _ _ hon).2; rw [← hsr]; iexact Hright
      ihave Hlag : mvcc.lagTok (GF := GF) γ r.crev r.finRev $$ [Hlag]
      · rw [← hsr]; iexact Hlag
      iapply mvcc.lagTok_rest γ _ r.finRev
      iframe Hlag Hlr
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
