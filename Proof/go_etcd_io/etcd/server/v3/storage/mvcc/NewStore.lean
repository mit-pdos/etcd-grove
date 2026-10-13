/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewStore
public import Spec.go_uber_org.zap.NewNop
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newTreeIndex
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.NewFIFOScheduler
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewHashStorage
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.UnsafeCreateMetaBucket
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__restore

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
variable [go_etcd_io.etcd.cache.v3.Assumptions]

/-- The initial log's bucket is empty. -/
theorem mvcc.bucketMap_init : mvcc.bucketMap [[], []] = (∅ : mvcc.Bucket) := by
  simp [mvcc.bucketMap, mvcc.bucketOf, mvcc.bucketOfRev]; rfl

/-- A ghost variable as two halves (the committed log: `s.revMu`'s and the batch lock's). -/
theorem mvcc.ghostVar_halves {A : Type} [Pos.Countable A] (γ : GName) (a : A) :
    ghostVar (GF := GF) γ 1 a ⊣⊢ ghostVar γ (1 : Qp).half a ∗ ghostVar γ (1 : Qp).half a := by
  have h := (ghostVar_fractional (GF := GF) γ a).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h

/-- A guard of a lock from its reader slots (there is at least one). -/
theorem mvcc.guard_of_slots (rw : Loc) (P : Qp → IProp GF) :
    ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), sync.ownRWMutex rw P) ⊢
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), sync.ownRWMutex rw P) ∗
        sync.isRWMutexGuard rw P := by
  have hpos : 0 < Int.toNat sync.rwmutex.actualMaxReaders :=
    Int.lt_toNat.2 (by simpa using sync.actualMaxReaders_pos)
  obtain ⟨m, hm⟩ : ∃ m, Int.toNat sync.rwmutex.actualMaxReaders = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hm, List.replicate_succ]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨Htok, Htoks⟩
  icases sync.ownRWMutex_guard _ _ $$ Htok with ⟨Htok, #Hguard⟩
  iframe Hguard
  iapply BigSepL.bigSepL_cons.2
  iframe Htok Htoks

/-- One of the reader slots of a lock, and the rest back from it. -/
theorem mvcc.slot_take (Q : IProp GF) :
    ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), Q) ⊢
      Q ∗ (Q -∗ [∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), Q) := by
  have hpos : 0 < Int.toNat sync.rwmutex.actualMaxReaders :=
    Int.lt_toNat.2 (by simpa using sync.actualMaxReaders_pos)
  obtain ⟨m, hm⟩ : ∃ m, Int.toNat sync.rwmutex.actualMaxReaders = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hm, List.replicate_succ]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, Hs⟩
  iframe H1
  iintro H1
  iapply BigSepL.bigSepL_cons.2
  iframe H1 Hs

/-- The store's reader handles from the reader slots of its two locks and its index's. -/
theorem mvcc.storeReaders_of_slots (s ti : Loc) (γ : mvcc.StoreNames) : ∀ (n : Nat),
    s.[store, go!"kvindex"] ↦□
        (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) ∗
      ([∗list] _x ∈ List.replicate n (), sync.ownRWMutex (mvcc.muAddr s) (mvcc.muInv (GF := GF) s γ)) ∗
      ([∗list] _x ∈ List.replicate n (), sync.ownRWMutex (mvcc.revMuAddr s) (mvcc.revMuInv s γ)) ∗
      ([∗list] _x ∈ List.replicate n (), mvcc.idxReader ti γ.idx) ⊢
      [∗list] _x ∈ List.replicate n (), mvcc.storeReaderC s γ
  | 0 => by rw [List.replicate_zero]; iintro _; iapply BigSepL.bigSepL_nil_intro; iempintro
  | n + 1 => by
    rw [List.replicate_succ]
    iintro ⟨#Hidx, Hm, Hr, Hi⟩
    icases BigSepL.bigSepL_cons.1 $$ Hm with ⟨Hm1, Hm⟩
    icases BigSepL.bigSepL_cons.1 $$ Hr with ⟨Hr1, Hr⟩
    icases BigSepL.bigSepL_cons.1 $$ Hi with ⟨Hi1, Hi⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hm1 Hr1 Hi1]
    · iunfold mvcc.storeReaderC
      iexists ti
      simp only [named]
      iframe Hm1 Hr1 Hi1
      iexact Hidx
    · iapply mvcc.storeReaders_of_slots s ti γ n
      iframe Hm Hr Hi
      iexact Hidx

theorem mvcc.NewStore.wp_proof
    (hNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (hNewIdx : mvcc.newTreeIndex.spec (GF := GF) (hG := hG))
    (hFifo : schedule.NewFIFOScheduler.spec (GF := GF) (hG := hG))
    (hHash : mvcc.NewHashStorage.spec (GF := GF) (hG := hG))
    (hMeta : schema.UnsafeCreateMetaBucket.spec (GF := GF) (hG := hG))
    (hRestore : mvcc.store.restore.spec (GF := GF) (hG := hG)) :
    mvcc.NewStore.spec (GF := GF) (hG := hG) := by
  intro lg b le cfg γb γl P f Hcfg0
  wp_start as ⟨Hbk, Hbv, #Hlessor⟩
  -- package facts: the configuration defaults, the `Key` bucket, zap, schedule, schema
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, #Hdbl, ⟨%dsi, #Hdsi⟩, -⟩
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hsch
  icases Hsi with ⟨-, -, -, ⟨%bK, #HKeyG⟩⟩
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hsched : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule $$ []
  · iPkgInit
  wp_apply wp_with_defer
  iintro %defer Hdefer
  (try wp_auto)
  -- `if lg == nil { lg = zap.NewNop() }`
  wp_join iprop(∃ lg' : Loc, lg_ptr ↦ lg' ∗ ⌜lg' ≠ null⌝) with [lg] as ⟨%lg', lg, %Hlgnn⟩
  · wp_apply hNop as %l %Hl
    (try wp_auto)
    wp_join_done
    iexists l; iframe lg; ipureintro; exact Hl
  · iexists lg; iframe lg; ipureintro; exact Hif
  -- the configuration's defaults: a zero batch limit is the default's (`1000`), so positive
  wp_join iprop(∃ c : StoreConfig, cfg_ptr ↦ c ∗ ⌜0 < sint.Z c.CompactionBatchLimit'⌝) with [cfg]
    as ⟨%cfg1, cfg, %Hcfg1⟩
  · iexists _; iframe cfg; ipureintro; simp only; decide
  · iexists _; iframe cfg; ipureintro
    have h0 : sint.Z cfg.CompactionBatchLimit' ≠ 0 := by intro h; apply Hif; word
    omega
  wp_join iprop(∃ c : StoreConfig, cfg_ptr ↦ c ∗ ⌜0 < sint.Z c.CompactionBatchLimit'⌝) with [cfg]
    as ⟨%cfg2, cfg, %Hcfg2⟩
  · iexists _; iframe cfg; ipureintro; exact Hcfg1
  · iexists _; iframe cfg; ipureintro; exact Hcfg1
  -- the store's struct
  wp_apply hNewIdx $$ [] as %ti ⟨%γi, #Hti, Hiw, Hil, Hcu, Hird⟩
  · ipureintro; exact Hlgnn
  (try wp_auto)
  wp_apply hFifo as %sc ⟨%γs, #HisSched⟩
  (try wp_auto)
  wp_apply chan.wp_make1 (V := Unit) as %stopc %γstop ⟨#Hstc, %Hstcap, Hstown⟩
  (try wp_auto)
  iStructNamed «$r0»
  wp_apply hHash as %hp -
  (try wp_auto)
  wp_alloc rv as Hrv
  (try wp_auto)
  wp_alloc wv as Hwv
  (try wp_auto)
  -- `s.le.SetRangeDeleter(...)`: the lessor is not nil
  ihave #Hlessor0 : mvcc.isLessor le γl $$ []
  · iexact Hlessor
  iunfold mvcc.isLessor at Hlessor
  icases Hlessor with ⟨%li, %Hli, -, -, -, #HSetRD⟩
  subst Hli
  (try wp_auto)
  wp_apply HSetRD
  (try wp_auto)
  -- the ghost state: the index at the initial log `[[], []]` (revision 0 and `currentRev = 1`),
  -- the committed log, the revision budget
  imod mvcc.idxWriter_commit γi [] [] (by simp) $$ Hiw Hil with ⟨Hiw, Hil, -⟩
  imod mvcc.idxWriter_commit γi ([] ++ [[]]) [] (by simp) $$ Hiw Hil with ⟨Hiw, Hil, #Hcert⟩
  have hlog : (([] : mvcc.Log) ++ [[]] ++ [[]]) = [[], []] := rfl
  rw [hlog]
  imod ghostVar_alloc (GF := GF) ([[], []] : mvcc.Log) with ⟨%γc, Hc⟩
  icases (mvcc.ghostVar_halves γc _).1 $$ Hc with ⟨Hc1, Hc2⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γr, Hauth⟩
  imod ownTokAuth_add (2 ^ 63 - 5) γr 0 $$ Hauth with ⟨Hauth, Htoks⟩
  rw [Nat.zero_add]
  icases (mvcc.ownTokAuth_halves γr _).1 $$ Hauth with ⟨Hauth, HauthR⟩
  -- the post-lock hook's names: the lock's invariant and the hook, read-only
  imod (saved_prop_alloc (GF := GF) P DFrac.discard DFrac.valid_discard) with ⟨%γh, #Hh⟩
  imod (dghostVar_alloc (GF := GF) f) with ⟨%γhf, Hhf⟩
  imod (dghostVar_persist (GF := GF) γhf 1 f) $$ Hhf with #Hhf
  -- compaction's: the meta keys' record (nothing written), the finished compactions' counter
  imod ghostVar_alloc (GF := GF) ((none, none) : Option w64 × Option w64) with ⟨%γm, Hmeta⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γfin, Hfin, -⟩
  obtain ⟨γ, hγi, hγb, hγc, hγl, hγr, hγh, hγhf, hγm, hγfin, hγs⟩ : ∃ γ : mvcc.StoreNames,
      γ.idx = γi ∧ γ.bucket = γb ∧ γ.clog = γc ∧ γ.leases = γl ∧ γ.revs = γr ∧ γ.hook = γh ∧
      γ.hookFn = γhf ∧ γ.cmeta = γm ∧ γ.fin = γfin ∧ γ.sch = γs :=
    ⟨⟨γi, γb, γc, γl, γr, γh, γhf, γm, γfin, γs⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  ihave #Hhook : mvcc.hookIs γ P f $$ []
  · iunfold mvcc.hookIs; rw [hγh, hγhf]; iframe Hh Hhf
  ihave Hcres : mvcc.compactRes γ $$ [Hmeta Hfin]
  · iunfold mvcc.compactRes
    iexists none, none
    iunfold mvcc.metaCompact
    rw [hγm, hγfin]
    iframe Hmeta
    rw [show mvcc.crevN (mvcc.finRev none) = 0 from rfl]
    iexact Hfin
  ihave #HisSched' : schedule.isScheduler sc γ.sch $$ []
  · rw [hγs]; iexact HisSched
  rw [← hγi, ← hγc, ← hγr]
  ihave Hbv : mvcc.bucketView γ 1 (∅ : mvcc.Bucket) $$ [Hbv]
  · iunfold mvcc.bucketView; rw [hγb]; iexact Hbv
  icases (mvcc.bucketView_halves γ 1 _).1 $$ Hbv with ⟨Hbv1, Hbv2⟩
  -- the compaction revision's authority: half the compaction right's, a quarter for each lock
  icases (mvcc.crevUB_split γ.idx (1 : Qp).half (1 : Qp).half (-1)).1 $$ [Hcu] with ⟨Hright, Hcu⟩
  · rw [Qp.half_add_half]; iexact Hcu
  icases (mvcc.crevUB_split γ.idx (1 : Qp).half.half (1 : Qp).half.half (-1)).1 $$ [Hcu]
    with ⟨HcuM, HcuR⟩
  · rw [Qp.half_add_half]; iexact Hcu
  -- the stop channel
  imod alloc_broadcast_chan (E := ⊤) iprop(True) γstop stopc $$ Hstc Hstown with Hstop
  ihave #Hstop0 := ownBroadcastChan_Unknown _ _ _ _ $$ Hstop
  -- the fixed fields, and the views' `kv`
  iStructNamedPrefix Hrv "R"
  iStructNamedPrefix Hwv "W"
  ipersist b
  ipersist le
  ipersist kvindex
  ipersist lg
  ipersist Rkv
  ipersist Wkv
  ipersist cfg
  ipersist fifoSched
  ipersist stopc
  ipersist hashes
  -- `tx := s.b.BatchTx()`: the backend's contract at the store's names
  ihave #Hbk1 : mvcc.isKeyBackend b (mvcc.bucketView γ) (mvcc.delKey γ) (mvcc.writerRes «$r0_ptr» γ)
      P f $$ [Hbk]
  · iapply Hbk $$ %«$r0_ptr» %γ
    ipureintro; exact hγb
  ihave #Hbk0 : mvcc.isKeyBackend b (mvcc.bucketView γ) (mvcc.delKey γ) (mvcc.writerRes «$r0_ptr» γ)
      P f $$ []
  · iexact Hbk1
  iunfold mvcc.isKeyBackend at Hbk1
  icases Hbk1 with ⟨%Dep, #HbkD⟩
  ihave #HbkD0 := HbkD
  iunfold mvcc.isKeyBackendD at HbkD
  icases HbkD with ⟨%bi, %Hbi, -, -, #HB, #HForce, -⟩
  subst Hbi
  (try wp_auto)
  wp_apply HB as %bt #Hbt
  (try wp_auto)
  iunfold mvcc.isBatchTx at Hbt
  icases Hbt with ⟨%Locked, #Hbt⟩
  iunfold mvcc.batchTxSpec at Hbt
  icases Hbt with ⟨-, -, #HUnlock0, -, -, #HLockOut, #HCreate, -⟩
  -- `tx.LockOutsideApply()`, the buckets created
  -- (`wp_apply` of the batch transaction's triples, whose token `Locked` is a variable from
  -- an existential, fails with an unknown free variable here: bind and apply)
  wp_bind (App (Val #(methods bt.ty _ bt.v)) (Val #()))
  iapply HLockOut
  · itrivial
  inext
  iintro ⟨Hlocked, HP⟩
  (try wp_auto)
  wp_bind (App (Val #(methods bt.ty _ bt.v)) (Val #bK))
  iapply HCreate $$ %([] : mvcc.Puts) %bK [Hlocked]
  · iexact Hlocked
  inext
  iintro Hlocked
  (try wp_auto)
  wp_bind (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.UnsafeCreateMetaBucket)) (Val #(GoInterface.ok bt)))
  iapply (hMeta bt (Locked [])) $$ [Hlocked]
  · iframe Hlocked
    isplitr
    · iPkgInit
    imodintro
    iintro %b'
    ihave Hc := HCreate $$ %([] : mvcc.Puts) %b'
    iexact Hc
  inext
  iintro Hlocked
  (try wp_auto)
  -- `tx.Unlock()`: the batch lock's resource deposited (half of `currentRev`, half the
  -- committed log, half the bucket's view, the index writer, the revision budget, compaction's
  -- part); the deposit witness
  have hsplit := mvcc.own_half_half (1 : Qp)
  ihave Hcur2 : («$r0_ptr».[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half}
      (W64 1 : w64) : IProp GF) $$ [currentRev]
  · rw [← hsplit]; iexact currentRev
  icases ((typedPointsto_dfractional (GF := GF) _ _).dfractional _ _).1 $$ Hcur2 with ⟨HcurA, HcurB⟩
  have hone : (W64 1 : w64) = W64 (((([[], []] : mvcc.Log).length : Int)) - 1) := rfl
  ihave HW : mvcc.writerRes «$r0_ptr» γ $$ [Hauth Hiw Hc1 HcurA Hbv1 Hcres]
  · iunfold mvcc.writerRes
    iexists [[], []], 2 ^ 63 - 5
    simp only [named]
    rw [mvcc.bucketMap_init, ← hone]
    iframe Hauth Hiw Hc1 HcurA Hbv1 Hcres
    iframe #
    ipureintro
    exact ⟨by simp, by simp⟩
  wp_bind (App (Val #(methods bt.ty _ bt.v)) (Val #()))
  iapply HUnlock0 $$ [Hlocked HW HP]
  · iframe Hlocked HW HP
  inext
  iintro #Hdep
  (try wp_auto)
  -- `s.b.ForceCommit()`
  wp_apply HForce
  (try wp_auto)
  -- `s.mu.Lock()`: the lock initialized with half `compactMainRev` and a quarter of the
  -- compaction revision's authority at `-1`, one slot taken
  ihave Hcmp2 : («$r0_ptr».[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half •
      DFrac.own (1 : Qp).half} (W64 (-1) : w64) : IProp GF) $$ [compactMainRev]
  · rw [← hsplit]; iexact compactMainRev
  icases ((typedPointsto_dfractional (GF := GF) _ _).dfractional _ _).1 $$ Hcmp2 with ⟨HcmpA, HcmpB⟩
  imod sync.init_RWMutex (mvcc.muInv «$r0_ptr» γ) (mvcc.muAddr «$r0_ptr») $$ [HcmpA HcuM] mu
    with Hmus
  · inext
    iunfold mvcc.muInv
    iexists -1
    iunfold mvcc.muInvAt
    iframe HcmpA HcuM
    isplitl []
    · iexists [[], []]; iframe Hcert; ipureintro; simp
    ipureintro; decide
  icases mvcc.guard_of_slots _ _ $$ Hmus with ⟨Hmus, #Hmug⟩
  icases mvcc.slot_take _ $$ Hmus with ⟨Hmu1, Hmus⟩
  wp_apply +noauto sync.RWMutex.wp_Lock $$ [$Hmu1] as ⟨Hmul, HmuP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.muInv «$r0_ptr» γ 1)) $$ Hlc1 HmuP with HmuP
  iunfold mvcc.muInv at HmuP
  icases HmuP with ⟨%cm, HmuP⟩
  iunfold mvcc.muInvAt at HmuP
  iNamed HmuP
  ihave %Hcm := mvcc.crevUB_agree γ.idx _ _ cm (-1) HcM (by decide) $$ HcrevM HcuR
  subst Hcm
  ihave HcmpF : («$r0_ptr».[store, go!"compactMainRev"] ↦ (W64 (-1) : w64) : IProp GF)
      $$ [HcmpM HcmpB]
  · rw [show (DFrac.own 1 : DFrac) = DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half from hsplit]
    iapply ((typedPointsto_dfractional (GF := GF) _ _).dfractional _ _).2
    iframe HcmpM HcmpB
  -- `s.restore()` on the fresh backend: nothing changes (`err == nil`)
  wp_apply hRestore $$ %«$r0_ptr» %γ %(GoInterface.ok bi) %(GoInterface.ok li) %ti %lg'
      %(1 : Qp).half %P %f [$Hbv2 $HcurB $HcmpF $revMu] as ⟨Hbv2, HcurB, HcmpF, revMu⟩
  · iframe #; ipureintro; exact Hlgnn
  (try wp_auto)
  ihave HcmpF2 : («$r0_ptr».[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half •
      DFrac.own (1 : Qp).half} (W64 (-1) : w64) : IProp GF) $$ [HcmpF]
  · rw [← hsplit]; iexact HcmpF
  icases ((typedPointsto_dfractional (GF := GF) _ _).dfractional _ _).1 $$ HcmpF2 with ⟨HcmpA, HcmpB⟩
  -- `s.revMu` initialized with the committed log `[[], []]`: the other halves of
  -- `currentRev`, of the committed log and of the bucket's view, the index's certificate, the
  -- other half of `compactMainRev` and the other quarter of its authority
  imod sync.init_RWMutex (mvcc.revMuInv «$r0_ptr» γ) (mvcc.revMuAddr «$r0_ptr»)
    $$ [HcurB Hc2 Hbv2 HauthR Hil HcmpB HcuR] revMu with Hrevs
  · inext
    iunfold mvcc.revMuInv
    iexists [[], []], 2 ^ 63 - 5, -1
    simp only [named]
    rw [mvcc.bucketMap_init, ← hone]
    iframe HcurB Hc2 Hbv2 HauthR Hil HcmpB HcuR
    iframe #
    ipureintro; simp
  icases mvcc.guard_of_slots _ _ $$ Hrevs with ⟨Hrevs, #Hrevg⟩
  -- the deferred `s.mu.Unlock()`
  wp_apply sync.RWMutex.wp_Unlock $$ [$Hmul HcmpA HcrevM] as Hmu1
  · inext
    iunfold mvcc.muInv
    iexists -1
    iunfold mvcc.muInvAt
    iframe HcmpA HcrevM
    iframe #
    ipureintro; decide
  (try wp_auto)
  -- the store
  ihave #Hlessor1 : mvcc.isLessor (GoInterface.ok li) γ.leases $$ []
  · rw [hγl]; iexact Hlessor0
  ihave #Hs : mvcc.isStore «$r0_ptr» γ $$ []
  · iunfold mvcc.isStore
    iexists (GoInterface.ok bi), (GoInterface.ok li), ti, lg', P, f, Dep, cfg2, sc, stopc, hp
    simp only [named]
    iframe #
    ipureintro; exact ⟨Hlgnn, Hcfg2⟩
  ispecialize Hmus $$ Hmu1
  iapply HΦ
  iexists γ
  isplitr
  · ipureintro; exact ⟨hγb, hγl⟩
  iframe Hs Hhook Htoks Hcert
  isplitl [ReadView WriteView]
  · iexists rv, wv
    iunfold mvcc.isReadView
    iunfold mvcc.isWriteView
    simp only [named]
    iframe ReadView WriteView
    iframe #
  isplitl [Hmus Hrevs Hird]
  · iapply mvcc.storeReaders_of_slots «$r0_ptr» ti γ
    iframe Hmus Hrevs Hird
    iexact kvindex
  isplitl [Hstop]
  · iunfold mvcc.storeCloser; iexists stopc; iframe stopc
    iunfold mvcc.stopCloser; iexists γstop; iexact Hstop
  isplitl []
  · iunfold mvcc.storeStop; iexists stopc; iframe stopc
    iunfold mvcc.isStopChan; iexists γstop; iexact Hstop0
  iunfold mvcc.compactRight
  iexact Hright

end proof

end EtcdGrove
end Perennial
