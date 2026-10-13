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

/-- The store's reader handles (of a store that may be compacted) from the reader slots of its
two locks and its index's, and the backend's reader tokens. -/
theorem mvcc.storeReaders_of_slots (s ti : Loc) (γ : mvcc.StoreNames) : ∀ (n : Nat),
    s.[store, go!"kvindex"] ↦□
        (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) ∗
      ([∗list] _x ∈ List.replicate n (), sync.ownRWMutex (mvcc.muAddr s) (mvcc.muInv (GF := GF) s γ)) ∗
      ([∗list] _x ∈ List.replicate n (), sync.ownRWMutex (mvcc.revMuAddr s) (mvcc.revMuInv s γ)) ∗
      ([∗list] _x ∈ List.replicate n (), mvcc.idxReader ti γ.idx) ∗
      ([∗list] _x ∈ List.replicate n (), mvcc.storeRT γ) ⊢
      [∗list] _x ∈ List.replicate n (), mvcc.storeReaderC s γ
  | 0 => by rw [List.replicate_zero]; iintro _; iapply BigSepL.bigSepL_nil_intro; iempintro
  | n + 1 => by
    rw [List.replicate_succ]
    iintro ⟨#Hidx, Hm, Hr, Hi, Ht⟩
    icases BigSepL.bigSepL_cons.1 $$ Hm with ⟨Hm1, Hm⟩
    icases BigSepL.bigSepL_cons.1 $$ Hr with ⟨Hr1, Hr⟩
    icases BigSepL.bigSepL_cons.1 $$ Hi with ⟨Hi1, Hi⟩
    icases BigSepL.bigSepL_cons.1 $$ Ht with ⟨Ht1, Ht⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hm1 Hr1 Hi1 Ht1]
    · iunfold mvcc.storeReaderC
      iexists ti
      simp only [named]
      iframe Hm1 Hr1 Hi1 Ht1
      iexact Hidx
    · iapply mvcc.storeReaders_of_slots s ti γ n
      iframe Hm Hr Hi Ht
      iexact Hidx

theorem mvcc.NewStore.wp_proof
    (hNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (hNewIdx : mvcc.newTreeIndex.spec (GF := GF) (hG := hG))
    (hFifo : schedule.NewFIFOScheduler.spec (GF := GF) (hG := hG))
    (hHash : mvcc.NewHashStorage.spec (GF := GF) (hG := hG))
    (hMeta : schema.UnsafeCreateMetaBucket.spec (GF := GF) (hG := hG))
    (hRestore : mvcc.store.restore.spec (GF := GF) (hG := hG)) :
    mvcc.NewStore.spec (GF := GF) (hG := hG) := by
  intro lg b le cfg kb γb γl P f Hcfg0
  wp_start as ⟨Hbk, Hbv, Hrg, Hwt1, Hwt2, Hrts, Hlrd, #Hlessor⟩
  -- package facts: the configuration defaults, the `Key` bucket, zap, schedule, schema
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, #Hdbl, ⟨%dsi, #Hdsi⟩, -⟩
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hsch
  icases Hsi with ⟨-, -, -, ⟨%bK, #HKeyG, -⟩⟩
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
  wp_apply hNewIdx $$ [] as %ti ⟨%γi, #Hti, Hiw, Hil, Hcu, Hcmp0, Hird⟩
  · ipureintro; exact Hlgnn
  (try wp_auto)
  wp_apply hFifo $$ [] as %sc ⟨%γs, %n₀, %p₀, #HisFifo, Hstop, Hq0, #Hp0⟩
  · ipureintro; exact Hlgnn
  -- the store never stops its scheduler: its untracked jobs need `schedLive` (2026-10-13, the
  -- request path's unit 4c's FIFO contract)
  imod schedule.schedLive_of_stopTok γs $$ Hstop with #Hlive
  ihave #HisSched : schedule.isScheduler sc γs $$ []
  · iunfold schedule.isScheduler; iframe HisFifo Hlive
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
  icases Hlessor with ⟨%lp, %Hli, -, -, -, -, #HSetRD⟩
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
  obtain ⟨γ, hγi, hγb, hγc, hγl, hγr, hγh, hγhf, hγk, hγm, hγfin, hγs⟩ : ∃ γ : mvcc.StoreNames,
      γ.idx = γi ∧ γ.bucket = γb ∧ γ.clog = γc ∧ γ.leases = γl ∧ γ.revs = γr ∧ γ.hook = γh ∧
      γ.hookFn = γhf ∧ γ.kb = kb ∧ γ.cmeta = γm ∧ γ.fin = γfin ∧ γ.sch = γs :=
    ⟨⟨γi, γb, γc, γl, γr, γh, γhf, kb, γm, γfin, γs⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl⟩
  ihave #Hhook : mvcc.hookIs γ P f $$ []
  · iunfold mvcc.hookIs; rw [hγh, hγhf]; iframe Hh Hhf
  ihave Hcres : mvcc.compactRes γ $$ [Hmeta Hfin]
  · iunfold mvcc.compactRes
    iexists none, none, 0
    iunfold mvcc.metaCompact
    rw [hγm, hγfin]
    iframe Hmeta Hfin
    ipureintro; exact Nat.le_refl _
  ihave #HisSched' : schedule.isScheduler sc γ.sch $$ []
  · rw [hγs]; iexact HisSched
  rw [← hγi, ← hγc, ← hγr]
  ihave Hbv : mvcc.bucketView γ 1 (∅ : mvcc.Bucket) $$ [Hbv]
  · iunfold mvcc.bucketView; rw [hγb, hγk]; iexact Hbv
  rw [← hγk]
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
  ihave #Hbk1 : mvcc.storeBackend b «$r0_ptr» γ P f $$ [Hbk]
  · iapply Hbk $$ %«$r0_ptr» %γ
    ipureintro; exact ⟨hγb, rfl⟩
  iunfold mvcc.storeBackend at Hbk1
  icases Hbk1 with ⟨%Dep, #Hbk1⟩
  ihave #Hbk0 := Hbk1
  iunfold mvcc.isKeyBackendG at Hbk1
  icases Hbk1 with ⟨%bi, %Hbi, -, -, #HB, #HForce, -⟩
  subst Hbi
  (try wp_auto)
  wp_apply HB as %bt #Hbt
  (try wp_auto)
  iunfold mvcc.isBatchTxG at Hbt
  icases Hbt with ⟨%Locked, %LockedO, -, #Hinit⟩
  iunfold mvcc.batchTxInitSpec at Hinit
  icases Hinit with ⟨#HLockOut, #HCreate, #HUnlock0⟩
  -- `tx.LockOutsideApply()`, the buckets created
  -- (`wp_apply` of the batch transaction's triples, whose token `Locked` is a variable from
  -- an existential, fails with an unknown free variable here: bind and apply)
  icases mvcc.slot_take _ $$ Hrts with ⟨Hrt1, Hrts⟩
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
  wp_bind (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.UnsafeCreateMetaBucket)) (Val #(GoInterface.ok bt)))
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
  -- `tx.Unlock()`: the batch lock's resource deposited (half of `currentRev`, half the
  -- committed log, half the bucket's view, the index writer, the revision budget, compaction's
  -- part), registered in the backend's late-bound slot; the deposit witness
  have hsplit := mvcc.own_half_half (1 : Qp)
  ihave Hcur2 : («$r0_ptr».[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half}
      (W64 1 : w64) : IProp GF) $$ [currentRev]
  · rw [← hsplit]; iexact currentRev
  icases ((typedPointsto_dfractional (GF := GF) _ _).dfractional _ _).1 $$ Hcur2 with ⟨HcurA, HcurB⟩
  have hone : (W64 1 : w64) = W64 (((([[], []] : mvcc.Log).length : Int)) - 1) := rfl
  ihave Hlrd : lease.lessorRdOf γ.leases $$ [Hlrd]
  · rw [hγl]; iexact Hlrd
  ihave HW : mvcc.writerRes «$r0_ptr» γ $$ [Hauth Hiw Hc1 HcurA Hbv1 Hcres Hlrd]
  · iunfold mvcc.writerRes
    iexists [[], []], 2 ^ 63 - 5
    simp only [named]
    rw [mvcc.bucketMap_init, ← hone]
    iframe Hauth Hiw Hc1 HcurA Hbv1 Hcres Hlrd
    iframe #
    ipureintro
    exact ⟨by simp, by simp⟩
  imod mvcc.storeW_register «$r0_ptr» γ $$ [$HWi $Hrg $HW] with ⟨HW, #Hregd⟩
  wp_bind (App (Val #(methods bt.ty _ bt.v)) (Val #()))
  iapply HUnlock0 $$ %(0 + 1 + 1) [Hlocked HW HP]
  · iframe Hlocked HW HP
  inext
  iintro #Hdep
  (try wp_auto)
  -- `s.b.ForceCommit()`
  wp_apply HForce $$ [$Hrt1 $Hwt2] as Hrt1
  ispecialize Hrts $$ Hrt1
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
  wp_apply hRestore $$ %«$r0_ptr» %γ %(GoInterface.ok bi) %(lease.lessorIface lp) %ti %lg'
      %(1 : Qp).half %P %f %_ %_ %_ %_ %_ %_ %_ [$Hbv2 $HcurB $HcmpF $revMu]
      as ⟨Hbv2, HcurB, HcmpF, revMu⟩
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
  ihave #Hlessor1 : mvcc.isLessor (lease.lessorIface lp) γ.leases $$ []
  · rw [hγl]; iexact Hlessor0
  ihave #Hs : mvcc.isStore «$r0_ptr» γ $$ []
  · iunfold mvcc.isStore
    iexists (GoInterface.ok bi), (lease.lessorIface lp), ti, lg', P, f, Dep, cfg2, sc, stopc, hp
    simp only [named]
    iframe #
    ipureintro; exact ⟨Hlgnn, Hcfg2⟩
  ispecialize Hmus $$ Hmu1
  iapply HΦ
  iexists γ
  isplitr
  · ipureintro; exact ⟨hγb, hγl, rfl⟩
  iframe Hs Hhook Htoks Hcert
  isplitl [ReadView WriteView]
  · iexists rv, wv
    iunfold mvcc.isReadView
    iunfold mvcc.isWriteView
    simp only [named]
    iframe ReadView WriteView
    iframe #
  isplitl [Hmus Hrevs Hird Hrts]
  · iapply mvcc.storeReaders_of_slots «$r0_ptr» ti γ
    iframe Hmus Hrevs Hird Hrts
    iexact kvindex
  isplitl [Hstop]
  · iunfold mvcc.storeCloser; iexists stopc; iframe stopc
    iunfold mvcc.stopCloser; iexists γstop; iexact Hstop
  isplitl []
  · iunfold mvcc.storeStop; iexists stopc; iframe stopc
    iunfold mvcc.isStopChan; iexists γstop; iexact Hstop0
  -- the compaction right: the index compactor's token at `-1` beside the scheduler's queue, whose
  -- last name saves the initial `True` (2026-10-13, unit 5c)
  iunfold mvcc.compactRight
  iframe Hright
  iunfold mvcc.compactQueue
  iexists [n₀], p₀, iprop(True), mvcc.compactTok γ (-1)
  rw [hγs, List.singleton_append]
  iframe Hq0 Hp0
  isplitl [Hcmp0]
  · iunfold mvcc.compactTok
    iexists -1
    rw [hγi]
    iframe Hcmp0
    ipureintro; exact Int.le_refl _
  iintro ⟨-, H⟩
  iexact H

end proof

end EtcdGrove
end Perennial
