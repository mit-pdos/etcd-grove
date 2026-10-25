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
two locks and the readers' tickets (D22 receiver epochs, S4: the index's slots are in the readers'
pool; S5a: so are the backend's reader tokens). -/
theorem mvcc.storeReaders_of_slots (s : Loc) (γ : mvcc.StoreNames) : ∀ (n : Nat),
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
    · iapply mvcc.storeReaders_of_slots s γ n
      iframe Hm Hr Hk

/-- `n` tokens, one by one. -/
theorem mvcc.ownToks_ones (γ : GName) : ∀ (n : Nat),
    ownToks (GF := GF) γ n ⊢ [∗list] _x ∈ List.replicate n (), ownToks γ 1
  | 0 => by rw [List.replicate_zero]; iintro _; iapply BigSepL.bigSepL_nil_intro; iempintro
  | n + 1 => by
    rw [List.replicate_succ]
    iintro H
    icases (ownToks_add 1 n γ).1 $$ H with ⟨Hn, H1⟩
    iapply BigSepL.bigSepL_cons.2
    iframe H1
    iapply mvcc.ownToks_ones γ n
    iexact Hn

theorem mvcc.NewStore.wp_proof
    (hNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (hNewIdx : mvcc.newTreeIndex.spec (GF := GF) (hG := hG))
    (hFifo : schedule.NewFIFOScheduler.spec (GF := GF) (hG := hG))
    (hHash : mvcc.NewHashStorage.spec (GF := GF) (hG := hG))
    (hMeta : schema.UnsafeCreateMetaBucket.spec (GF := GF) (hG := hG))
    (hRestore : mvcc.store.restore.spec (GF := GF) (hG := hG)) :
    mvcc.NewStore.spec (GF := GF) (hG := hG) := by
  intro lg b le cfg kb γb γl P f wq γi γok Hcfg0 Hrb0
  wp_start as ⟨Hbk, Hbv, Hncmp, Hrg, Hwt1, Hwt2, Hrts, Hlrd, #Hlessor, Hifresh, Hok⟩
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
  imod mvcc.idxFresh_split γi $$ Hifresh with ⟨Hnauth0, Hcmpf, #Hclb0, #Hllb0, Hiw, Hil, Hcu⟩
  wp_apply (hNewIdx γi lg' 0 []) $$ [Hnauth0 Hcmpf] as %ti ⟨Hix, Hig, Hcmp0⟩
  · iframe Hnauth0 Hcmpf; iframe #; ipureintro; exact Hlgnn
  (try wp_auto)
  wp_apply hFifo $$ [] as %sc ⟨%γs, %n₀, %p₀, #HisFifo, HsStop, Hq0, #Hp0⟩
  · ipureintro; exact Hlgnn
  -- the scheduler's stop token goes to the closer (`storeCloser`, D19m (C), 2026-10-18): the
  -- caller gives it up when the store will not be closed (until then given up here)
  (try wp_auto)
  wp_apply chan.wp_make1 (V := Unit) as %stopc %γstop ⟨#Hstc, %Hstcap, Hstown⟩
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
  (try wp_auto)
  wp_apply HSetRD
  (try wp_auto)
  -- the ghost state: the index at the initial log `[[], []]` (revision 0 and `currentRev = 1`),
  -- the committed log, the revision budget
  imod mvcc.idxWriter_commit γi [] [] (by simp) $$ Hiw Hil with ⟨Hiw, Hil, -⟩
  imod mvcc.idxWriter_commit γi ([] ++ [[]]) [] (by simp) $$ Hiw Hil with ⟨Hiw, Hil, #Hcert⟩
  have hlog : (([] : mvcc.Log) ++ [[]] ++ [[]]) = [[], []] := rfl
  rw [hlog]
  icases mvcc.idxWriter_nevLb_nil γi [[], []] $$ Hiw with ⟨Hiw, #Hnev0⟩
  imod ghostVar_alloc (GF := GF) ([[], []] : mvcc.Log) with ⟨%γc, Hc⟩
  icases ghostVar_halves γc _ $$ Hc with ⟨Hc1, Hc2⟩
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
  -- the writer's (D22 receiver epochs, S2): `s.mu`'s deposit ghost, the batch lock's key, the
  -- ghost of the log the bucket's view is of
  imod ghostVar_alloc (GF := GF) () with ⟨%γwr, Hwr⟩
  imod ghostVar_alloc (GF := GF) () with ⟨%γwk, Hwk⟩
  imod ghostVar_alloc (GF := GF) ([[], []] : mvcc.Log) with ⟨%γwv, Hwvg⟩
  icases ghostVar_halves γwv _ $$ Hwvg with ⟨Hwv1, Hwv2⟩
  -- the store's objects, pinned (D22 receiver epochs, S3: until S5)
  -- (S5b) the store's current objects and physical names, set once the names are made
  imod (dghostVar_alloc (GF := GF) (((⟨b, ti, sc, stopc⟩ : mvcc.StoreObjs),
      (⟨γi.nev, γi.cmp, γb, γh, γhf, kb, γm, γfin, γs, γwk, γwv⟩ : mvcc.PhysNames)) :
      mvcc.StoreObjs × mvcc.PhysNames)) with ⟨%γcur, Hcur1⟩
  -- `s.revMu`'s restoring flag, down: half the lock's, half the fields' shares' (S3)
  imod (dghostVar_alloc (GF := GF) false) with ⟨%γrst, Hrst⟩
  icases ((dghostVar_fractional (GF := GF) γrst false).fractional (1 : Qp).half (1 : Qp).half).1
    $$ [Hrst] with ⟨HrstF, HrstR⟩
  · rw [Qp.half_add_half]; iexact Hrst
  -- the readers' tickets: every one idle (D22 receiver epochs, S4)
  imod ownTokAuth_alloc (GF := GF) with ⟨%γtk, Htka⟩
  imod ownTokAuth_add mvcc.nReaders γtk 0 $$ Htka with ⟨Htka, Htks⟩
  rw [Nat.zero_add]
  imod ownTokAuth_alloc (GF := GF) with ⟨%γtko, Htkoa⟩
  -- (S5a) the watchable store's deposit ghost, and the tickets out under its lock
  imod ghostVar_alloc (GF := GF) () with ⟨%γwsd, Hwsd⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γtkw, Htkwa⟩
  -- (the restore plan's R5e) the retired tickets: none
  imod ownTokAuth_alloc (GF := GF) with ⟨%γtkr, Htkra⟩
  obtain ⟨γ, hγi, hγb, hγc, hγl, hγr, hγh, hγhf, hγk, hγm, hγfin, hγs, hγok, hγw, hγwr, hγwk,
      hγwv, hγcur, hγrst, hγtk, hγtko, hγwsd, hγtkw, hγtkr⟩ :
      ∃ γ : mvcc.StoreNames,
      γ.idx = γi ∧ γ.bucket = γb ∧ γ.clog = γc ∧ γ.leases = γl ∧ γ.revs = γr ∧ γ.hook = γh ∧
      γ.hookFn = γhf ∧ γ.kb = kb ∧ γ.cmeta = γm ∧ γ.fin = γfin ∧ γ.sch = γs ∧ γ.cok = γok ∧
      γ.watchQ = wq ∧ γ.wr = γwr ∧ γ.wk = γwk ∧ γ.wv = γwv ∧ γ.cur = γcur ∧ γ.rst = γrst ∧
      γ.tk = γtk ∧ γ.tko = γtko ∧ γ.wsd = γwsd ∧ γ.tkw = γtkw ∧ γ.tkr = γtkr :=
    ⟨⟨γi, γb, γc, γl, γr, γh, γhf, kb, γm, γfin, γs, γok, wq, γwr, γwk, γwv, γcur, γrst, γtk, γtko,
        γwsd, γtkw, γtkr⟩,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
  rw [← hγrst] at *
  rw [← hγtk, ← hγtko, ← hγtkw, ← hγtkr]
  ihave Hwsd : mvcc.wsDep γ $$ [Hwsd]
  · iunfold mvcc.wsDep; rw [hγwsd]; iexact Hwsd
  rw [← hγwr] at *
  rw [← hγwk] at *
  rw [← hγwv] at *
  -- the current objects and names, at the store's (D22 receiver epochs, S5b): half for the fields'
  -- shares, an eighth each for `s.revMu`, the writer's invariant, the readers' pool and the
  -- writer's fragment
  ihave Hcur1 : ∃ v : mvcc.StoreObjs × mvcc.PhysNames, dghostVar (GF := GF) γ.cur (DFrac.own 1) v
      $$ [Hcur1]
  · iexists _; rw [hγcur]; iexact Hcur1
  icases Hcur1 with ⟨%v0, Hcur1⟩
  imod dghostVar_update (((⟨b, ti, sc, stopc⟩ : mvcc.StoreObjs), γ.phys) : mvcc.StoreObjs × mvcc.PhysNames)
    γ.cur _ $$ Hcur1 with Hcur1
  ihave Hcur1 : mvcc.curAt γ (DFrac.own 1) ⟨b, ti, sc, stopc⟩ $$ [Hcur1]
  · iunfold mvcc.curAt; iexact Hcur1
  icases (mvcc.curAt_halves γ 1 _).1 $$ Hcur1 with ⟨HcurF, HcurR⟩
  icases (mvcc.curAt_halves γ _ _).1 $$ HcurR with ⟨HcurR1, HcurR2⟩
  icases (mvcc.curAt_halves γ _ _).1 $$ HcurR1 with ⟨HcurRev, HcurWi⟩
  icases (mvcc.curAt_halves γ _ _).1 $$ HcurR2 with ⟨HcurPool, HcurFrag⟩
  ihave #HhookP : mvcc.hookP γ P $$ []
  · iunfold mvcc.hookP; rw [hγh]; iexact Hh
  ihave #Hhook : mvcc.hookInit γ P f $$ []
  · iunfold mvcc.hookInit
    iframe HhookP
    cases kb with
    | none => simp only [hγk, mvcc.hookFn, mvcc.kbHookIs]; rw [hγhf]; iexact Hhf
    | some d => simp only [hγk]; itrivial
  ihave Hcres : mvcc.compactRes γ $$ [Hmeta Hfin]
  · iunfold mvcc.compactRes
    iexists none, none, 0
    iunfold mvcc.metaCompact
    rw [hγm, hγfin]
    iframe Hmeta Hfin
    ipureintro; exact Nat.le_refl _
  ihave #HisSched' : schedule.isFifo sc γ.sch $$ []
  · rw [hγs]; iexact HisFifo
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
  ipersist le
  ipersist lg
  ipersist Rkv
  ipersist Wkv
  ipersist cfg
  ipersist hashes
  -- `tx := s.b.BatchTx()`: the backend's contract at the store's names
  ihave #Hbk1 : mvcc.storeBackend b «$r0_ptr» γ P $$ [Hbk]
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
  -- `tx.Unlock()`: the batch lock's resource deposited (half the committed log, half the
  -- bucket's view, compaction's part), registered in the backend's late-bound slot; the deposit
  -- witness. (R4) The writer's state (half of `currentRev`, the index writer) and its invariant,
  -- the readers' pool and `s.mu`'s invariant are made after `restore`, which writes all of
  -- `currentRev` and rebuilds the private index, making its lock (`idx_publish`).
  have hsplit := dfrac_own_half_half (1 : Qp)
  have hone : (W64 1 : w64) = W64 (((([[], []] : mvcc.Log).length : Int)) - 1) := rfl
  ihave Hlrd : lease.lessorRdOf γ.leases $$ [Hlrd]
  · rw [hγl]; iexact Hlrd
  ihave HW : mvcc.writerRes «$r0_ptr» γ $$ [Hwk Hwv2 Hbv1 Hcres]
  · iunfold mvcc.writerRes
    iexists [[], []]
    simp only [named]
    rw [mvcc.bucketMap_init]
    iunfold mvcc.writerKey
    iframe Hwk Hwv2 Hbv1 Hcres
    iframe #
    ipureintro; simp
  imod mvcc.storeW_register «$r0_ptr» γ $$ [$HWi $Hrg $HW] with ⟨HW, #Hregd⟩
  wp_bind (App (Val #(methods bt.ty _ bt.v)) (Val #()))
  iapply HUnlock0 $$ %(0 + 1 + 1) [Hlocked HW HP]
  · iframe Hlocked HW HP
  inext
  iintro #Hdep
  (try wp_auto)
  -- `s.b.ForceCommit()`
  ihave #Hrq0 := mvcc.storeReq_true (GF := GF) γ
  wp_apply HForce $$ %iprop(True) %iprop(True) [$Hrt1 $Hwt2] as ⟨Hrt1, -⟩
  · iframe #
  ispecialize Hrts $$ Hrt1
  (try wp_auto)
  -- `s.mu.Lock()` on private memory (its invariant names the index, which `restore` makes)
  wp_apply (plain.wp_Lock sync.atomic.Int32.wp_Add (mvcc.muAddr «$r0_ptr»)) $$ [$mu] as mu
  (try wp_auto)
  -- `s.restore()` on the fresh backend (an empty bucket): nothing changes (`err == nil`); a
  -- reader's slot lent; the backend's no-compaction token consumed (D22 S-g)
  ihave Hncmp : mvcc.kbNoCmp γ.kb γ.bucket $$ [Hncmp]
  · rw [hγk, hγb]; iexact Hncmp
  ihave #HbkW := mvcc.isKeyBackendG_wand $$ Hbk0
  icases mvcc.slot_take _ $$ Hrts with ⟨Hrt1, Hrts⟩
  ihave Hrt1 : mvcc.storeRT (GF := GF) γ $$ [Hrt1]
  · first | iexact Hrt1 | (rw [hγk]; iexact Hrt1)
  ihave Hbv2 : mvcc.restoreView (GF := GF) (GoInterface.ok bi) γ (mvcc.storeRT γ) (1 : Qp).half []
      $$ [Hbv2]
  · unfold mvcc.restoreView mvcc.restoreViewOut; simp only [↓reduceIte]; iframe
  have hR := hRestore «$r0_ptr» γ (GoInterface.ok bi) (lease.lessorIface lp) ti lg'
      (1 : Qp).half P (mvcc.hookFn γ) (mvcc.storeRT γ) (mvcc.storeWT γ) (mvcc.storeW «$r0_ptr» γ)
      (mvcc.kbWi γ.kb) Dep (mvcc.storeCmp γ) (mvcc.storePutOk γ)
      (DFrac.own 1) (DFrac.own 1) []
      iprop(«$r0_ptr».[store, go!"revMu"] ↦ (zero_val sync.RWMutex) ∗
        «$r0_ptr».[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half} (W64 1 : w64))
      iprop(«$r0_ptr».[store, go!"revMu"] ↦ rwW)
      iprop(«$r0_ptr».[store, go!"revMu"] ↦ (zero_val sync.RWMutex) ∗
        «$r0_ptr».[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half} (W64 1 : w64) ∗
        iprop(mvcc.restoreViewOut γ (1 : Qp).half [] ∗ mvcc.isTreeIndex ti γ.idx ∗
          ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
            mvcc.idxReader ti γ.idx) ∗ ⌜mvcc.logCh ([[], []] : mvcc.Log) < receiptBound GF⌝))
      (DFrac.own 1) (1 : Qp).half (1 : Qp).half mvcc.restoreLogOk_nil (Qp.half_add_half 1)
  simp only [List.append_nil] at hR
  icases mvcc.idxWriter_lb γ.idx [[], []] $$ Hiw with ⟨Hiw, #Hiwlb⟩
  rw [show (mvcc.evsOf ([[], []] ++ [[]])).length = 0 from rfl,
    show (W64 ((([[], []] : mvcc.Log).length : Int) - 1) : w64) = W64 1 from rfl] at hR
  icases (mvcc.typedPointsto_parts _ _ (1 : Qp).half (1 : Qp).half (Qp.half_add_half 1)).1
    $$ currentRev with ⟨HcurA, HcurB⟩
  -- `restore`'s lock of `s.revMu`: private memory (`PlainRWMutex.lean`)
  ihave HLk : mvcc.revLockW (GF := GF) «$r0_ptr» (1 : Qp).half
      iprop(«$r0_ptr».[store, go!"revMu"] ↦ (zero_val sync.RWMutex) ∗
        «$r0_ptr».[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half} (W64 1 : w64))
      iprop(«$r0_ptr».[store, go!"revMu"] ↦ rwW) $$ []
  · iunfold mvcc.revLockW
    iintro %Ψ ⟨HrevMu, Hc⟩ HΨ
    wp_apply (plain.wp_Lock sync.atomic.Int32.wp_Add _) $$ [$HrevMu] as HrevMu
    iapply HΨ $$ %_ Hc HrevMu
  ihave HUl : mvcc.revUnlockW (GF := GF) «$r0_ptr» (1 : Qp).half ([[], []] : mvcc.Log)
      iprop(«$r0_ptr».[store, go!"revMu"] ↦ rwW)
      iprop(mvcc.restoreViewOut γ (1 : Qp).half [] ∗ mvcc.isTreeIndex ti γ.idx ∗
          ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
            mvcc.idxReader ti γ.idx) ∗ ⌜mvcc.logCh ([[], []] : mvcc.Log) < receiptBound GF⌝)
      iprop(«$r0_ptr».[store, go!"revMu"] ↦ (zero_val sync.RWMutex) ∗
        «$r0_ptr».[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half} (W64 1 : w64) ∗
        iprop(mvcc.restoreViewOut γ (1 : Qp).half [] ∗ mvcc.isTreeIndex ti γ.idx ∗
          ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
            mvcc.idxReader ti γ.idx) ∗ ⌜mvcc.logCh ([[], []] : mvcc.Log) < receiptBound GF⌝)) $$ []
  · iunfold mvcc.revUnlockW
    rw [show (W64 ((([[], []] : mvcc.Log).length : Int) - 1) : w64) = W64 1 from rfl]
    iintro %Ψ Hc HrevMu Hv HΨ
    wp_apply (plain.wp_Unlock sync.atomic.Int32.wp_Add _) $$ [$HrevMu] as HrevMu
    iapply HΨ
    iframe HrevMu Hc Hv
  wp_apply hR
      $$ [$Hbv2 $Hrt1 $HcurA $compactMainRev $revMu $HcurB $HLk $HUl $Hncmp $b $kvindex $Hix $Hig $Hiwlb]
      as ⟨Hrt1, -, ⟨revMu, HcurB, Hbv2, #Hti, Hird, -⟩, HcurA, compactMainRev, b, kvindex⟩
  · iframe #; ipureintro; exact Hlgnn
  ihave Hbv2 : mvcc.bucketView (GF := GF) γ (1 : Qp).half ∅ $$ [Hbv2]
  · unfold mvcc.restoreViewOut; simp only [↓reduceIte]; iexact Hbv2
  ihave Hrt1 : mvcc.kbRT (GF := GF) γ.kb $$ [Hrt1]
  · iexact Hrt1
  ispecialize Hrts $$ Hrt1
  (try wp_auto)
  -- the writer's state, in the writer's invariant (D22 receiver epochs, S2)
  ihave HL : mvcc.writerL «$r0_ptr» γ $$ [Hauth Hiw Hc1 Hwv1 HcurA Hlrd]
  · iunfold mvcc.writerL
    iexists [[], []], 2 ^ 63 - 5
    simp only [named]
    rw [← hone]
    iframe Hauth Hiw Hc1 Hwv1 HcurA Hlrd
    iframe #
    ipureintro
    exact ⟨by simp, by simp⟩
  -- (S6) the writer's state with the store registered
  imod (inv_alloc mvcc.writerN ⊤ (mvcc.writerInvBody «$r0_ptr» γ))
    $$ [HL HcurWi] with #Hwi
  · inext; iunfold mvcc.writerInvBody; ileft
    iexists γ.phys, _; rw [mvcc.StoreNames.withPhys_self]; iframe HcurWi; ileft; iframe HL
    iunfold mvcc.writerReg; ileft; iexact Hregd
  ihave #Hwi : mvcc.writerInv «$r0_ptr» γ $$ []
  · iunfold mvcc.writerInv; iexact Hwi
  -- the readers' pool: every slot of the index's lock in (D22 receiver epochs, S4)
  -- (S5a) each slot with a reader token of the backend
  ihave Hslots := mvcc.idxSlots_of γ (⟨GoInterface.ok bi, ti, sc, stopc⟩ : mvcc.StoreObjs) _ $$ [Hird Hrts]
  · iframe Hird Hrts
  imod (inv_alloc mvcc.poolN ⊤ iprop(∃ (p : mvcc.PhysNames) (o : mvcc.StoreObjs),
      mvcc.curAt (γ.withPhys p) (DFrac.own (1 : Qp).half.half.half) o ∗ mvcc.poolBody (γ.withPhys p) o))
    $$ [Htka Htkoa Htkwa Htkra Hslots HcurPool] with #Hpool
  · inext
    iexists γ.phys, _
    rw [mvcc.StoreNames.withPhys_self]
    iframe HcurPool
    iunfold mvcc.poolBody
    iexists mvcc.nReaders, 0, 0, 0
    rw [List.replicate_zero]
    iframe Htka Htkoa Htkwa Htkra Hslots
    isplitl []
    · iapply BigSepL.bigSepL_nil_intro; iempintro
    isplitl []
    · iapply BigSepL.bigSepL_nil_intro; iempintro
    ipureintro; omega
  ihave #Hpool : mvcc.readerPool γ $$ []
  · iunfold mvcc.readerPool; iexact Hpool
  ihave Hcmp2 : («$r0_ptr».[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half •
      DFrac.own (1 : Qp).half} (W64 (-1) : w64) : IProp GF) $$ [compactMainRev]
  · rw [← hsplit]; iexact compactMainRev
  icases ((typedPointsto_dfractional (GF := GF) _ _).dfractional _ _).1 $$ Hcmp2 with ⟨HcmpA, HcmpB⟩
  -- `s.revMu` initialized with the committed log `[[], []]`: the other halves of
  -- `currentRev`, of the committed log and of the bucket's view, the index's certificate, the
  -- other half of `compactMainRev` and the other quarter of its authority
  -- the committed log's authority: `s.revMu`'s fraction, and for a watchable store's the outer
  -- quarter (`logQ`), the caller's (unit W-K)
  ihave Hsplit : mvcc.idxLogAuth γ.idx (mvcc.revQ γ 1) [[], []] ∗
      (if wq then mvcc.logQ γ [[], []] else iprop(True)) $$ [Hil]
  · have hq := (monoListAuthOwn_fractional (GF := GF) γ.idx.log ([[], []] : mvcc.Log)).fractional
      (1 : Qp).half.half (1 : Qp).half.half
    rw [Qp.half_add_half] at hq
    cases wq
    · simp only [mvcc.revQ, hγw, Bool.false_eq_true, ↓reduceIte]; iframe Hil
    · simp only [mvcc.revQ, mvcc.logQ, mvcc.idxLogAuth, hγw, ↓reduceIte]; iapply hq.1 $$ Hil
  icases Hsplit with ⟨Hil, HlogQ⟩
  imod sync.init_RWMutex (mvcc.revMuInv «$r0_ptr» γ) (mvcc.revMuAddr «$r0_ptr»)
    $$ [HcurB Hc2 Hbv2 HauthR Hil HcmpB HcuR HrstR HcurRev] revMu with Hrevs
  · inext
    iapply (mvcc.revMuInv_close «$r0_ptr» γ γ)
    isplitr [HrstR HcurRev]
    rotate_left
    · iunfold mvcc.revMuTok; iframe HrstR; isplitl; · iexists _; iexact HcurRev
      ipureintro; rfl
    iunfold mvcc.revMuBody
    iexists [[], []], 2 ^ 63 - 5, -1
    simp only [named]
    rw [mvcc.bucketMap_init, ← hone]
    iframe HcurB Hc2 Hbv2 HauthR Hil HcmpB HcuR
    iframe #
    isplitl []
    · iunfold mvcc.certOk; ileft; ipureintro; simp
    ipureintro; simp
  icases sync.ownRWMutex_slots_guard _ _ $$ Hrevs with ⟨Hrevs, #Hrevg⟩
  -- the four fields `store.Restore` writes (D22 receiver epochs, S3): half to `s.mu`, the rest to
  -- `restore` (lent), then a quarter each to the right to close and the watchable store's share
  -- what the objects are (D22 receiver epochs, S5b: until then `isStore`'s)
  ihave #Hph : mvcc.physOk «$r0_ptr» γ (⟨GoInterface.ok bi, ti, sc, stopc⟩ : mvcc.StoreObjs) $$ []
  · iunfold mvcc.physOk
    iexists P, Dep
    simp only [named]
    iframe #
  ihave Hfs : mvcc.fieldShareAt «$r0_ptr» γ ((1 : Qp).half + (1 : Qp).half) (⟨GoInterface.ok bi, ti, sc, stopc⟩ : mvcc.StoreObjs)
      $$ [b kvindex fifoSched stopc HrstF HcurF]
  · rw [Qp.half_add_half]
    iunfold mvcc.fieldShareAt
    simp only [named]
    iframe HrstF HcurF Hph
    iunfold mvcc.storeFields
    iframe b kvindex fifoSched stopc
  icases (mvcc.fieldShareAt_split «$r0_ptr» γ _ _ _).1 $$ Hfs with ⟨Hfm, Hfr⟩
  ihave Hfm := mvcc.fieldShare_of_at «$r0_ptr» γ _ _ $$ Hfm
  iunfold mvcc.fieldShareAt at Hfr
  iNamedSuffix Hfr "Q"
  ihave HrstQ := HfrstQ
  iunfold mvcc.storeFields at HfldsQ
  iNamedSuffix HfldsQ "R"
  -- the deferred `s.mu.Unlock()` on private memory; then `s.mu`'s invariant is made
  wp_apply +noauto (plain.wp_Unlock sync.atomic.Int32.wp_Add (mvcc.muAddr «$r0_ptr»)) $$ [$mu] as mu
  imod sync.init_RWMutex (mvcc.muInv «$r0_ptr» γ) (mvcc.muAddr «$r0_ptr») $$ [HcmpA HcuM Hwr Hfm] mu
    with Hmus
  · inext
    iunfold mvcc.muInv
    iexists -1
    iframe Hwr Hfm
    iunfold mvcc.muInvAt
    iframe HcmpA HcuM
    isplitl []
    · iapply mvcc.crevSafe_neg γ (-1) [[], []] (by decide) (by simp) $$ Hcert
    ipureintro; decide
  icases sync.ownRWMutex_slots_guard _ _ $$ Hmus with ⟨Hmus, #Hmug⟩
  (try wp_auto)
  -- the store
  ihave #Hlessor1 : mvcc.isLessor (lease.lessorIface lp) γ.leases $$ []
  · rw [hγl]; iexact Hlessor0
  ihave #Hs : mvcc.isStore «$r0_ptr» γ $$ []
  · iunfold mvcc.isStore
    iexists (lease.lessorIface lp), lg', cfg2, hp
    simp only [named]
    iframe #
    ipureintro; exact ⟨Hlgnn, Hcfg2, Hrb0⟩
  ihave Hok' : (ghostMapAuth γ.cok 1 (∅ : GMap w64 mvcc.Log) : IProp GF) $$ [Hok]
  · rw [hγok]; iexact Hok
  iapply HΦ
  iexists γ
  isplitr
  · ipureintro; refine ⟨hγb, hγl, rfl, hγw, ?_, ?_⟩ <;> first | rfl | assumption
  iframe Hs Hok' Hhook Htoks Hcert HlogQ
  isplitl [ReadView WriteView]
  · iexists rv, wv
    iunfold mvcc.isReadView
    iunfold mvcc.isWriteView
    simp only [named]
    iframe ReadView WriteView
    iframe #
    iunfold mvcc.kvOver; ileft; ipureintro; rfl
  isplitl [Hmus Hrevs Htks]
  · iapply mvcc.storeReaders_of_slots «$r0_ptr» γ
    iframe Hmus Hrevs
    iapply mvcc.ownToks_ones
    iexact Htks
  -- the compaction jobs' queue: the index compactor's token at `-1` beside the scheduler's
  -- queue, whose last name saves the initial `True` (2026-10-13, unit 5c)
  ihave Hcq : mvcc.compactQueue γ (-1) $$ [Hq0 Hcmp0]
  · iunfold mvcc.compactQueue
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
  -- the right to close: the stop channel's close, the scheduler's stop token, the queue (D19m (C))
  -- the rest of the fields: a quarter to the right to close, a quarter to the caller (the
  -- watchable store's share; D22 receiver epochs, S3)
  ihave Hfr : mvcc.fieldShareAt «$r0_ptr» γ ((1 : Qp).half.half + (1 : Qp).half.half) (⟨GoInterface.ok bi, ti, sc, stopc⟩ : mvcc.StoreObjs)
      $$ [HfbR HfidxR HfschR HfstopR HrstQ HcurQ]
  · rw [Qp.half_add_half]
    iunfold mvcc.fieldShareAt
    simp only [named]
    iframe HrstQ HcurQ Hph
    iunfold mvcc.storeFields
    iframe HfbR HfidxR HfschR HfstopR
  icases (mvcc.fieldShareAt_split «$r0_ptr» γ _ _ _).1 $$ Hfr with ⟨Hfc, Hfw⟩
  isplitl [Hstop HsStop Hcq Hfc]
  · iunfold mvcc.storeCloser
    iexists _
    iframe Hcq Hfc
    isplitl []
    · iunfold mvcc.isStopChan; iexists γstop; iexact Hstop0
    isplitl [Hstop]
    · iunfold mvcc.stopCloser; iexists γstop; iexact Hstop
    rw [hγs]; iexact HsStop
  isplitl [Hfw]
  · iapply mvcc.fieldShare_of_at «$r0_ptr» γ _ _; iexact Hfw
  isplitl [Hwsd]
  · iexact Hwsd
  isplitl [HcurFrag]
  · iunfold mvcc.writerFrag; iexists _; iexact HcurFrag
  -- the compaction right's half of the revision's authority at `-1`
  iexact Hright

end proof

end EtcdGrove
end Perennial
