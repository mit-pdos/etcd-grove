/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.New
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newWatchableStore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__syncWatchersLoop
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__syncVictimsLoop
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.NewWatchableLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiLemmas

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

/-- Two of the reader slots out of `n ≥ 2`. -/
theorem mvcc.slots_take2 (Q : IProp GF) (n : Nat) (h : 2 ≤ n) :
    ([∗list] _x ∈ List.replicate n (), Q) ⊢
      Q ∗ Q ∗ [∗list] _x ∈ List.replicate (n - 2) (), Q := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 2 = m by omega, List.replicate_succ, List.replicate_succ]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H2, H⟩
  iframe

theorem mvcc.New.wp_proofA
    (hNew : mvcc.newWatchableStore.spec (GF := GF) (hG := hG))
    (hSWL : mvcc.watchableStore.syncWatchersLoop.spec (GF := GF) (hG := hG))
    (hSVL : mvcc.watchableStore.syncVictimsLoop.spec (GF := GF) (hG := hG)) :
    mvcc.New.specA (GF := GF) (hG := hG) := by
  intro lg b le cfg kb γb γl P f rd0 γi γok γtag aq Hcfg0 Hrb0
  wp_start as ⟨Hbk, Hbv, Hncmp, Hrg, Hwt1, Hwt2, Hsrm, Hrts, Hlrd, #Hlessor, Hro, Hifresh, Hok0⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply (hNew _ _ _ _ _ _ _ _ f _ γi γok γtag aq Hcfg0 Hrb0)
    $$ [$Hbk $Hbv $Hncmp $Hrg $Hwt1 $Hwt2 $Hsrm $Hrts $Hlrd $Hlessor $Hro $Hifresh $Hok0]
    as %s ⟨%st, %γ, %Hγ, #Hws, Hro, #Hhook, Hww, Htw, Hok, Hreaders,
    ⟨%stc, #Hstc, Hstop⟩, Hsclose, Hcr, Hfrag, Hret, Hwg⟩
  (try wp_auto)
  imod sync.init_WaitGroup mvcc.wsWgWGN (mvcc.wsWgAddr s) $$ Hwg with ⟨%γwg, #HisWg, Hctr, Hwaiters⟩
  wp_apply mvcc.wp_wsWg_Add2_init s γwg $$ [$Hctr $Hwaiters] as ⟨Hctr, Hwaiters⟩
  · iframe #
  imod ownTokAuth_alloc (GF := GF) with ⟨%γd, Hauth⟩
  imod ownTokAuth_add 2 γd 0 $$ Hauth with ⟨Hauth, Hdone⟩
  icases (ownToks_add 1 1 γd).1 $$ Hdone with ⟨Hd1, Hd2⟩
  imod inv_alloc mvcc.wsWgN ⊤ (mvcc.wsWgInv γwg γd) $$ [Hctr Hauth] with #Hinv
  · inext
    iunfold mvcc.wsWgInv
    iexists W32 2, 0 + 2
    iframe Hctr Hauth
    ipureintro; decide
  have hN : 2 ≤ Int.toNat sync.rwmutex.actualMaxReaders - mvcc.nJobRd kb := by
    have h3 : 3 ≤ Int.toNat sync.rwmutex.actualMaxReaders := by
      rw [sync.rwmutex.actualMaxReaders_unseal]; decide
    have := mvcc.nJobRd_le kb
    omega
  icases mvcc.slots_take2 _ _ hN $$ Hreaders with ⟨Hr1, Hr2, Hreaders⟩
  (try wp_auto)
  wp_apply wp_fork $$ [Hr1 Hd1]
  · wp_apply hSWL s st γ $$ [$Hws $Hr1 Hd1]
    · iunfold mvcc.wsDone
      iexists γwg, γd
      iframe HisWg Hinv Hd1
    itrivial
  (try wp_auto)
  wp_apply wp_fork $$ [Hr2 Hd2]
  · wp_apply hSVL s st γ $$ [$Hws $Hr2 Hd2]
    · iunfold mvcc.wsDone
      iexists γwg, γd
      iframe HisWg Hinv Hd2
    itrivial
  (try wp_auto)
  iapply HΦ
  iexists st, γ
  iframe Hws Hro Hhook Hww Htw Hok Hreaders Hcr Hfrag Hret
  isplitr
  · ipureintro; exact Hγ
  iunfold mvcc.wsCloser
  iexists stc
  iframe Hstc Hstop Hsclose
  iunfold mvcc.wsWaiter
  iexists γwg, γd
  iframe HisWg Hinv Hwaiters

/-- **`New` in the old mode**: `specA` at `aq = false`. -/
theorem mvcc.New.wp_proof
    (hNew : mvcc.newWatchableStore.spec (GF := GF) (hG := hG))
    (hSWL : mvcc.watchableStore.syncWatchersLoop.spec (GF := GF) (hG := hG))
    (hSVL : mvcc.watchableStore.syncVictimsLoop.spec (GF := GF) (hG := hG)) :
    mvcc.New.spec (GF := GF) (hG := hG) := by
  intro lg b le cfg kb γb γl P f rd0 γi γok γtag Hcfg0 Hrb0
  iintro %Φ Hpre HΦ
  iapply (mvcc.New.wp_proofA hNew hSWL hSVL lg b le cfg kb γb γl P f rd0 γi γok γtag false Hcfg0 Hrb0)
    $$ %Φ Hpre
  inext
  iintro %s ⟨%st, %γ, %Hγ, Hrest⟩
  iapply HΦ
  iexists st, γ
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := Hγ
  isplitr
  · ipureintro; exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  simp only [Bool.false_eq_true, ↓reduceIte]
  iexact Hrest

section candidate
variable [go_etcd_io.etcd.cache.v3.Assumptions]
variable [backend_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- **The candidate `New`** (`specC`, mvcc's candidate API): `specA`'s in the abstract mode over the
real backend (its contract by the bridge, `storeBackend_of_backend`, nothing deletable: the backend
does not compact), the index's names and the certificate map fresh; of what it returns, the readers'
pool (the watchable store's readers, `poolR`), the revision tokens' and the watch tokens' pools (from
the writer's and the watch budget), the pin of the store's objects (the writer's fragment, made
persistent), the client's state at `mvccStart` (the writer's halves of the abstract log and the
pending revision, its certificate and half of the watchers' log), the open token (its invariant
holding the closer) and the range deleter. -/
theorem mvcc.New.wp_proofC
    (hNA : mvcc.New.specA (GF := GF) (hG := hG))
    (hCRT : backend.backend.ConcurrentReadTx.spec (GF := GF) (hG := hG))
    (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hFC : backend.backend.ForceCommit.spec (GF := GF) (hG := hG))
    (hSz : backend.backend.Size.spec (GF := GF) (hG := hG))
    (hSzU : backend.backend.SizeInUse.spec (GF := GF) (hG := hG))
    (hcRL : backend.concurrentReadTx.RLock.spec (GF := GF) (hG := hG))
    (hcRU : backend.concurrentReadTx.RUnlock.spec (GF := GF) (hG := hG))
    (hcUR : backend.concurrentReadTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hrRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hrRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hrUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hLI : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG))
    (hLO : backend.batchTxBuffered.LockOutsideApply.spec (GF := GF) (hG := hG))
    (hSP : backend.batchTxBuffered.UnsafeSeqPut.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hbUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hCB : backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG))
    (hDel : backend.batchTxBuffered.UnsafeDelete.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG)) :
    mvcc.New.specC (GF := GF) (hG := hG) := by
  intro lg le cfg d Pk γl rd0 hcfg hrb hth hP hcm
  iintro %Φ ⟨#Hpkg, #Hbpkg, #Hsch, #Hb, #Hsz, Hv, Hncmp, Hrg, Hdl, Hw1, Hw2, #Hwb, Hrts, Hlrd,
    #Hle, Hro⟩ HΦ
  obtain ⟨hnc, hnj, -, -, hsrm⟩ := mvcc.cmOff_res (GF := GF) d hcm
  imod mvcc.idxFresh_alloc (GF := GF) with ⟨%γi, Hifresh⟩
  imod backend.dlNoDel_fix d.γB $$ Hdl with #Hnd
  ihave #Hbk := mvcc.storeBackend_of_backend hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU
    hrUR hLI hLO hSP hUL hbUR hCB hDel hID hName hSafe d hP hcm Pk γl $$ [$Hbpkg $Hsch $Hb $Hsz $Hnd]
  imod ghost_map_alloc_empty (K := w64) (V := mvcc.Log) (GF := GF) with ⟨%γok, Hok0⟩
  iapply wp_fupd
  wp_apply (hNA lg _ le cfg (some d) γl γl Pk #func.nil rd0 γi γok γl true hcfg hrb)
    $$ [Hv Hncmp Hrg Hw1 Hw2 Hrts Hlrd Hro Hifresh Hok0] as %s ⟨%st, %γ, %Hγ, #Hws, ⟨%rd, Hro, Hrd⟩,
      #Hhook, Hww, Htw, Hok, Hreaders, Hcl, -, Hab, -⟩
  · iframe Hle Hro Hifresh Hok0
    isplitr
    · iintro %s %γ %hγ
      iapply Hbk
      ipureintro; exact ⟨hγ.1, hγ.2.1⟩
    rw [show mvcc.kbView (GF := GF) (some d) γl 1 (∅ : mvcc.Bucket) = mvcc.bkView d.γB 1 ∅ from rfl,
      show mvcc.kbNoCmp (GF := GF) (some d) γl = mvcc.bkNoCmp d.γB from rfl,
      show mvcc.kbRegRight (GF := GF) (some d) = mvcc.lateReg d.gx from rfl,
      show mvcc.kbWT (GF := GF) (some d) = backend.wbTok d.γB from rfl,
      show mvcc.kbRT (GF := GF) (some d) = mvcc.bkRTx d.γB d.P d.be from rfl]
    iframe Hv Hncmp Hrg Hw1 Hw2 Hrts Hlrd
    iapply hsrm.2; itrivial
  obtain ⟨hb, hl, hkb, hi, hcok, -, hcm', habs⟩ := Hγ
  have hcmf : γ.st.cm = false := by rw [hcm']; exact decide_eq_false hnc
  -- the pin of the store's objects: the writer's fragment, persistent
  icases Hab with ⟨Hfa, Hab, Hpn⟩
  iunfold mvcc.writerFragA at Hfa
  icases Hfa with ⟨%o, Hfa⟩
  iunfold mvcc.curAt at Hfa
  imod dghostVar_persist γ.st.cur _ _ $$ Hfa with #Hpin
  ihave #Hws1 := Hws
  iunfold mvcc.isWatchableStore at Hws1
  iNamed Hws1
  iunfold mvcc.watchWriter at Hww
  icases Hww with ⟨#Hc0, Hrevs, Hwl⟩
  -- the readers' pool, of the watchable store's readers
  have hmr : Int.toNat sync.rwmutex.actualMaxReaders = 2 ^ 30 - 1 := by
    rw [sync.rwmutex.actualMaxReaders_unseal]; decide
  have hn : threadBound GF ≤ (Int.toNat sync.rwmutex.actualMaxReaders - mvcc.nJobRd (some d) - 2) + 1 := by
    rw [hnj, hmr]; omega
  imod threadPool.init mvcc.tixN (mvcc.watchReader s st γ) ⊤ _ hn $$ Hreaders with ⟨%γt, #Hpool⟩
  -- the revision tokens' pool and the watch tokens' pool
  imod receipt_zero (GF := GF) with H0
  imod receipt_zero (GF := GF) with H1
  imod inv_alloc mvcc.revPoolN ⊤ iprop(∃ (a n : Nat), ⧗ a ∗ ownToks γ.st.revs n ∗
      ⌜receiptBound GF ≤ a + n + 1⌝) $$ [H0 Hrevs] with #Hrev
  · inext; iexists 0, mvcc.wBudget [[], []]; iframe H0 Hrevs; ipureintro; unfold mvcc.wBudget; simp; omega
  imod inv_alloc mvcc.wtPoolN ⊤ iprop(∃ (a n : Nat), ⧗ a ∗ mvcc.watchToks γ n ∗
      ⌜receiptBound GF ≤ a + n + 1⌝) $$ [H1 Htw] with #Hwtp
  · inext; iexists 0, 2 ^ 63 - 3; iframe H1 Htw; ipureintro; omega
  -- the open token, its invariant holding the closer
  imod ghostVar_alloc (GF := GF) () with ⟨%γo, Hop⟩
  imod inv_alloc mvcc.mvccOpenN ⊤ iprop(ghostVar γo 1 () ∨
      (∃ c : Int, mvcc.wsCloserM s st γ.st c)) $$ [Hcl] with #Hopi
  · inext; iright; iexists (-1)
    iapply (mvcc.wsCloserM_off s st γ.st (-1) (by rw [hkb]; exact hnc)).2
    iexact Hcl
  have hpr : mvcc.poolR (GF := GF) st
      ({ ws := γ, tl := γt, watched := true, wl := s, sl := st, op := γo } : mvcc.MvccImpl) =
      mvcc.watchReader s st γ := rfl
  have hwt : mvcc.storeWT (GF := GF) γ.st = backend.wbTok d.γB := by
    unfold mvcc.storeWT mvcc.kbWT; rw [hkb]
  imodintro
  iapply HΦ
  iexists ({ ws := γ, tl := γt, watched := true, wl := s, sl := st, op := γo } : mvcc.MvccImpl)
  isplitr
  · ipureintro
    refine ⟨hl, ?_⟩
    unfold mvcc.mvccBackend
    simp only [mvcc.MvccImpl.st, hkb]
  isplitr
  · iunfold mvcc.isWatchableMvcc
    iunfold mvcc.isWatchableMvccI
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iexists st
    iframe Hws
    iunfold mvcc.isMvccI
    simp only [mvcc.MvccImpl.st, ↓reduceIte]
    rw [hpr, hwt]
    iframe Hs Hpool Hfrz
    isplitr
    · ipureintro; exact ⟨habs, Hwq, ⟨d, hkb⟩, by omega, trivial⟩
    isplitr
    · iexists o; iunfold mvcc.curAt; iexact Hpin
    isplitr
    · iunfold mvcc.revPool; iexact Hrev
    isplitr
    · iexact Hwb
    isplitr
    · iunfold mvcc.wtPool; iexact Hwtp
    iexact Hws
  isplitl [Hab Hpn Hok Hwl]
  · iunfold mvcc.mvccState
    iunfold mvcc.mvccStateI
    simp only [mvcc.MvccImpl.st, mvcc.mvccStart, hcmf, Bool.false_eq_true, ↓reduceIte]
    iframe Hab Hpn Hc0 Hwl
    isplitl [Hok]
    · iexists ∅; iframe Hok; ipureintro
      intro n l h; simp at h
    isplitr
    · iintro !> %x %hx; cases hx
    ipureintro; exact ⟨mvcc.MvccReachable.start, by simp⟩
  isplitr
  · iunfold mvcc.mvccBackendIs
    iunfold mvcc.mvccBackendIsI
    iexists d, (mvcc.lateW d.gx)
    isplitr
    · ipureintro; exact ⟨hkb, rfl, rfl⟩
    iframe Hb
    iunfold mvcc.hookInit at Hhook
    icases Hhook with ⟨#HP, -⟩
    iexact HP
  isplitl [Hop]
  · iunfold mvcc.mvccOpen
    iunfold mvcc.mvccOpenI
    simp only [↓reduceIte]
    iframe Hop Hopi
  iexists rd
  iframe Hro
  iunfold mvcc.mvccDeleter
  iunfold mvcc.mvccDeleterI
  simp only [↓reduceIte]
  iexact Hrd

end candidate

end proof

end EtcdGrove
end Perennial
