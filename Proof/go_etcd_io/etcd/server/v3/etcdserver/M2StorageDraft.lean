/-
**M2, the storage side: the server's glue over the Draft** (`notes/m2-storage-plan.md`; revised
after review round 1, `notes/spec-first-study/m2-storage-review-1.md`). Imported by nothing. What
`NewServer` and the apply thread do with the drafted mvcc statements (`mvcc/M2StorageDraft.lean`),
proved against them before any proof is switched:

- `server_kv_watchable_ofD` (review round 1's S1: one lemma over the backend record `d`, the mode
  `d.cm`, in place of `server_kv_watchable_of` and the round's `server_kv_watchable_ofC`): the
  server's KV from `New.specD` over the backend `d` in either mode: the deletable keys fixed by the
  mode (nothing deletable off, the store's keys on: `storeDlReg`), the compaction keys' values
  tracked when compacting (`□ (⌜d.cm = true⌝ -∗ fkV)`, as `mvcc_NewStore_backend` takes it), the
  safe-range slot in either mode (`mvcc.kbSRM_some`). Its post: the store at `kb = some d`,
  `actualMaxReaders - nJobRd (some d) - 2` watch readers, `retiredAt γ (nJobRd (some d))`, the
  closer and `crevRightM γw.st` (the right made after `NewServer`'s last error return,
  `mvcc.compactRight_of_wsCloser` with `mvcc.kbCmpM_some`; the round's wrapper
  `newServer_compactRight` dropped, S2). It gives `watchWriter`/`writerFrag` in place of today's
  `txn.isKV`/`txn.kvWriter`, which are defined over today's `isWatchableStore` (a Draft artifact:
  at the switch the predicate is redefined in place and they follow as today).
- `kbWTSupplyM_of_srvWTPool`: R2-7's conversion (unchanged).
- **F2, the backend's name frozen in compaction mode** (review round 1's F2, the user's decision;
  D22's predicates, the collaborator's: drafted here only). `srvBeOwnD` is `srvBeOwn` with the
  apply thread's quarter of `E.γbe` discarded when the store compacts (`srvBeFrac`); off, it reads
  as today (`srvBeOwnD_off`). A discarded part forbids any update of `E.γbe` (an update needs the
  whole), which is P4 (no snapshot installed in compaction mode); it is persistent, so the apply
  thread's compaction arm copies it out (`srvBeOwnD_frozen`) for R2-7's conversion
  (`kbWTSupplyM_of_srvBeOwnD`: the supply `store.Compact.specD` takes, closing Q1 (a)'s chain).
  The boot's allocation (`srvBe_allocD`, `NewServer`'s three-way split of `E.γbe`) discards that
  quarter when the backend compacts.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuildLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.M2StorageDraft

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section draft
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **R2-7's conversion** (`notes/backend-cmp-plan.md`, "R2-7, D22's side"): the server's write
budget (`srvWTPool`) at the boot backend `d`, with a discarded part of the current backend's ghost
variable at `d` (persistent: `d` stays the backend for good, as in a server that installs no
snapshot), is the compaction's write-back supply (`kbWTSupplyM`), from the same stock: each
conversion takes a receipt into the pool (`srvWTPool_take_extra_d`). -/
theorem kbWTSupplyM_of_srvWTPool (E : apply.AEnv GF) (γp : GName) (d : mvcc.KBReal) :
    srvWTPool (GF := GF) E γp ∗ dghostVar E.γbe DFrac.discard d ⊢ mvcc.kbWTSupplyM (some d) := by
  iintro ⟨#Hp, #Hg⟩
  unfold mvcc.kbWTSupplyM
  split
  · unfold mvcc.kbWTSupply
    iintro !> Hr
    imod srvWTPool_take_extra_d E γp d _ $$ Hp Hr Hg with ⟨Ht, -⟩
    imodintro
    iexact Ht
  · itrivial

/-- **`server_kv_watchable_of` over the backend record `d`, in either mode** (S1; see the file
header). -/
theorem server_kv_watchable_ofD
    (hNew : mvcc.New.specD (GF := GF) (hG := hG))
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
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (hLSR : backend.backend.LockForSafeRangeDelete.spec (GF := GF) (hG := hG))
    (hUSR : backend.backend.UnlockForSafeRangeDelete.spec (GF := GF) (hG := hG))
    (hUP : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (lg : Loc) (le : GoInterface)
    (cfg : go_etcd_io.etcd.server.v3.storage.mvcc.StoreConfig)
    (d : mvcc.KBReal) (hP : mvcc.bridgeParams d.P) (γb γl : GName)
    (Pk : IProp GF) (f : val) (rd0 : GoFunc) (N : Nat) (γi : mvcc.IdxNames) (γok : GName)
    (M : auth.AuthMode)
    (hcfg : mvcc.batchLimitOk cfg.CompactionBatchLimit')
    (hrb : receiptBound GF ≤ 2 ^ 48) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
        backend.isBackend d.γB d.P (mvcc.lateW d.gx) Pk d.be ∗ mvcc.keySized d.γB d.P d.be ∗
        backend.dlInit d.γB ∗ □ (⌜d.cm = true⌝ -∗ backend.fkV d.γB true) ∗
        mvcc.bkView d.γB 1 (∅ : mvcc.Bucket) ∗ mvcc.bkNoCmp d.γB ∗ mvcc.lateReg d.gx ∗
        ownToks d.γB.wb (N + 2) ∗ backend.srSlot d.be ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          mvcc.bkRTx d.γB d.P d.be) ∗
        lease.lessorRdOf γl ∗ mvcc.isLessor le γl ∗ lease.rdOwn γl rd0 ∗
        mvcc.idxFresh γi ∗ ghostMapAuth γok 1 (∅ : GMap w64 mvcc.Log) }}
      (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.New)) (Val #lg))
        (Val #(interface.mkOk
          (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be)))
        (Val #le)) (Val #cfg))
    {{ (ws : Loc), RET #(interface.mkOk
          (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws);
        ∃ (st : Loc) (γw : mvcc.WsNames),
        ⌜γw.st.bucket = γb ∧ γw.st.leases = γl ∧ γw.st.kb = some d ∧ γw.st.idx = γi ∧
          γw.st.cok = γok⌝ ∗
        (∃ rv : Loc, st.[go_etcd_io.etcd.server.v3.storage.mvcc.store, go!"ReadView"] ↦□
            (interface.mkOk (go.GoType.PointerType
              go_etcd_io.etcd.server.v3.storage.mvcc.readView.ty) #rv : GoInterface) ∗
          mvcc.isReadView rv st γw.st) ∗
        mvcc.hookInit γw.st Pk f ∗ mvcc.watchWriter γw [[], []] ∗ mvcc.writerFrag γw.st ∗
        txn.storeWTs γw.st N ∗ ghostMapAuth γw.st.cok 1 (∅ : GMap w64 mvcc.Log) ∗
        mvcc.isWatchableStoreD ws st γw ∗ mvcc.watchToks γw (2 ^ 63 - 3) ∗
        ([∗list] _x ∈ List.replicate
            (Int.toNat sync.rwmutex.actualMaxReaders - mvcc.nJobRd (some d) - 2) (),
          mvcc.watchReader ws st γw) ∗
        mvcc.wsCloser ws st γw.st ∗ mvcc.crevRightM γw.st ∗
        mvcc.retiredAt γw.st (mvcc.nJobRd (some d)) ∗
        (∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvcc.rdIs rd ws st γw) ∗ auth.modeTag γw.tag M }} := by
  iintro %Φ ⟨#Hpkg, #Hbpkg, #Hsch, #Hb, #Hsz, Hdl, #Hfv, Hv, Hncmp, Hrg, Hw, Hsr, Hrts, Hlrd,
    #Hle, Hro, Hif, Hok⟩ HΦ
  -- the backend's deletable keys fixed by the mode, and the store's contract the bridge's of it
  ihave Hsb : iprop(|==> □ ∀ (s : Loc) (γ : mvcc.StoreNames),
      ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        mvcc.storeBackend (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be) s γ Pk) $$ [Hdl]
  · by_cases hcm : d.cm = true
    · imod mvcc.storeDlReg_fix d.γB γi $$ Hdl with #Hreg
      ihave #Hfk := Hfv $$ %hcm
      ihave #Hsb := mvcc.storeBackend_of_backendC hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL
        hrRU hrUR hLI hLO hSP hUL hbUR hCB hDel hID hName hSafe hLSR hUSR hUP d hP Pk γb γi $$ []
      · iframe #
      imodintro; imodintro
      iexact Hsb
    · have hcm' : d.cm = false := by simpa using hcm
      imod backend.dlNoDel_fix d.γB $$ Hdl with #Hnd
      ihave #Hsb := mvcc.storeBackend_of_backend hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL
        hrRU hrUR hLI hLO hSP hUL hbUR hCB hDel hID hName hSafe d hP hcm' Pk γb $$ []
      · iframe #
      imodintro; imodintro
      iintro %s %γ %hγ
      iapply Hsb
      ipureintro; exact ⟨hγ.1, hγ.2.1⟩
  imod Hsb with #Hsb
  imod auth.modeTag_alloc (GF := GF) M with ⟨%γtag, #Htag⟩
  rw [show N + 2 = (N + 1) + 1 by omega]
  icases ownToks_add_1 1 (N + 1) d.γB.wb $$ Hw with ⟨Hw, Hw1⟩
  icases ownToks_add_1 1 N d.γB.wb $$ Hw with ⟨Hw, Hw2⟩
  ihave Hsrm := mvcc.kbSRM_some d $$ Hsr
  iapply (hNew lg _ le cfg (some d) γb γl Pk f rd0 γi γok γtag hcfg hrb)
    $$ [Hv Hncmp Hrg Hw1 Hw2 Hsrm Hrts Hlrd Hro Hif Hok]
  · iframe Hpkg Hle Hro Hif Hok Hsrm Hsb
    simp only [mvcc.kbView_some, mvcc.kbNoCmp_some, mvcc.kbRegRight_some, mvcc.kbWT_some,
      mvcc.kbRT_some]
    unfold backend.wbTok
    iframe Hv Hncmp Hrg Hw1 Hw2 Hrts Hlrd
  inext
  iintro %ws ⟨%st, %γw, %Hγ, #Hws, Hro, #Hhk, Hww, Hwt, Hcok, Hrds, Hcl, Hcr, Hfrag, Hret⟩
  obtain ⟨hb, hl, hk, hi, hc, ht⟩ := Hγ
  ihave #Hrv := mvcc.isWatchableStoreD_readView ws st γw $$ Hws
  iapply HΦ
  iexists st, γw
  rw [ht]
  iframe Hws Hhk Hww Hfrag Hwt Hcok Hrds Hcl Hcr Hro Hret Htag Hrv
  isplitr
  · ipureintro; exact ⟨hb, hl, hk, hi, hc⟩
  unfold txn.storeWTs
  rw [hk]
  iexact Hw

/-! ## F2: the backend's name frozen in compaction mode (D22's predicates, drafted) -/

/-- **The apply thread's part of `E.γbe`, by the mode** (F2): a quarter, as today, when the store
does not compact; discarded when it does (the name frozen: no snapshot is installed, P4). -/
def srvBeFrac (E : apply.AEnv GF) : DFrac :=
  if mvcc.kbCmpM E.γ.kb then DFrac.discard else DFrac.own (1 : Qp).half.half

/-- **Draft of `srvBeOwn`** (F2; D22's `InvApplier.lean`): the apply thread's part of `E.γbe` at
`srvBeFrac E`; otherwise the same. -/
def srvBeOwnD (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ d : mvcc.KBReal, ⌜E.γ.kb = some d⌝ ∗
    srvBeAddr s ↦{DFrac.own (1 : Qp).half} srvBeIface d.be ∗
    dghostVar E.γbe (srvBeFrac E) d)

/-- Off, the drafted predicate is today's (`srv_be_swap` and the snapshot path read it so). -/
theorem srvBeOwnD_off (s : Loc) (E : apply.AEnv GF) (h : ¬ mvcc.kbCmpM E.γ.kb) :
    srvBeOwnD (GF := GF) s E ⊣⊢ srvBeOwn s E := by
  unfold srvBeOwnD srvBeOwn srvBeFrac
  simp only [h, ↓reduceIte]
  exact .rfl

/-- **The frozen name, copied out** (F2; persistent): in compaction mode the apply thread's part is
a discarded part of `E.γbe` at the store's backend. -/
theorem srvBeOwnD_frozen (s : Loc) (E : apply.AEnv GF) (h : mvcc.kbCmpM E.γ.kb) :
    srvBeOwnD (GF := GF) s E ⊢
      srvBeOwnD s E ∗ ∃ d : mvcc.KBReal, ⌜E.γ.kb = some d⌝ ∗ dghostVar E.γbe DFrac.discard d := by
  unfold srvBeOwnD srvBeFrac
  simp only [h, ↓reduceIte]
  iintro ⟨%d, %Hd, Hbe, #Hg⟩
  isplitl [Hbe]
  · iexists d; iframe Hbe Hg; ipureintro; exact Hd
  iexists d; iframe Hg; ipureintro; exact Hd

/-- **The compaction's supply, at the apply thread** (F2 closing Q1 (a)'s chain): the write budget
and the apply thread's part of `s.be` give `store.Compact.specD`'s `kbWTSupplyM E.γ.kb`, the part
kept. -/
theorem kbWTSupplyM_of_srvBeOwnD (s : Loc) (E : apply.AEnv GF) (γp : GName)
    (h : mvcc.kbCmpM E.γ.kb) :
    srvWTPool (GF := GF) E γp ∗ srvBeOwnD s E ⊢ srvBeOwnD s E ∗ mvcc.kbWTSupplyM E.γ.kb := by
  iintro ⟨#Hp, Hbo⟩
  icases srvBeOwnD_frozen s E h $$ Hbo with ⟨Hbo, %d, %Hd, #Hg⟩
  iframe Hbo
  rw [Hd]
  iapply kbWTSupplyM_of_srvWTPool E γp d $$ [Hp Hg]
  iframe #

/-- **The boot's allocation of `E.γbe`, by the mode** (F2; `NewServer.lean:644-648`'s split): half
for `s.bemu`'s lock invariant (`bemuP`), a quarter for the write budget (`srvWTStock`), and the
apply thread's part at the store's mode (`srvBeFrac`: discarded when compacting). -/
theorem srvBe_allocD (d : mvcc.KBReal) :
    ⊢ |==> ∃ γbe : GName, dghostVar (GF := GF) γbe (DFrac.own (1 : Qp).half) d ∗
      dghostVar γbe (DFrac.own (1 : Qp).half.half) d ∗
      dghostVar γbe (if mvcc.kbCmpM (some d) then DFrac.discard
        else DFrac.own (1 : Qp).half.half) d := by
  imod (dghostVar_alloc (GF := GF) d) with ⟨%γbe, Hγbe⟩
  icases (dghostVar_split (GF := GF) γbe d (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half))
    $$ [Hγbe] with ⟨Hγbm, Hγbe⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hγbe
  icases (dghostVar_split (GF := GF) γbe d (DFrac.own (1 : Qp).half.half)
      (DFrac.own (1 : Qp).half.half)) $$ [Hγbe] with ⟨HγbW, HγbA⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hγbe
  iexists γbe
  iframe Hγbm HγbW
  by_cases h : mvcc.kbCmpM (some d)
  · simp only [h, ↓reduceIte]
    iapply dghostVar_persist γbe _ d $$ HγbA
  · simp only [h, ↓reduceIte]
    imodintro; iexact HγbA

end draft

end EtcdGrove
end Perennial
