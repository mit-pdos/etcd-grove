/-
**mvcc's store over the real backend** (unit 5): `NewStore` and `store.Write` stated over the
backend's proved contract (`isBackend`, through the bridge `storeBackend_of_backend`) instead of
mvcc's assumed one. Lean-first; `notes/decisions.md`, "The store over the real backend (unit 5)".

The store is of the real instance `d` (`StoreNames.kb = some d`): its view of the `Key` bucket is
the backend's clients' view (`bkView d.γB`), its reader slots carry a reader's slot of the
backend and a share of it open (`bkRTx`), its writes spend a write-back's budget (`wbTok`), its
puts meet the safe-range condition (`keyPutOk`: proved of mvcc's revision keys,
`storePutOk_next`), and the backend's batch lock holds the store's writer's resource through the
late-bound `lateW d.gx`, registered by `NewStore`'s first `Unlock`. The other mvcc results are
generic in the instance: at `γ.kb = some d` they are over the real backend. The compaction's
(units 5a-5c) are not: they need a backend that supports it (`storeCmp`, false of the real
instance: its model forbids deleting from the safe-range `Key` bucket; `notes/decisions.md`, "The
compaction over the real backend"), so a store of the real instance is used frozen
(`compactRight_freeze`, `storeReaders_of`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewStore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Write
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ReaderSpecs

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
variable [go_etcd_io.etcd.cache.v3.Assumptions]
variable [backend_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- **`NewStore` over the real backend**: on a fresh backend made for the real instance `d`
(`isBackend d.γB d.P (lateW d.gx) Pk d.be`, with schema's buckets, its post-lock hook `f` set
for good, and the size premise `keySized` of its range reads), given what the backend's creator
holds (the clients' view of the empty `Key` bucket, the right to register the store's lock
resource, two write-back tokens, one reader token per reader slot), and a batch limit not
negative, on a backend that records no compaction (`bkNoCmp`, D19l (v) (A), D22 S-g), `NewStore`
returns a store of that instance (with the right to close it, holding the scheduler's stop token,
and the compaction right's half of the revision's authority: D19m (C)). In compaction mode (`d.cm`,
question 5's core stage) the creator also gives the backend's safe-range slot (`kbSRM`, from
`newPost`'s `srSlot`) and the
compaction keys' values tracked (`fkV d.γB true`, from `newPost`'s `fkCl`), and gets one reader fewer
(`nJobRd`: the compaction job's, kept back; the pool's retired count starts there, `retiredAt`,
whose half lets the creator retire a reader for its own reader token: Probe P2, 2026-10-30); the store registers its deletable keys in the backend
(`storeDlReg`) and its contract has the compaction (`storeCmp`, part (4): the new bridge,
`storeBackend_of_backendC`); the write-back supply is `store.Compact`'s (M2's Q1 (a)). Otherwise
the slot is `True` (`cmOff_res`), the
registration is "nothing deletable" (`dlNoDel`) and the contract the old bridge's. -/
theorem mvcc.NewStore_backend
    (hNewStore : mvcc.NewStore.spec (GF := GF) (hG := hG))
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
    (lg : Loc) (le : GoInterface) (cfg : StoreConfig) (d : mvcc.KBReal)
    (hP : mvcc.bridgeParams d.P) (γb γl : GName) (Pk : IProp GF) (f : GoFunc)
    (hf : f ≠ func.nil) (rd0 : GoFunc) (hcfg : mvcc.batchLimitOk cfg.CompactionBatchLimit')
    (hrb : receiptBound GF ≤ 2 ^ 48) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
        backend.isBackend d.γB d.P (mvcc.lateW d.gx) Pk d.be ∗ backend.plHookRO d.γB f ∗
        mvcc.keySized d.γB d.P d.be ∗
        -- (the backend-compaction stage) the deletable-keys registration, unfixed: the store fixes it
        -- by its compaction mode (`dlNoDel`, or the store's deletable keys, `storeDlReg`)
        backend.dlInit d.γB ∗
        -- (question 5's core stage, part (4)) in compaction mode, the compaction keys' values tracked
        -- (the backend's constructor's `fkCl`)
        □ (⌜d.cm = true⌝ -∗ backend.fkV d.γB true) ∗
        mvcc.bkView d.γB 1 (∅ : mvcc.Bucket) ∗ mvcc.bkNoCmp d.γB ∗ mvcc.lateReg d.gx ∗
        backend.wbTok d.γB ∗ backend.wbTok d.γB ∗ mvcc.kbSRM (some d) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          mvcc.bkRTx d.γB d.P d.be) ∗
        lease.lessorRdOf γl ∗ mvcc.isLessor le γl ∗ lease.rdOwn γl rd0 }}
      (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewStore)) (Val #lg))
        (Val #(interface.mkOk
          (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be)))
        (Val #le)) (Val #cfg))
    {{ (s : Loc), RET #s; ∃ γ : mvcc.StoreNames,
        ⌜γ.bucket = γb ∧ γ.leases = γl ∧ γ.kb = some d ∧ γ.watchQ = false⌝ ∗
        mvcc.isStore s γ ∗ (∃ rd : GoFunc, lease.rdOwn γl rd) ∗ ghostMapAuth γ.cok 1 (∅ : GMap w64 mvcc.Log) ∗ mvcc.hookIs γ Pk #f ∗
        (∃ rv wv : Loc,
          s.[store, go!"ReadView"] ↦
            (interface.mkOk (go.GoType.PointerType readView.ty) #rv : GoInterface) ∗
          mvcc.isReadView rv s γ ∗
          s.[store, go!"WriteView"] ↦
            (interface.mkOk (go.GoType.PointerType writeView.ty) #wv : GoInterface) ∗
          mvcc.isWriteView wv s γ) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - mvcc.nJobRd (some d)) (),
          mvcc.storeReaderC s γ) ∗
        ownToks γ.revs (2 ^ 63 - 5) ∗ mvcc.idxCert γ.idx [[], []] ∗ mvcc.storeCloser s γ ∗
        mvcc.fieldShare s γ (1 : Qp).half.half ∗ mvcc.crevUB γ.idx (1 : Qp).half (-1) ∗
        mvcc.retiredAt γ (mvcc.nJobRd (some d)) }} := by
  iintro %Φ ⟨#Hpkg, #Hbpkg, #Hsch, #Hb, #Hhk, #Hsz, Hdl, #Hfv, Hv, Hncmp, Hrg, Hw1, Hw2, Hsrm, Hrts, Hlrd, #Hle, Hro⟩ HΦ
  -- the index's names and the certificate map, fresh (D13a: `NewStore` takes them)
  imod mvcc.idxFresh_alloc (GF := GF) with ⟨%γi, Hifresh⟩
  -- the deletable keys fixed by the mode (question 5's core stage, part (4)): a compacting store's
  -- (`storeDlReg`, over the index's names), and its contract with the compaction (the new bridge);
  -- else nothing deletable (`dlNoDel`) and the old bridge
  ihave Hbk : iprop(|==> □ ∀ (s : Loc) (γ : mvcc.StoreNames), ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
      mvcc.storeBackend (interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be) s γ Pk) $$ [Hdl]
  · cases hc : d.cm with
    | false =>
      imod backend.dlNoDel_fix d.γB $$ Hdl with #Hnd
      ihave #Hbk := mvcc.storeBackend_of_backend hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU
        hrUR hLI hLO hSP hUL hbUR hCB hDel hID hName hSafe d hP hc Pk γb $$ [$Hbpkg $Hsch $Hb $Hsz $Hnd]
      imodintro
      iintro !> %s %γ %hγ
      iapply Hbk
      ipureintro; exact ⟨hγ.1, hγ.2.1⟩
    | true =>
      imod backend.dlReg_fix d.γB _ $$ Hdl with #Hreg
      ihave #Hfv' := Hfv $$ [] 
      · ipureintro; first | exact hc | rfl
      imodintro
      iintro !>
      iapply mvcc.storeBackend_of_backendC hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU
        hrUR hLI hLO hSP hUL hbUR hCB hDel hID hName hSafe hLSR hUSR hUP d hP Pk γb γi
      iframe Hbpkg Hsch Hb Hsz Hfv'
      iunfold mvcc.storeDlReg
      iexact Hreg
  imod Hbk with #Hbk
  imod ghost_map_alloc_empty (K := w64) (V := mvcc.Log) (GF := GF) with ⟨%γok, Hok0⟩
  iapply (hNewStore lg _ le cfg (some d) γb γl Pk #f rd0 false γi γok hcfg hrb)
    $$ %Φ [Hv Hncmp Hrg Hw1 Hw2 Hsrm Hrts Hlrd Hro Hifresh Hok0]
  · iframe Hpkg Hle Hro Hifresh Hok0 Hsrm
    isplitr
    · iexact Hbk
    rw [show mvcc.kbView (GF := GF) (some d) γb 1 (∅ : mvcc.Bucket) = mvcc.bkView d.γB 1 ∅ from rfl,
      show mvcc.kbNoCmp (GF := GF) (some d) γb = mvcc.bkNoCmp d.γB from rfl,
      show mvcc.kbRegRight (GF := GF) (some d) = mvcc.lateReg d.gx from rfl,
      show mvcc.kbWT (GF := GF) (some d) = backend.wbTok d.γB from rfl,
      show mvcc.kbRT (GF := GF) (some d) = mvcc.bkRTx d.γB d.P d.be from rfl]
    iframe Hv Hncmp Hrg Hw1 Hw2 Hrts Hlrd
  inext
  iintro %s ⟨%γ, %Hγ, Hs, Hro, Hok, #Hh0, Hv, Hr, Ht, Hc, -, Hcl, Hst, -, Hfrag, Hcr, Hret⟩
  ihave Hh := mvcc.hookIs_of_init γ Pk #f d Hγ.2.2.1 f hf $$ [$Hh0 $Hhk $Hfrag]
  iapply HΦ
  iexists γ
  iframe Hs Hro Hok Hh Hv Hr Ht Hc Hcl Hst Hcr Hret
  ipureintro; exact ⟨Hγ.1, Hγ.2.1, Hγ.2.2.1, Hγ.2.2.2.1⟩

/-- **`store.Write` over the real backend**: the generic `store.Write` at a store of the real
instance `d`, its write token the backend's write-back budget. -/
theorem mvcc.store_Write_backend (hWrite : mvcc.store.Write.spec (GF := GF) (hG := hG))
    (s : Loc) (γ : mvcc.StoreNames) (d : mvcc.KBReal) (hk : γ.kb = some d) (trace : Loc)
    (P Pre Q : IProp GF) (f : val) (te : Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        mvcc.isStore s γ ∗ mvcc.storeReader s γ ∗ mvcc.revToken γ ∗ backend.wbTok d.γB ∗
        ⌜trace ≠ null⌝ ∗ mvcc.hookIs γ P f ∗ Pre ∗
        □ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) ∗ traceutil.ownTrace trace te }}
      (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Write")) (Val #trace))
    {{ (mw : Loc), RET #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw);
        (∃ (ilog : mvcc.Log) (crev : Int),
          mvcc.isTxnWrite mw s γ trace ilog [] (W64 0) (W64 0) (W64 0) crev) ∗
        Q }} := by
  have hWrite := mvcc.store.Write.spec_R hWrite
  have hwt : mvcc.storeWT (GF := GF) γ = backend.wbTok d.γB := by
    unfold mvcc.storeWT mvcc.kbWT; rw [hk]
  rw [← hwt]
  iintro %Φ H HΦ
  iapply (hWrite s γ trace P Pre Q f te) $$ %Φ [H]
  · iexact H
  inext
  iintro %mw ⟨⟨%ilog, %crev, Htx, -⟩, HQ, -⟩
  iapply HΦ
  iframe HQ
  iexists ilog, crev
  iexact Htx

end proof

end EtcdGrove
end Perennial
