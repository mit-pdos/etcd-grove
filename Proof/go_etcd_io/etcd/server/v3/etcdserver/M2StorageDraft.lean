/-
**M2, the storage side: the server's glue over the Draft** (`notes/m2-storage-plan.md`). Imported by
nothing. What `NewServer` does with the drafted `mvcc.New.specD` (`mvcc/M2StorageDraft.lean`) in
compaction mode, proved against that statement before any proof is switched:

- `server_kv_watchable_ofC`: `server_kv_watchable_of` at a backend record in compaction mode
  (`d.cm = true`), over the compacting bridge (`storeBackend_of_backendC`, the backend's deletable
  keys fixed at the store's, `storeDlReg`), with the compaction's budgets from what the boot holds:
  the compaction keys' values tracked (`fkV`, from `bootBackend_of_newPost`), the safe-range slot
  (`srSlot`, through `mvcc.kbSRM_some`); not the write-back supply, which `New` no longer takes
  (Q1 (a), the user's: the compaction takes it, `store.Compact.specD`). Its post gives what the compacting
  server keeps: the closer and the compaction right's half (`crevRightM`), to make the right after
  `NewServer`'s last error return (`mvcc.compactRight_of_wsCloser`), and the retired count at `1`
  (the job's reader kept back), so the server's two retirements end at `3 = 2 + nJobRd`, which
  `writerOwn` now counts.
- `kbWTSupplyM_of_srvWTPool`: R2-7's conversion, the supply from the server's write budget at the
  boot backend, its part of `E.γbe` discarded (no snapshot is installed in compaction mode): what
  the apply loop's compaction arm hands `store.Compact` (Q1 (a)), after `start` has allocated the
  pool.

The post leaves out `server_kv_watchable_of`'s `txn.isKV` and `txn.kvWriter` (it gives the writer's
`watchWriter` and fragment instead): both are defined over today's `isWatchableStore`, which the
Draft names `isWatchableStoreD`; at the switch the predicate is redefined in place and they follow
as in `server_kv_watchable_of`.
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

/-- **`server_kv_watchable_of` in compaction mode, over the Draft's `New`** (see the file header). -/
theorem server_kv_watchable_ofC
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
    (d : mvcc.KBReal) (hP : mvcc.bridgeParams d.P) (hcm : d.cm = true) (γb γl : GName)
    (Pk : IProp GF) (f : val) (rd0 : GoFunc) (N : Nat) (γi : mvcc.IdxNames) (γok : GName)
    (M : auth.AuthMode)
    (hcfg : mvcc.batchLimitOk cfg.CompactionBatchLimit')
    (hrb : receiptBound GF ≤ 2 ^ 48) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
        backend.isBackend d.γB d.P (mvcc.lateW d.gx) Pk d.be ∗ mvcc.keySized d.γB d.P d.be ∗
        backend.dlInit d.γB ∗ backend.fkV d.γB true ∗
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
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - 1 - 2) (),
          mvcc.watchReader ws st γw) ∗
        mvcc.wsCloser ws st γw.st ∗ mvcc.crevRightM (some d) γw.st ∗ mvcc.retiredAt γw.st 1 ∗
        (∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvcc.rdIs rd ws st γw) ∗ auth.modeTag γw.tag M }} := by
  iintro %Φ ⟨#Hpkg, #Hbpkg, #Hsch, #Hb, #Hsz, Hdl, #Hfv, Hv, Hncmp, Hrg, Hw, Hsr, Hrts, Hlrd,
    #Hle, Hro, Hif, Hok⟩ HΦ
  -- this store compacts: the backend's deletable keys fixed at the store's (`storeDlReg`, over the
  -- index's names `γi`), and its contract the compacting bridge's
  imod backend.dlReg_fix d.γB _ $$ Hdl with #Hreg
  imod auth.modeTag_alloc (GF := GF) M with ⟨%γtag, #Htag⟩
  ihave #Hsb := mvcc.storeBackend_of_backendC hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU
    hrUR hLI hLO hSP hUL hbUR hCB hDel hID hName hSafe hLSR hUSR hUP d hP Pk γb γi $$ []
  · iframe #
    iunfold mvcc.storeDlReg
    iexact Hreg
  rw [show N + 2 = (N + 1) + 1 by omega]
  icases ownToks_add_1 1 (N + 1) d.γB.wb $$ Hw with ⟨Hw, Hw1⟩
  icases ownToks_add_1 1 N d.γB.wb $$ Hw with ⟨Hw, Hw2⟩
  ihave Hsrm := mvcc.kbSRM_some d $$ Hsr
  have hj : mvcc.nJobRd (some d) = 1 := by unfold mvcc.nJobRd; simp [hcm]
  iapply (hNew lg _ le cfg (some d) γb γl Pk f rd0 γi γok γtag hcfg hrb)
    $$ [Hv Hncmp Hrg Hw1 Hw2 Hsrm Hrts Hlrd Hro Hif Hok]
  · iframe Hpkg Hle Hro Hif Hok Hsrm
    isplitr
    · iintro %s %γ %hγ
      iapply Hsb
      ipureintro; exact hγ
    simp only [mvcc.kbView_some, mvcc.kbNoCmp_some, mvcc.kbRegRight_some, mvcc.kbWT_some,
      mvcc.kbRT_some]
    unfold backend.wbTok
    iframe Hv Hncmp Hrg Hw1 Hw2 Hrts Hlrd
  inext
  rw [hj]
  iintro %ws ⟨%st, %γw, %Hγ, #Hws, Hro, #Hhk, Hww, Hwt, Hcok, Hrds, Hcl, Hcr, Hfrag, Hret⟩
  obtain ⟨hb, hl, hk, hi, hc, ht⟩ := Hγ
  ihave #Hws' := Hws
  iunfold mvcc.isWatchableStoreD at Hws'
  icases Hws' with ⟨%vc, %stc, %rv, %γv, Hws'⟩
  iNamed Hws'
  iapply HΦ
  iexists st, γw
  rw [ht]
  iframe Hws Hhk Hww Hfrag Hwt Hcok Hrds Hcl Hcr Hro Hret Htag
  isplitr
  · ipureintro; exact ⟨hb, hl, hk, hi, hc⟩
  isplitr
  · iexists rv
    iframe Hrv
    iunfold mvcc.isReadView
    iexists _
    iframe Hrvkv Hs
    iunfold mvcc.kvOver; iright; iexists ws; iframe Hst; ipureintro; rfl
  unfold txn.storeWTs
  rw [hk]
  iexact Hw

/-- **After `NewServer`'s last error return, the compaction right** (the drafted `NewServer`
step): the store's closer, kept until the transport's `Start` succeeded (Go's deferred
`kv.Close()` closes the store on any earlier error), and the authority's half make the right at
`-1` and `storeStop`, for the apply thread's `store.Compact`. -/
theorem newServer_compactRight (ws st : Loc) (d : mvcc.KBReal) (hcm : d.cm = true)
    (γs : mvcc.StoreNames) :
    mvcc.wsCloser (GF := GF) ws st γs ∗ mvcc.crevRightM (some d) γs ==∗
      mvcc.compactRight γs (-1) ∗ mvcc.storeStop st γs :=
  mvcc.compactRight_of_wsCloser ws st (some d) γs (by unfold mvcc.kbCmpM; exact hcm)

end draft

end EtcdGrove
end Perennial
