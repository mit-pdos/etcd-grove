/-
**What `NewServer`'s proof uses of the server's results, from the callees' specs** (unit N4,
2026-10-17: the import cycle broken). `etcdserver/Results.lean` imports the server's `Link.lean`,
which imports `NewServer`'s proof; so the bridges `NewServer` needs -- the backend over the
server's hooks (`backend_server_hooks`) and the server's KV from `mvcc.New`
(`server_kv_watchable`) -- are stated here with the specs they use as hypotheses, and
`Results.lean` instantiates them with the linked results. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.New
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.KVWrite
public import Proof.go_etcd_io.etcd.server.v3.auth.ModeTag
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InstanceLaws

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.cindex

section backend
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The real backend's facts of the instance `d` are those of `d` not compacting (question 5's core
stage, part (1): the server's store at `{ d with cm := false }`). -/
theorem isBackend_cmOff (d : mvcc.KBReal) (Pk : IProp GF) :
    backend.isBackend (GF := GF) d.γB d.P (mvcc.lateW d.gx) Pk d.be ⊢
      backend.isBackend ({ d with cm := false } : mvcc.KBReal).γB ({ d with cm := false } : mvcc.KBReal).P (mvcc.lateW ({ d with cm := false } : mvcc.KBReal).gx) Pk ({ d with cm := false } : mvcc.KBReal).be := by
  exact .rfl

theorem plHookRO_cmOff (d : mvcc.KBReal) (f : GoFunc) :
    backend.plHookRO (GF := GF) d.γB f ⊢ backend.plHookRO ({ d with cm := false } : mvcc.KBReal).γB f := by
  exact .rfl

theorem keySized_cmOff (d : mvcc.KBReal) :
    (□ ∀ (γB : backend.BNames) (b : Loc), mvcc.keySized (GF := GF) γB d.P b) ⊢
      □ ∀ (γB : backend.BNames) (b : Loc),
        mvcc.keySized γB ({ d with cm := false } : mvcc.KBReal).P b := by
  exact .rfl

/-- The same facts at the instance in either mode (`{ d with cm := c }`: M2's server). -/
theorem isBackend_withCm (d : mvcc.KBReal) (c : Bool) (Pk : IProp GF) :
    backend.isBackend (GF := GF) d.γB d.P (mvcc.lateW d.gx) Pk d.be ⊢
      backend.isBackend ({ d with cm := c } : mvcc.KBReal).γB ({ d with cm := c } : mvcc.KBReal).P
        (mvcc.lateW ({ d with cm := c } : mvcc.KBReal).gx) Pk ({ d with cm := c } : mvcc.KBReal).be := by
  exact .rfl

theorem plHookRO_withCm (d : mvcc.KBReal) (c : Bool) (f : GoFunc) :
    backend.plHookRO (GF := GF) d.γB f ⊢ backend.plHookRO ({ d with cm := c } : mvcc.KBReal).γB f := by
  exact .rfl

theorem keySized_withCm (d : mvcc.KBReal) (c : Bool) :
    (□ ∀ (γB : backend.BNames) (b : Loc), mvcc.keySized (GF := GF) γB d.P b) ⊢
      □ ∀ (γB : backend.BNames) (b : Loc),
        mvcc.keySized γB ({ d with cm := c } : mvcc.KBReal).P b := by
  exact .rfl

/-- `server_kv_watchable` (`Results.lean`) from the specs it uses. -/
theorem server_kv_watchable_of
    (hNew : mvcc.New.spec (GF := GF) (hG := hG))
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
    (lg : Loc) (le : GoInterface)
    (cfg : go_etcd_io.etcd.server.v3.storage.mvcc.StoreConfig)
    (d : mvcc.KBReal) (hP : mvcc.bridgeParams d.P) (γb γl : GName) (Pk : IProp GF) (f : val)
    (rd0 : GoFunc) (N : Nat) (γi : mvcc.IdxNames) (γok : GName) (M : auth.AuthMode)
    (hcfg : mvcc.batchLimitOk cfg.CompactionBatchLimit')
    (hrb : receiptBound GF ≤ 2 ^ 48) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
        backend.isBackend d.γB d.P (mvcc.lateW d.gx) Pk d.be ∗ mvcc.keySized d.γB d.P d.be ∗
        -- (the backend-compaction stage) the deletable-keys registration, unfixed: the store fixes it
        -- where its compaction mode is chosen (today's stores never compact: `dlNoDel`)
        backend.dlInit d.γB ∗
        mvcc.bkView d.γB 1 (∅ : mvcc.Bucket) ∗ mvcc.bkNoCmp d.γB ∗ mvcc.lateReg d.gx ∗
        ownToks d.γB.wb (N + 2) ∗
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
        ⌜γw.st.bucket = γb ∧ γw.st.leases = γl ∧ γw.st.kb = some ({ d with cm := false } : mvcc.KBReal) ∧ γw.st.idx = γi ∧
          γw.st.cok = γok ∧ γw.st.cm = false⌝ ∗
        txn.isKV (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws) st γw.st ∗
        (∃ rv : Loc, st.[go_etcd_io.etcd.server.v3.storage.mvcc.store, go!"ReadView"] ↦□
            (interface.mkOk (go.GoType.PointerType
              go_etcd_io.etcd.server.v3.storage.mvcc.readView.ty) #rv : GoInterface) ∗
          mvcc.isReadView rv st γw.st) ∗
        mvcc.hookInit γw.st Pk f ∗ txn.kvWriter st γw.st [[], []] ∗ txn.storeWTs γw.st N ∗
        ghostMapAuth γw.st.cok 1 (∅ : GMap w64 mvcc.Log) ∗
        mvcc.isWatchableStore ws st γw ∗ mvcc.watchToks γw (2 ^ 63 - 3) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - 2) (),
          mvcc.watchReader ws st γw) ∗
        mvcc.wsCloser ws st γw.st ∗ mvcc.retiredAt γw.st 0 ∗ (∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvcc.rdIs rd ws st γw) ∗ auth.modeTag γw.tag M }} := by
  iintro %Φ ⟨#Hpkg, #Hbpkg, #Hsch, #Hb, #Hsz, Hdl, Hv, Hncmp, Hrg, Hw, Hrts, Hlrd, #Hle, Hro, Hif, Hok⟩ HΦ
  -- this store never compacts: the registration fixed at "nothing deletable"
  imod backend.dlNoDel_fix d.γB $$ Hdl with #Hnd
  -- the auth mode's tag (the auth plan's A4): the store's owner tag names the mode `M`
  imod auth.modeTag_alloc (GF := GF) M with ⟨%γtag, #Htag⟩
  -- (question 5's core stage, part (1)) the store over the backend's instance not compacting,
  -- `{ d with cm := false }` (M2 turns the server's compaction on), whose backend is `d`'s: no slot,
  -- no supply, no reader kept back (`cmOff_res`)
  ihave #Hsb := mvcc.storeBackend_of_backend hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU
    hrUR hLI hLO hSP hUL hbUR hCB hDel hID hName hSafe ({ d with cm := false } : mvcc.KBReal) hP rfl Pk γb $$ []
  · simp only [mvcc.KBReal.P_withCm]; iframe #
  rw [show N + 2 = (N + 1) + 1 by omega]
  icases ownToks_add_1 1 (N + 1) d.γB.wb $$ Hw with ⟨Hw, Hw1⟩
  icases ownToks_add_1 1 N d.γB.wb $$ Hw with ⟨Hw, Hw2⟩
  obtain ⟨-, hj, -, -, hsr⟩ := mvcc.cmOff_res (GF := GF) ({ d with cm := false } : mvcc.KBReal) rfl
  ihave Hsrm : mvcc.kbSRM (GF := GF) (some ({ d with cm := false } : mvcc.KBReal)) $$ []
  · iapply hsr.2; itrivial
  iapply (hNew lg _ le cfg (some ({ d with cm := false } : mvcc.KBReal)) γb γl Pk f rd0 γi γok γtag hcfg hrb)
    $$ [Hv Hncmp Hrg Hw1 Hw2 Hsrm Hrts Hlrd Hro Hif Hok]
  · iframe Hpkg Hle Hro Hif Hok Hsrm
    isplitr
    · iintro %s %γ %hγ
      iapply Hsb
      ipureintro; exact ⟨hγ.1, hγ.2.1⟩
    simp only [mvcc.kbView_some, mvcc.kbNoCmp_some, mvcc.kbRegRight_some, mvcc.kbWT_some,
      mvcc.kbRT_some, mvcc.KBReal.P_withCm]
    unfold backend.wbTok
    iframe Hv Hncmp Hrg Hw1 Hw2 Hrts Hlrd
  inext
  rw [hj, Nat.sub_zero]
  iintro %ws ⟨%st, %γw, %Hγ, #Hws, Hro, #Hhk, Hww, Hwt, Hcok, Hrds, Hcl, -, Hfrag, Hret⟩
  obtain ⟨hb, hl, hk, hi, hc, ht, hcmw⟩ := Hγ
  have hcmw' : γw.st.cm = false := by rw [hcmw]; simp [mvcc.kbCmpM]
  ihave #Hws' := Hws
  iunfold mvcc.isWatchableStore at Hws'
  icases Hws' with ⟨%vc, %stc, %rv, %γv, Hws'⟩
  iNamed Hws'
  iapply HΦ
  iexists st, γw
  rw [ht]
  iframe Hws Hhk Hwt Hcok Hrds Hcl Hro Hret
  iframe Htag
  isplitr
  · ipureintro; exact ⟨hb, hl, hk, hi, hc, hcmw'⟩
  isplitr
  · iunfold txn.isKV; iright; iexists ws, γw; iframe Hws; ipureintro; exact ⟨rfl, rfl⟩
  isplitr
  · iexists rv
    iframe Hrv
    iunfold mvcc.isReadView
    iexists _
    iframe Hrvkv Hs
    iunfold mvcc.kvOver; iright; iexists ws; iframe Hst; ipureintro; rfl
  isplitl [Hww Hfrag]
  · iunfold mvcc.watchWriter at Hww
    icases Hww with ⟨#Hc, Htoks, Hhalf⟩
    iunfold txn.kvWriter
    isplitl [Htoks]
    · iunfold txn.soleWriter
      iframe Hc
      have hsb : txn.soleBudget [[], []] = mvcc.wBudget [[], []] := rfl
      rw [hsb]
      iframe Htoks
      ipureintro; exact ⟨txn.soleLog_boot, hrb⟩
    isplitr [Hfrag]
    · iapply (txn.wlogOwn_watch st γw.st [[], []] Hwq).2
      iexists ws, γw
      iframe Hws Hhalf Hc
      ipureintro; rfl
    iexact Hfrag
  unfold txn.storeWTs
  rw [hk]
  iexact Hw

/-- **`server_kv_watchable_of` in either compaction mode** (M2, `NewServer.specCompact`; the
storage side's Draft `server_kv_watchable_ofD`, at the instance `{ d with cm := c }`): off, as
`server_kv_watchable_of` (nothing deletable); on, the store's keys deletable (`storeDlReg`), the
backend's fixed-keys fact and its safe-range slot given to the store, which keeps a reader back for
its compaction job (`nJobRd`) and gives the compaction's right (`crevRightM`). The specs only the
compacting store's backend contract uses are needed only on. -/
theorem server_kv_watchable_ofM (c : Bool)
    (hNew : mvcc.New.spec (GF := GF) (hG := hG))
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
    (hLSR : c = true → backend.backend.LockForSafeRangeDelete.spec (GF := GF) (hG := hG))
    (hUSR : c = true → backend.backend.UnlockForSafeRangeDelete.spec (GF := GF) (hG := hG))
    (hUP : c = true → backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (lg : Loc) (le : GoInterface)
    (cfg : go_etcd_io.etcd.server.v3.storage.mvcc.StoreConfig)
    (d : mvcc.KBReal) (hP : mvcc.bridgeParams d.P) (γb γl : GName) (Pk : IProp GF) (f : val)
    (rd0 : GoFunc) (N : Nat) (γi : mvcc.IdxNames) (γok : GName) (M : auth.AuthMode)
    (hcfg : mvcc.batchLimitOk cfg.CompactionBatchLimit')
    (hrb : receiptBound GF ≤ 2 ^ 48) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
        backend.isBackend d.γB d.P (mvcc.lateW d.gx) Pk d.be ∗ mvcc.keySized d.γB d.P d.be ∗
        backend.dlInit d.γB ∗
        mvcc.bkView d.γB 1 (∅ : mvcc.Bucket) ∗ mvcc.bkNoCmp d.γB ∗ mvcc.lateReg d.gx ∗
        ownToks d.γB.wb (N + 2) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          mvcc.bkRTx d.γB d.P d.be) ∗
        lease.lessorRdOf γl ∗ mvcc.isLessor le γl ∗ lease.rdOwn γl rd0 ∗
        mvcc.idxFresh γi ∗ ghostMapAuth γok 1 (∅ : GMap w64 mvcc.Log) ∗
        □ (⌜c = true⌝ -∗ backend.fkV d.γB true) ∗ backend.srSlot d.be }}
      (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.New)) (Val #lg))
        (Val #(interface.mkOk
          (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be)))
        (Val #le)) (Val #cfg))
    {{ (ws : Loc), RET #(interface.mkOk
          (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws);
        ∃ (st : Loc) (γw : mvcc.WsNames),
        ⌜γw.st.bucket = γb ∧ γw.st.leases = γl ∧ γw.st.kb = some ({ d with cm := c } : mvcc.KBReal) ∧
          γw.st.idx = γi ∧ γw.st.cok = γok ∧ γw.st.cm = c⌝ ∗
        txn.isKV (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws) st γw.st ∗
        (∃ rv : Loc, st.[go_etcd_io.etcd.server.v3.storage.mvcc.store, go!"ReadView"] ↦□
            (interface.mkOk (go.GoType.PointerType
              go_etcd_io.etcd.server.v3.storage.mvcc.readView.ty) #rv : GoInterface) ∗
          mvcc.isReadView rv st γw.st) ∗
        mvcc.hookInit γw.st Pk f ∗ txn.kvWriter st γw.st [[], []] ∗ txn.storeWTs γw.st N ∗
        ghostMapAuth γw.st.cok 1 (∅ : GMap w64 mvcc.Log) ∗
        mvcc.isWatchableStore ws st γw ∗ mvcc.watchToks γw (2 ^ 63 - 3) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders -
            mvcc.nJobRd (some ({ d with cm := c } : mvcc.KBReal)) - 2) (),
          mvcc.watchReader ws st γw) ∗
        mvcc.wsCloser ws st γw.st ∗ mvcc.crevRightM γw.st ∗
        mvcc.retiredAt γw.st (mvcc.nJobRd (some ({ d with cm := c } : mvcc.KBReal))) ∗
        (∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvcc.rdIs rd ws st γw) ∗ auth.modeTag γw.tag M }} := by
  iintro %Φ ⟨#Hpkg, #Hbpkg, #Hsch, #Hb, #Hsz, Hdl, Hv, Hncmp, Hrg, Hw, Hrts, Hlrd, #Hle, Hro, Hif,
    Hok, #Hfv, Hsr⟩ HΦ
  -- the backend's deletable keys fixed by the mode, and the store's contract the bridge's of it
  ihave Hsb : iprop(|==> □ ∀ (s : Loc) (γ : mvcc.StoreNames),
      ⌜γ.bucket = γb ∧ γ.kb = some ({ d with cm := c } : mvcc.KBReal) ∧ γ.idx = γi⌝ →
        mvcc.storeBackend (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be) s γ Pk) $$ [Hdl]
  · cases c with
    | true =>
      imod mvcc.storeDlReg_fix d.γB γi $$ Hdl with #Hreg
      ihave #Hfk := Hfv $$ %rfl
      ihave #Hsb := mvcc.storeBackend_of_backendC hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL
        hrRU hrUR hLI hLO hSP hUL hbUR hCB hDel hID hName hSafe (hLSR rfl) (hUSR rfl) (hUP rfl)
        ({ d with cm := true } : mvcc.KBReal) hP Pk γb γi $$ []
      · simp only [mvcc.KBReal.P_withCm]; iframe #
      imodintro; imodintro
      iexact Hsb
    | false =>
      imod backend.dlNoDel_fix d.γB $$ Hdl with #Hnd
      ihave #Hsb := mvcc.storeBackend_of_backend hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL
        hrRU hrUR hLI hLO hSP hUL hbUR hCB hDel hID hName hSafe ({ d with cm := false } : mvcc.KBReal)
        hP rfl Pk γb $$ []
      · simp only [mvcc.KBReal.P_withCm]; iframe #
      imodintro; imodintro
      iintro %s %γ %hγ
      iapply Hsb
      ipureintro; exact ⟨hγ.1, hγ.2.1⟩
  imod Hsb with #Hsb
  imod auth.modeTag_alloc (GF := GF) M with ⟨%γtag, #Htag⟩
  rw [show N + 2 = (N + 1) + 1 by omega]
  icases ownToks_add_1 1 (N + 1) d.γB.wb $$ Hw with ⟨Hw, Hw1⟩
  icases ownToks_add_1 1 N d.γB.wb $$ Hw with ⟨Hw, Hw2⟩
  ihave Hsrm := mvcc.kbSRM_some ({ d with cm := c } : mvcc.KBReal) $$ Hsr
  iapply (hNew lg _ le cfg (some ({ d with cm := c } : mvcc.KBReal)) γb γl Pk f rd0 γi γok γtag hcfg hrb)
    $$ [Hv Hncmp Hrg Hw1 Hw2 Hsrm Hrts Hlrd Hro Hif Hok]
  · iframe Hpkg Hle Hro Hif Hok Hsrm Hsb
    simp only [mvcc.kbView_some, mvcc.kbNoCmp_some, mvcc.kbRegRight_some, mvcc.kbWT_some,
      mvcc.kbRT_some, mvcc.KBReal.P_withCm]
    unfold backend.wbTok
    iframe Hv Hncmp Hrg Hw1 Hw2 Hrts Hlrd
  inext
  iintro %ws ⟨%st, %γw, %Hγ, #Hws, Hro, #Hhk, Hww, Hwt, Hcok, Hrds, Hcl, Hcr, Hfrag, Hret⟩
  obtain ⟨hb, hl, hk, hi, hc, ht, hcmw⟩ := Hγ
  have hcmw' : γw.st.cm = c := by rw [hcmw]; cases c <;> simp [mvcc.kbCmpM]
  ihave #Hws' := Hws
  iunfold mvcc.isWatchableStore at Hws'
  icases Hws' with ⟨%vc, %stc, %rv, %γv, Hws'⟩
  iNamed Hws'
  iapply HΦ
  iexists st, γw
  rw [ht]
  iframe Hws Hhk Hwt Hcok Hrds Hcl Hcr Hro Hret
  iframe Htag
  isplitr
  · ipureintro; exact ⟨hb, hl, hk, hi, hc, hcmw'⟩
  isplitr
  · iunfold txn.isKV; iright; iexists ws, γw; iframe Hws; ipureintro; exact ⟨rfl, rfl⟩
  isplitr
  · iexists rv
    iframe Hrv
    iunfold mvcc.isReadView
    iexists _
    iframe Hrvkv Hs
    iunfold mvcc.kvOver; iright; iexists ws; iframe Hst; ipureintro; rfl
  isplitl [Hww Hfrag]
  · iunfold mvcc.watchWriter at Hww
    icases Hww with ⟨#Hc, Htoks, Hhalf⟩
    iunfold txn.kvWriter
    isplitl [Htoks]
    · iunfold txn.soleWriter
      iframe Hc
      have hsb : txn.soleBudget [[], []] = mvcc.wBudget [[], []] := rfl
      rw [hsb]
      iframe Htoks
      ipureintro; exact ⟨txn.soleLog_boot, hrb⟩
    isplitr [Hfrag]
    · iapply (txn.wlogOwn_watch st γw.st [[], []] Hwq).2
      iexists ws, γw
      iframe Hws Hhalf Hc
      ipureintro; rfl
    iexact Hfrag
  unfold txn.storeWTs
  rw [hk]
  iexact Hw

/-- `backend_server_hooks` (`Results.lean`) from the specs it uses. -/
theorem backend_server_hooks_of
    (hOn : storage.BackendHooks.OnPreCommitUnsafe.spec (GF := GF) (hG := hG))
    (hSave : consistentIndex.UnsafeSave.spec (GF := GF) (hG := hG))
    (hPut : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (γA : ApplyNames) (ci : Loc) (γ : backend.BNames)
    (P : backend.BParams) (W : IProp GF) (b bh lgh : Loc) (hP : ciKeys P)
    (hH : storage.hooksParams P) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗
      storage.isBackendHooks bh
        ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty,
          #ci⟩ lgh ∗
      backend.isBackendNH γ P W (batchLockInv γA (metaTM γ P)) b (storage.hooksIface bh) ∗
      isCI ci γA.ci ∗ inv applyN (consInv γA) ∗ regdOrLink γA γ ⊢
      backend.isBackend γ P W (batchLockInv γA (metaTM γ P)) b := by
  iintro ⟨#Hspkg, #Hbpkg, #Hsch, #Hcpkg, #Hh, #Hnh, #Hci, #Hinv, #Hrl⟩
  iapply isBackend_backendHooks hOn γ P W
    (batchLockInv γA (metaTM γ P)) b bh _ lgh hH
  iframe Hspkg Hbpkg Hsch Hh Hnh
  iintro !> #Hb %t #Ht
  iapply ci_saveSpec hSave hPut hUR hID hName hSafe γA ci γ P W _ b t hP hH
  iframe #

/-- **The physical names of the backend `applySnapshot` opens** (D22 receiver epochs, S8b,
2026-10-24): the fresh `π0` with the new backend's write-back and open names. -/
abbrev futPhys (π0 : ApplyPhys) (γB : backend.BNames) : ApplyPhys :=
  { π0 with bwb := γB.wb, bopn := γB.opn }

/-- **The server's hooks' contract for the backend `applySnapshot` opens** (D22 receiver epochs,
S8b, 2026-10-24; `OpenSnapshotBackend`'s `openPre`): for the family of batch-lock resources
`batchLockInv (γA.withPh (futPhys π0 γB)) (metaTM γB P)` (the protocol at the fresh names `π0`
carrying the new backend's write-back and open names, so a hook of the backend before its names are
registered finds the payment rights deposited for it: `regdOrLink`'s second case). -/
theorem hooksOk_server_fut
    (hOn : storage.BackendHooks.OnPreCommitUnsafe.spec (GF := GF) (hG := hG))
    (hSave : consistentIndex.UnsafeSave.spec (GF := GF) (hG := hG))
    (hPut : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (γA : ApplyNames) (π0 : ApplyPhys) (ci : Loc) (P : backend.BParams)
    (W : backend.BNames → IProp GF) (bh lgh : Loc) (hP : ciKeys P) (hH : storage.hooksParams P) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗
      storage.isBackendHooks bh
        ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty,
          #ci⟩ lgh ∗
      isCI ci γA.ci ∗ inv applyN (consInv γA) ⊢
      backend.hooksOk P W (fun γB => batchLockInv (γA.withPh (futPhys π0 γB)) (metaTM γB P))
        (storage.hooksIface bh) := by
  iintro ⟨#Hspkg, #Hbpkg, #Hsch, #Hcpkg, #Hh, #Hci, #Hinv⟩
  iapply hooksOk_backendHooks hOn P W _ bh _ lgh hH
  iframe Hspkg Hbpkg Hsch Hh
  iintro !> %γ %b %t Hb #Ht
  inext
  ihave #Hrl : regdOrLink (γA.withPh (futPhys π0 γ)) γ $$ []
  · iunfold regdOrLink; iright; ipureintro; exact ⟨rfl, rfl⟩
  iapply ci_saveSpec hSave hPut hUR hID hName hSafe (γA.withPh (futPhys π0 γ)) ci γ P (W γ) _ b t
    hP hH
  ihave #Hinv' : inv applyN (consInv (γA.withPh (futPhys π0 γ))) $$ []
  · rw [show consInv (GF := GF) (γA.withPh (futPhys π0 γ)) = consInv γA from rfl]; iexact Hinv
  iframe Hbpkg Hsch Hcpkg Hb Ht Hci Hinv' Hrl

end backend

end EtcdGrove
end Perennial
