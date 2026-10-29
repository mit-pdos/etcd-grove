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
        ⌜γw.st.bucket = γb ∧ γw.st.leases = γl ∧ γw.st.kb = some d ∧ γw.st.idx = γi ∧
          γw.st.cok = γok⌝ ∗
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
  iintro %Φ ⟨#Hpkg, #Hbpkg, #Hsch, #Hb, #Hsz, Hv, Hncmp, Hrg, Hw, Hrts, Hlrd, #Hle, Hro, Hif, Hok⟩ HΦ
  -- the auth mode's tag (the auth plan's A4): the store's owner tag names the mode `M`
  imod auth.modeTag_alloc (GF := GF) M with ⟨%γtag, #Htag⟩
  -- the backend never compacts here: its deletable keys' registration fixed at `False` (from the
  -- opener's `dlInit`, `dlReg_fix`), threaded from the boot backend in a later Draft step
  ihave #Hnd : backend.dlReg d.γB (fun _ => iprop(False)) $$ []
  · sorry -- backend-cmp Draft: new case (the registration fixed at False, from the opener's dlInit through the boot chain)
  ihave #Hsb := mvcc.storeBackend_of_backend hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU
    hrUR hLI hLO hSP hUL hbUR hCB hDel hID hName hSafe d hP Pk γb $$ [$Hbpkg $Hsch $Hb $Hsz $Hnd]
  rw [show N + 2 = (N + 1) + 1 by omega]
  icases ownToks_add_1 1 (N + 1) d.γB.wb $$ Hw with ⟨Hw, Hw1⟩
  icases ownToks_add_1 1 N d.γB.wb $$ Hw with ⟨Hw, Hw2⟩
  iapply (hNew lg _ le cfg (some d) γb γl Pk f rd0 γi γok γtag hcfg hrb)
    $$ [Hv Hncmp Hrg Hw1 Hw2 Hrts Hlrd Hro Hif Hok]
  · iframe Hpkg Hle Hro Hif Hok
    isplitr
    · iintro %s %γ %hγ
      iapply Hsb $$ %s %γ %hγ
    rw [show mvcc.kbView (GF := GF) (some d) γb 1 (∅ : mvcc.Bucket) = mvcc.bkView d.γB 1 ∅ from rfl,
      show mvcc.kbNoCmp (GF := GF) (some d) γb = mvcc.bkNoCmp d.γB from rfl,
      show mvcc.kbRegRight (GF := GF) (some d) = mvcc.lateReg d.gx from rfl,
      show mvcc.kbWT (GF := GF) (some d) = backend.wbTok d.γB from rfl,
      show mvcc.kbRT (GF := GF) (some d) = mvcc.bkRTx d.γB d.P d.be from rfl]
    unfold backend.wbTok
    iframe Hv Hncmp Hrg Hw1 Hw2 Hrts Hlrd
  inext
  iintro %ws ⟨%st, %γw, %Hγ, #Hws, Hro, #Hhk, Hww, Hwt, Hcok, Hrds, Hcl, Hfrag, Hret⟩
  obtain ⟨hb, hl, hk, hi, hc, ht⟩ := Hγ
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
  · ipureintro; exact ⟨hb, hl, hk, hi, hc⟩
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
