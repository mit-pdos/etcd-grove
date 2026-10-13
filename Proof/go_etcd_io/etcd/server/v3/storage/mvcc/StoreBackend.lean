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
variable [backend_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- **`NewStore` over the real backend**: on a fresh backend made for the real instance `d`
(`isBackend d.γB d.P (lateW d.gx) Pk d.be`, with schema's buckets, its post-lock hook `f` set
for good, and the size premise `keySized` of its range reads), given what the backend's creator
holds (the clients' view of the empty `Key` bucket, the right to register the store's lock
resource, two write-back tokens, one reader token per reader slot), and a batch limit not
negative, `NewStore` returns a store of that instance (with its compaction right, of no use over
this instance: `storeCmp`). -/
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
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (lg : Loc) (le : GoInterface) (cfg : StoreConfig) (d : mvcc.KBReal)
    (hP : mvcc.bridgeParams d.P) (γb γl : GName) (Pk : IProp GF) (f : GoFunc)
    (hf : f ≠ func.nil) (hcfg : 0 ≤ sint.Z cfg.CompactionBatchLimit') :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
        backend.isBackend d.γB d.P (mvcc.lateW d.gx) Pk d.be ∗ backend.plHookRO d.γB f ∗
        mvcc.keySized d.γB d.P d.be ∗
        mvcc.bkView d.γB 1 (∅ : mvcc.Bucket) ∗ mvcc.lateReg d.gx ∗
        backend.wbTok d.γB ∗ backend.wbTok d.γB ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          mvcc.bkRTx d.γB d.P d.be) ∗
        lease.lessorRdOf γl ∗ mvcc.isLessor le γl }}
      (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewStore)) (Val #lg))
        (Val #(interface.mkOk
          (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be)))
        (Val #le)) (Val #cfg))
    {{ (s : Loc), RET #s; ∃ γ : mvcc.StoreNames,
        ⌜γ.bucket = γb ∧ γ.leases = γl ∧ γ.kb = some d⌝ ∗
        mvcc.isStore s γ ∗ mvcc.hookIs γ Pk #f ∗
        (∃ rv wv : Loc,
          s.[store, go!"ReadView"] ↦
            (interface.mkOk (go.GoType.PointerType readView.ty) #rv : GoInterface) ∗
          mvcc.isReadView rv s γ ∗
          s.[store, go!"WriteView"] ↦
            (interface.mkOk (go.GoType.PointerType writeView.ty) #wv : GoInterface) ∗
          mvcc.isWriteView wv s γ) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          mvcc.storeReaderC s γ) ∗
        ownToks γ.revs (2 ^ 63 - 5) ∗ mvcc.idxCert γ.idx [[], []] ∗ mvcc.storeCloser s ∗
        mvcc.storeStop s ∗ mvcc.compactRight γ (-1) }} := by
  iintro %Φ ⟨#Hpkg, #Hbpkg, #Hsch, #Hb, #Hhk, #Hsz, Hv, Hrg, Hw1, Hw2, Hrts, Hlrd, #Hle⟩ HΦ
  ihave #Hbk := mvcc.storeBackend_of_backend hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU
    hrUR hLI hLO hSP hUL hbUR hCB hID hName hSafe d hP Pk f hf γb $$ [$Hbpkg $Hsch $Hb $Hhk $Hsz]
  iapply (hNewStore lg _ le cfg (some d) γb γl Pk #f hcfg) $$ %Φ [Hv Hrg Hw1 Hw2 Hrts Hlrd] HΦ
  iframe Hpkg Hbk Hle
  rw [show mvcc.kbView (GF := GF) (some d) γb 1 (∅ : mvcc.Bucket) = mvcc.bkView d.γB 1 ∅ from rfl,
    show mvcc.kbRegRight (GF := GF) (some d) = mvcc.lateReg d.gx from rfl,
    show mvcc.kbWT (GF := GF) (some d) = backend.wbTok d.γB from rfl,
    show mvcc.kbRT (GF := GF) (some d) = mvcc.bkRTx d.γB d.P d.be from rfl]
  iframe Hv Hrg Hw1 Hw2 Hrts Hlrd

/-- **`store.Write` over the real backend**: the generic `store.Write` at a store of the real
instance `d`, its write token the backend's write-back budget. -/
theorem mvcc.store_Write_backend (hWrite : mvcc.store.Write.spec (GF := GF) (hG := hG))
    (s : Loc) (γ : mvcc.StoreNames) (d : mvcc.KBReal) (hk : γ.kb = some d) (trace : Loc)
    (P Pre Q : IProp GF) (f : val) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        mvcc.isStore s γ ∗ mvcc.storeReader s γ ∗ mvcc.revToken γ ∗ backend.wbTok d.γB ∗
        ⌜trace ≠ null⌝ ∗ mvcc.hookIs γ P f ∗ Pre ∗
        □ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) }}
      (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Write")) (Val #trace))
    {{ (mw : Loc), RET #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw);
        (∃ ilog : mvcc.Log, mvcc.isTxnWrite mw s γ ilog [] (W64 0) (W64 0) (W64 0)) ∗ Q }} := by
  have hwt : mvcc.storeWT (GF := GF) γ = backend.wbTok d.γB := by
    unfold mvcc.storeWT mvcc.kbWT; rw [hk]
  rw [← hwt]
  exact hWrite s γ trace P Pre Q f

end proof

end EtcdGrove
end Perennial
