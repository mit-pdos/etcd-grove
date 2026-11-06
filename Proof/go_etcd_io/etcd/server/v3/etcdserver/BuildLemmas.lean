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

-- MERGE-TODO(close): `lean`'s `srvStopChans_boot` (R2b-3c, the backend's stop channels for
-- `backend.Close`), restated at this branch's instance (no F2 ties, the boot's write invariant
-- `mvcc.lateW d.gx` in place of `lateWB`/`lateWD_boot`); its body waits on `srvStopChans`' restatement
-- (`SnapRO.lean`, over `mvcc.lateWD`) and on the user's decision about the API's `Close`.
/-- **`NewServer`'s backend's stop channels are the server's** (`bootstrap`'s lock resource),
at the instance in either compaction mode. -/
theorem srvStopChans_boot (γA : ApplyNames) (d : mvcc.KBReal) (c : Bool) :
    backend.isBackend (GF := GF) d.γB d.P (mvcc.lateW d.gx)
        (batchLockInv γA (metaTM d.γB d.P)) d.be ∗
      backend.isStopChans d.γB d.P (mvcc.lateW d.gx) (batchLockInv γA (metaTM d.γB d.P)) d.be ⊢
      srvStopChans γA ({ d with cm := c } : mvcc.KBReal) := by
  unfold srvStopChans
  exact .rfl

theorem plHookRO_withCm (d : mvcc.KBReal) (c : Bool) (f : GoFunc) :
    backend.plHookRO (GF := GF) d.γB f ⊢ backend.plHookRO ({ d with cm := c } : mvcc.KBReal).γB f := by
  exact .rfl

theorem keySized_withCm (d : mvcc.KBReal) (c : Bool) :
    (□ ∀ (γB : backend.BNames) (b : Loc), mvcc.keySized (GF := GF) γB d.P b) ⊢
      □ ∀ (γB : backend.BNames) (b : Loc),
        mvcc.keySized γB ({ d with cm := c } : mvcc.KBReal).P b := by
  exact .rfl

-- (Strict M1, 2026-11-06) `server_kv_watchable_of` and `server_kv_watchable_ofM` deleted: they
-- bridged `NewServer` to mvcc's internal `mvcc.New.spec` (the sole writer `txn.kvWriter`,
-- `txn.storeWTs`, `mvcc.isWatchableStore`, the watch tokens and readers, the mode tag). Over the API
-- the boot calls `mvcc.api.New.spec` (over `mvccStorageFor`, from `etcdStorage_open.law`) directly.

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
