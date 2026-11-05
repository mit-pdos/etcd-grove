/-
**The server's store invariant's laws** (strict M1, 2026-11-05): the draft's `kvAus.law`,
`kvPeek.law`, `crevOk_off.law`, `histLb_boot.law` and `bootStore.law` (`KVStoreApi.lean`), each the
generic one of `KVStoreCore.lean` at the raft witness `kvNx γr on` and the compaction permit
`crevOk γr` (`kvStoreInv_eq`, by `rfl`), over mvcc's API laws as hypotheses (`persistent.law`,
`mvccState_reachable.law`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVStoreApi

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section
namespace Perennial
namespace EtcdGrove
namespace srvApi
open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc mvcc.api

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- `apply.cmpRevAfter` is the core's `crevAfter`. -/
theorem cmpRevAfter_eq (c : Int) (rev : w64) : apply.cmpRevAfter c rev = crevAfter c rev := rfl

/-- **The builders** (`kvAus.law`). -/
theorem kvAus_holds (Hp : persistent.law (GF := GF)) (Hr : mvccState_reachable.law (GF := GF)) :
    kvAus.law (GF := GF) := by
  intro kv γ γr on γs
  rw [kvStoreInv_eq]
  simp only [cmpRevAfter_eq, kvReadAt_eq]
  exact kvAusG (kvNx γr on) (crevOk γr) Hp Hr kv γ γs

/-- **The watch path's peek** (`kvPeek.law`). -/
theorem kvPeek_holds (Hp : persistent.law (GF := GF)) (Hr : mvccState_reachable.law (GF := GF)) :
    kvPeek.law (GF := GF) := by
  intro kv γ γr on γs E hE
  rw [kvStoreInv_eq]
  simp only [histLb_eq]
  exact kvPeekG (kvNx γr on) (crevOk γr) Hp Hr kv γ γs E hE

/-- **The never-compacting cluster's compaction revision** (`crevOk_off.law`). -/
theorem crevOk_off_holds : crevOk_off.law (GF := GF) := by
  intro γr c h
  iintro H
  iunfold crevOk at H
  icases H with ⟨-, %H⟩
  ipureintro; exact H h

/-- **The boot's bound** (`histLb_boot.law`). -/
theorem histLb_boot_holds (Hp : persistent.law (GF := GF))
    (Hr : mvccState_reachable.law (GF := GF)) : histLb_boot.law (GF := GF) := by
  intro kv γ γr on γs
  rw [kvStoreInv_eq, histLb_eq]
  exact histLb_bootG (kvNx γr on) (crevOk γr) Hp Hr kv γ γs

/-- **The boot's store invariant** (`bootStore.law`): the witness of the empty history from the
committed raft log's empty prefix, the permit of `-1`. -/
theorem bootStore_holds (Hp : persistent.law (GF := GF)) : bootStore.law (GF := GF) := by
  intro kv γ γr on γs h0
  haveI := Hp.1 kv γ
  rw [kvStoreInv_eq]
  iintro ⟨#Hm, Hs, Hf, #Hlb⟩
  iunfold newServerStoreFreshA at Hf
  icases Hf with ⟨Hst, Hcr, Hsl, Hnl⟩
  iapply bootStoreG (kvNx γr on) (crevOk γr) Hp kv γ γs
  iframe Hm Hs Hst Hcr Hsl Hnl
  isplitl []
  · iunfold kvNx
    iexists []
    iframe Hlb
    ipureintro; exact h0
  iunfold crevOk
  isplitl []
  · ileft; ipureintro; rfl
  ipureintro; intro _; rfl

/-- The mode-off raft witness is `KVApply`'s `kvNxOff` (by `rfl`). -/
theorem kvNx_off (γr : ReadNames) : kvNx (GF := GF) γr false = kvNxOff γr.raft γr.kv := rfl

/-- **The server's witness and permit are persistent and timeless** (`envWitOk`, which the
apply thread's `srvKVInvs` carries). -/
theorem envWitOk_srv (E : apply.AEnv GF) (γr : ReadNames) (on : Bool)
    (hNx : E.Nx = kvNx γr on) (hCp : E.Cp = crevOk γr) : envWitOk E := by
  unfold envWitOk; rw [hNx, hCp]
  exact ⟨fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance⟩

/-- **The draft's `srvKVInvsA` from the apply thread's `srvKVInvs`** and the ties of the store
handle, the witness and the permit (strict M1, 2026-11-05: `srvKVInvs`, below the KV model, has
no tie naming it; the server's mode-level facts carry them). -/
theorem srvKVInvsA_of (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) (wsl : Loc)
    (h : E.kv = wsIfaceA wsl ∧ E.Nx = kvNx γr on ∧ E.Cp = crevOk γr) :
    srvKVInvs (GF := GF) E γr ⊢ srvKVInvsA on E γr wsl := by
  iintro H
  iunfold srvKVInvs at H
  icases H with ⟨#Hk, -, #Hr, #Hs, %Hm, -⟩
  iunfold srvKVInvsA
  iframe Hk Hr
  isplitl
  · rw [kvStoreInv_eq, ← h.2.1, ← h.2.2]; iexact Hs
  · ipureintro; exact ⟨h.1, h.2.1, h.2.2, Hm.1, Hm.2.1⟩

/-- **The apply thread's `srvKVInvs` from the store invariant**, the KV and raft invariants and the
KV certificates' (`kvCertInv`, the server's own), at the server's witness and permit (the mode
off: `srvKVInvs` ties `E.Nx` to `kvNxOff`, 2026-11-06). -/
theorem srvKVInvs_of (Hp : persistent.law (GF := GF)) (E : apply.AEnv GF)
    (γr : ReadNames) (hNx : E.Nx = kvNx γr false) (hCp : E.Cp = crevOk γr)
    (hm : γr.kv.cmp = E.cmp ∧ γr.kv.cret = E.cret) :
    kvInv (GF := GF) γr.raft γr.kv ∗ kvCertInv γr.raft γr.kv ∗ srvRaftLogInv γr.raft ∗
      kvStoreInv E.kv E.γ γr false E.γs ⊢ srvKVInvs E γr := by
  haveI : Persistent (kvStoreInv (GF := GF) E.kv E.γ γr false E.γs) := by
    rw [kvStoreInv_eq]; exact kvStoreInvG_persistent Hp E.kv E.γ (kvNx γr false) (crevOk γr) E.γs
  iintro ⟨#Hk, #Hc, #Hr, #Hs⟩
  iunfold srvKVInvs
  iframe Hk Hc Hr
  isplitl
  · rw [hNx, hCp, ← kvStoreInv_eq]; iexact Hs
  isplitl
  · ipureintro; exact ⟨hm.1, hm.2, envWitOk_srv E γr false hNx hCp⟩
  · ipureintro; exact hNx

end laws

end srvApi
end EtcdGrove
end Perennial
