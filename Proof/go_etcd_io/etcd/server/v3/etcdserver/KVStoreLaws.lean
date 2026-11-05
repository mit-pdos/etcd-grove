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
  iintro ⟨-, %H⟩
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

end laws

end srvApi
end EtcdGrove
end Perennial
