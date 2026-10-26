/-
**The KV's closer after `applySnapshot`** (D22 receiver epochs, S8d, step 6 of
`srvSnapApplied_of_walk`, `notes/snapshot-s8-plan.md`): `srvKVCloser` at the snapshot's environment.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyNames

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Step 6: the KV's closer at the snapshot's environment** (`restorePre_of_apply`'s closer
parts, kept by the walk, and the inner store's closer `store.Restore` gave back).

Brief for the prover: `unfold srvKVCloser mvcc.wsCloser`, `iexists wsk`, `iexists stck`,
`simp only [snapE_s, snapE_γ]`, rewrite `← hγw` in the goal's `E.γ.withPhys p'`, and frame. -/
theorem snap_kvCloser (s : Loc) (E : apply.AEnv GF) (γ' : ApplyNames) (TM' : MetaCI → IProp GF)
    (ci : Loc) (p' : mvcc.PhysNames) (g : GoFunc) (γB : backend.BNames) (al ast lp cl be : Loc)
    (γw : mvcc.WsNames) (wsk stck : Loc) (hγw : γw.st = E.γ) :
    srvKVAddr s ↦□ (interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsk : GoInterface) ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore go!"stopc" wsk ↦□ stck ∗
      mvcc.stopCloser stck ∗ mvcc.wsWaiter wsk ∗ mvcc.storeCloser E.s (γw.st.withPhys p') ⊢
    srvKVCloser s (snapE E γ' TM' ci p' g γB al ast lp cl be) := by
  unfold srvKVCloser mvcc.wsCloser
  simp only [snapE_s, snapE_γ]
  rw [← hγw]
  iintro ⟨#Hk, #Hst, Hsc, Hw, Hc⟩
  iexists wsk
  iframe
  isplitl []
  · iexact Hk
  · iexact Hst

end proof
end EtcdGrove
end Perennial
