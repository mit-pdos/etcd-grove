/-
`SetFinishedCompact(tx, value)` (`store.go:50`). Internal; no caller in the pinned etcd but mvcc's
tests (kept: an old spec). As `SetScheduledCompact`, of the finished key.

**Changes** from `specs-ref`'s file: over the storage contract.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `SetFinishedCompact(tx, value)`: the hook, then the finished key written and made visible. -/
def SetFinishedCompact.spec : Prop :=
  ∀ (B : MvccStorage) (Pk : IProp GF) (q : Qp) (dq : DFrac) (f : GoFunc) (Pre Q' Post R : IProp GF)
    (value : w64),
  let D' (D : KeyData) := D.putMeta .fin (revBytes ⟨value, W64 0⟩ false)
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ schemaVars ∗
      keyBackend B Pk ∗ kbOpen B q ∗ storageHook B dq f ∗ Pre ∗ hookRun B Pk f Pre Q' ∗
      (Q' ={⊤}=∗ Pk ∗ Post) ∗
      kbObs B (fun D => iprop(⌜D.metaMade = true⌝ ∗
        AU <{ ∃∃ (D1 : KeyData), kbData B D1 }> @ ⊤, ∅ <{ kbData B (D' D), COMM
          AU <{ ∃∃ (D2 : KeyData), kbData B D2 }> @ ⊤, ∅ <{ kbData B (D' D), COMM R }> }>)) }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.SetFinishedCompact))
      (Val #(GoInterface.ok (kbBatchTx B)))) (Val #value))
  {{ RET #(); kbOpen B q ∗ storageHook B dq f ∗ Post ∗ R }}

end spec
end Mvcc
end EtcdGrove
end Perennial
