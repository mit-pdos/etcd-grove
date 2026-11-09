/-
`SetScheduledCompact(tx, value)` (`store.go:38`). Internal: `updateCompactRev`.
`tx.LockInsideApply()` (the storage's hook run, `Pre` to `Q'`), `UnsafeSetScheduledCompact`, the
deferred `tx.Unlock()` (`Pk` back; the write made visible: the caller's second update, built at the
data the lock read, the first).

**Changes** from `specs-ref`'s file: over the storage contract (`storageHook`, `hookRun`, `kbObs`) in
place of `batchTxSpecG`, `lockArmS`, `mwLend`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalStore

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

/-- `SetScheduledCompact(tx, value)`: the hook, then the scheduled key written and made visible. -/
def SetScheduledCompact.spec : Prop :=
  ∀ (B : MvccStorage) (Pk : IProp GF) (dq : DFrac) (f : GoFunc) (Pre Q' Post R : IProp GF)
    (value : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ schemaVars ∗
      keyBackend B Pk ∗ storageHook B dq f ∗ Pre ∗ hookRun Pk f Pre Q' ∗ (Q' ={⊤}=∗ Pk ∗ Post) ∗
      kbObs B (fun D => iprop(⌜D.metaMade = true⌝ ∗
        AU <{ ∃∃ (D0 : KeyData), kbData B D0 }> @ ⊤, ∅
          <{ kbData B (D.putMeta .sched (revBytes ⟨value, W64 0⟩ false)), COMM R }>)) }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.SetScheduledCompact))
      (Val #(GoInterface.ok (kbBatchTx B)))) (Val #value))
  {{ RET #(); storageHook B dq f ∗ Post ∗ R }}

end spec
end Mvcc
end EtcdGrove
end Perennial
