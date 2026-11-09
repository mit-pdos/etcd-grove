/-
`UnsafeSetFinishedCompact(tx, value)` (`store.go:56`). Internal: `scheduleCompaction`'s last batch,
`SetFinishedCompact`. As `UnsafeSetScheduledCompact`, of the finished key.

**Changes** from `specs-ref`'s file: over the storage contract.
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

/-- `UnsafeSetFinishedCompact(tx, value)` on the storage's locked batch transaction. -/
def UnsafeSetFinishedCompact.spec : Prop :=
  ∀ (B : MvccStorage) (Pk : IProp GF) (D : KeyData) (value : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ schemaVars ∗
      keyBackend B Pk ∗ kbLocked B D ∗ ⌜D.metaMade = true⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeSetFinishedCompact))
      (Val #(GoInterface.ok (kbBatchTx B)))) (Val #value))
  {{ RET #(); kbLocked B (D.putMeta .fin (revBytes ⟨value, W64 0⟩ false)) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
