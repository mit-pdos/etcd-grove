/-
`UnsafeSetScheduledCompact(tx, value)` (`store.go:44`). Internal: `SetScheduledCompact`. Under the
batch lock (`kbLocked`), writes `Meta`'s scheduled key: `RevToBytes(Revision{Main: value})`.

**Changes** from `specs-ref`'s file: over the storage contract (`kbLocked`, `KeyData.putMeta`).
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

/-- `UnsafeSetScheduledCompact(tx, value)` on the storage's locked batch transaction. -/
def UnsafeSetScheduledCompact.spec : Prop :=
  ∀ (B : MvccStorage) (Pk : IProp GF) (D : KeyData) (value : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ schemaVars ∗
      keyBackend B Pk ∗ kbLocked B D ∗ ⌜D.metaMade = true⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeSetScheduledCompact))
      (Val #(GoInterface.ok (kbBatchTx B)))) (Val #value))
  {{ RET #(); kbLocked B (D.putMeta .sched (revBytes ⟨value, W64 0⟩ false)) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
