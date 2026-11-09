/-
`UnsafeReadScheduledCompact(tx)` (`store.go:30`). Internal: `restore`, `checkPrevCompactionCompleted`.
As `UnsafeReadFinishedCompact`, of the scheduled compaction key.

**Changes** from `specs-ref`'s file: over the storage contract's `rangeOk`.
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

/-- `UnsafeReadScheduledCompact(tx)`: `metaRev D.sched`. -/
def UnsafeReadScheduledCompact.spec : Prop :=
  ∀ (t : GoInterfaceOk) (R : IProp GF) (D : KeyData) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ schemaVars ∗
      rangeOk t R D (if b then KeyData.range else KeyData.rtRange) ∗ R ∗ ⌜D.metaMade = true ∧ metaOk D.sched⌝ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeReadScheduledCompact))
      (Val #(GoInterface.ok t)))
  {{ (x : w64) (found : Bool), RET (PairV #x #found); R ∗ ⌜(x, found) = metaRev D.sched⌝ }}

end spec
end Mvcc
end EtcdGrove
end Perennial
