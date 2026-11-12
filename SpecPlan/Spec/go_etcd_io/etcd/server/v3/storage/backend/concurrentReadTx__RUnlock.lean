/-
## `(*concurrentReadTx).RUnlock()` (`read_tx.go:151`): translated

**Users.** mvcc's `storeTxnRead.End` (`kvstore_txn.go`). **Proof sketch.** `rt.txWg.Done()` (the
interval's wait group: the budget token deposited at creation; the rollback goroutine of an ended
interval may now roll bbolt's read transaction back); the slot back. **Changes.** The slot back.
**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.backend.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`rt.RUnlock()`** on a concurrent read transaction: it ends; the reader slot back. -/
def concurrentReadTx.RUnlock.spec : Prop :=
  ∀ (γ : BeNames) (l : Loc) (F : Fp) (V : Image),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ beRd γ l F V ∗ beLive γ l 1 ∗ ⌜l ≠ rtLoc γ⌝ }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.concurrentReadTx.ty @!! go!"RUnlock")) (Val #()))
  {{ RET #(); beRdToks γ 1 }}

end spec

end Backend
end EtcdGrove
end Perennial
