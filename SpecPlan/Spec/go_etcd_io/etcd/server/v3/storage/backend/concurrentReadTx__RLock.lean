/-
## `(*concurrentReadTx).RLock()` (`read_tx.go:148`): translated

**Users.** mvcc's `store.Read` (`kvstore_txn.go:60`). **Proof sketch.** A no-op (the snapshot was
taken at creation). **Changes.** Unchanged. **Margin.** None.
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

/-- **`rt.RLock()`** on a concurrent read transaction: nothing. -/
def concurrentReadTx.RLock.spec : Prop :=
  ∀ (γ : BeNames) (l : Loc) (F : Fp) (V : Image),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ beRd γ l F V }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.concurrentReadTx.ty @!! go!"RLock")) (Val #()))
  {{ RET #(); beRd γ l F V }}

end spec

end Backend
end EtcdGrove
end Perennial
