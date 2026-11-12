/-
## `(*concurrentReadTx).Lock()` (`read_tx.go:144`): translated

**Users.** None outside tests (kept: it had a spec). **Proof sketch.** Empty body.
**Changes.** Unchanged. **Margin.** None.
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

/-- **`rt.Lock()`** on a concurrent read transaction: nothing. -/
def concurrentReadTx.Lock.spec : Prop :=
  ∀ (l : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.concurrentReadTx.ty @!! go!"Lock")) (Val #()))
  {{ RET #(); True }}

end spec

end Backend
end EtcdGrove
end Perennial
