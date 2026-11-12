/-
## `(*backend).BatchTx()` (`backend.go:266-268`): translated

**Users.** Every writer: mvcc (`kvstore_txn.go:176`, `kvstore.go:120`, `kvstore_compaction.go:55`),
the lessor (`lessor.go:809`, `lease.go:57`), the schema's writers (4b), auth (`auth/store.go`), the
consistent index (`cindex.go:175`). **Proof sketch.** Reads the read-only `b.batchTx`.
**Changes.** Unchanged in substance. **Margin.** None.
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

/-- **`b.BatchTx()`**: the backend's one batch transaction. -/
def backend.BatchTx.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty @!! go!"BatchTx")) (Val #()))
  {{ RET #(btIface γ); True }}

end spec

end Backend
end EtcdGrove
end Perennial
