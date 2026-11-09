/-
## `(*backend).ReadTx()` (`backend.go:279`): translated

**Users.** mvcc (`kvstore.go:188, 226, 327`, `kvstore_txn.go:57`, `watchable_store.go:441`), auth
(`schema/auth.go:64`), alarms (`schema/alarm.go:85`), the consistent index (`ReadConsistentIndex`),
bootstrap (`schema.Validate`, `bootstrap.go:292`). **Proof sketch.** Reads `b.readTx`.
**Changes.** Unchanged in substance. **Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Api

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

/-- **`b.ReadTx()`**: the shared read transaction. -/
def backend.ReadTx.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty @!! go!"ReadTx")) (Val #()))
  {{ RET #(rtIface γ); True }}

end spec

end Backend
end EtcdGrove
end Perennial
