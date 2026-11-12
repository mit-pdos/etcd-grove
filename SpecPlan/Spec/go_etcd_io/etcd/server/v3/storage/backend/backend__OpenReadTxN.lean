/-
## `(*backend).OpenReadTxN()` (`backend.go:1083-1085`): translated

**Users.** mvcc's metrics closure (`kvstore.go`). **Proof sketch.** An atomic load.
**Changes.** Unchanged. **Margin.** The value is not stated.
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

/-- **`b.OpenReadTxN()`**: some `int64`, at any time. -/
def backend.OpenReadTxN.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty @!! go!"OpenReadTxN")) (Val #()))
  {{ (n : w64), RET #n; True }}

end spec

end Backend
end EtcdGrove
end Perennial
