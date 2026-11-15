/-
## `(*backend).Size()` (`backend.go:454-456`): translated

**Users.** The quota (`storage/quota.go:133, 177`, any goroutine, also after the close: 2e's
`beReadable`), mvcc's metrics closures and compaction log (`kvstore.go:524`,
`kvstore_compaction.go:75`), bootstrap (`bootstrap.go:284, 308`). **Proof sketch.**
`atomic.LoadInt64(&b.size)` (an atomic's invariant: any `int64`). **Changes.** Unchanged.
**Margin.** The value is not stated.
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

/-- **`b.Size()`**: some `int64`, at any time. -/
def backend.Size.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty @!! go!"Size")) (Val #()))
  {{ (n : w64), RET #n; True }}

end spec

end Backend
end EtcdGrove
end Perennial
