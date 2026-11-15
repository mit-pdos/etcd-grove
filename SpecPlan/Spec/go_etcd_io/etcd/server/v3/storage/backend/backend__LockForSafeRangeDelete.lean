/-
## `(*backend).LockForSafeRangeDelete()` (`backend.go:1087-1089`): translated

**Users.** mvcc's compaction job (`kvstore_compaction.go:31`). **Proof sketch.**
`safeRangeDeleteMu.RLock()` (one reader slot of it, in the delete right). **Changes.** New (no old
spec). **Margin.** None.
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

/-- **`b.LockForSafeRangeDelete()`**: the safe-range delete right, held. -/
def backend.LockForSafeRangeDelete.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ beDel γ }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty @!! go!"LockForSafeRangeDelete")) (Val #()))
  {{ RET #(); beDelHeld γ }}

end spec

end Backend
end EtcdGrove
end Perennial
