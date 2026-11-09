/-
## `(*backend).UnlockForSafeRangeDelete()` (`backend.go:1091-1093`): translated

**Users.** mvcc's compaction job (`kvstore_compaction.go:32`, deferred). **Proof sketch.**
`safeRangeDeleteMu.RUnlock()`. **Changes.** New. **Margin.** None.
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

/-- **`b.UnlockForSafeRangeDelete()`**: the delete right idle again. -/
def backend.UnlockForSafeRangeDelete.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ beDelHeld γ }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty @!! go!"UnlockForSafeRangeDelete")) (Val #()))
  {{ RET #(); beDel γ }}

end spec

end Backend
end EtcdGrove
end Perennial
