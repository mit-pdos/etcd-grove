/-
## `(*authBackend).ForceCommit()`

**Users.** The auth store (`auth/store.go`: after `AuthEnable`'s first write, `Recover`).
**Proof sketch.** `abe.be.ForceCommit()`: the caller's triple. **Changes.** New. **Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Schema

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- **`be.ForceCommit()`'s effect** (the caller's triple). -/
def authBackend.ForceCommit.spec : Prop :=
  ∀ (abe lg : Loc) (be : GoInterface) (P Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (abe ↦□ (go_etcd_io.etcd.server.v3.storage.schema.authBackend.mk be lg) : IProp GF) ∗ callOk be go!"ForceCommit" P Q ∗ P }}
    (App (Val (abe @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty @!! go!"ForceCommit")) (Val #()))
  {{ RET #(); Q }}

end spec
end Schema
end EtcdGrove
end Perennial
