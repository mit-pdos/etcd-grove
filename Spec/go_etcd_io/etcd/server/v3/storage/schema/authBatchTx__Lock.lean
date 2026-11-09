/-
## `(*authBatchTx).Lock()`

**Users.** every auth write and `GetAllRoles` (`auth/store.go`: `tx.Lock()`). Snippet: `examples/specreq/schema/schema.go` (`ReqAuthWriteRead`).

**Proof sketch.** `atx.tx.LockInsideApply()`: the caller's triple of it (`callOk`), passed through.
**Changes.** New.
**Margin.** None.
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

/-- **`tx.LockInsideApply()`'s effect** (the caller's triple of it). -/
def authBatchTx.Lock.spec : Prop :=
  ∀ (atx lg : Loc) (tx : GoInterface) (P Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (atx ↦□ (go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.mk tx lg) : IProp GF) ∗ callOk tx go!"LockInsideApply" P Q ∗ P }}
    (App (Val (atx @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty @!! go!"Lock")) (Val #()))
  {{ RET #(); Q }}

end spec
end Schema
end EtcdGrove
end Perennial
