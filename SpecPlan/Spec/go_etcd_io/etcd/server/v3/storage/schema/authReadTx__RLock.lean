/-
## `(*authReadTx).RLock()`

**Users.** `lockedReadTx`-style readers of the auth store (`auth/store.go`), `GetUser`/`GetRole`/`GetAllUsers`. Snippet: `examples/specreq/schema/schema.go` (`ReqAuthWriteRead`).

**Proof sketch.** `atx.tx.RLock()`: the caller's triple of it (`callOk`), passed through.
**Changes.** From `specs-ref`'s `authReadTx__RLock.lean` (the old backend's read pool): the backend call's triple is the premise.
**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.schema.Api

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

/-- **`tx.RLock()`'s effect** (the caller's triple of it). -/
def authReadTx.RLock.spec : Prop :=
  ∀ (atx lg : Loc) (tx : GoInterface) (P Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (atx ↦□ (go_etcd_io.etcd.server.v3.storage.schema.authReadTx.mk tx lg) : IProp GF) ∗ callOk tx go!"RLock" P Q ∗ P }}
    (App (Val (atx @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authReadTx.ty @!! go!"RLock")) (Val #()))
  {{ RET #(); Q }}

end spec
end Schema
end EtcdGrove
end Perennial
