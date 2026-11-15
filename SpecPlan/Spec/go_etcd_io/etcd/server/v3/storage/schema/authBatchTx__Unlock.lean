/-
## `(*authBatchTx).Unlock()`

**Users.** Every auth write, `GetAllRoles` (`auth/store.go`). Snippet: `examples/specreq/schema/schema.go`
(`ReqAuthWriteRead`).

**Proof sketch.** `atx.tx.Unlock()` then `atx.tx.Commit()` (the "defensive" commit, `auth.go:115-119`:
the writes reach the read transactions): the caller's triples of both.

**Changes.** New. **Margin.** None.
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

/-- **`tx.Unlock()` then `tx.Commit()`** (the caller's triples of them). -/
def authBatchTx.Unlock.spec : Prop :=
  ∀ (atx lg : Loc) (tx : GoInterface) (P Q1 Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (atx ↦□ (go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.mk tx lg) : IProp GF) ∗ callOk tx go!"Unlock" P Q1 ∗ callOk tx go!"Commit" Q1 Q ∗ P }}
    (App (Val (atx @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty @!! go!"Unlock")) (Val #()))
  {{ RET #(); Q }}

end spec
end Schema
end EtcdGrove
end Perennial
