/-
## `(*authBatchTx).UnsafeDeleteUser(...)`

**Users.** `UserDelete` (`auth/store.go`), on the batch transaction under `Lock()`. Snippet: `examples/specreq/schema/schema.go`
(`ReqAuthWriteRead`). **Proof sketch.** `tx.UnsafeDelete(AuthUsers, []byte(name))`. (`txWr`). **Changes.** New (the old auth proofs had
no batch-side spec). **Margin.** None.
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

/-- **Deletes the user `name`.** -/
def authBatchTx.UnsafeDeleteUser.spec : Prop :=
  ∀ (atx lg : Loc) (tx : GoInterface) (S : Scope) (R : View → IProp GF) (V : View) (m0 : BData)
    (name : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (atx ↦□ (go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.mk tx lg) : IProp GF) ∗ txWr tx S R ∗ R V ∗ ⌜S.has .authUsers name ∧ V .authUsers = some m0⌝ }}
    (App (Val (atx @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty @!! go!"UnsafeDeleteUser")) (Val #name))
  {{ RET #(); R (V.del .authUsers name) }}

end spec
end Schema
end EtcdGrove
end Perennial
