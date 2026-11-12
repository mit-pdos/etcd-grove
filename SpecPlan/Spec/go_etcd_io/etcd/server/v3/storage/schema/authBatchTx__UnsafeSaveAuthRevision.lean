/-
## `(*authBatchTx).UnsafeSaveAuthRevision(...)`

**Users.** every auth write (`commitRevision`, `auth/store.go`), on the batch transaction under `Lock()`. Snippet: `examples/specreq/schema/schema.go`
(`ReqAuthWriteRead`). **Proof sketch.** A fresh 8-byte slice, `PutUint64`, made read-only for good, `tx.UnsafePut(Auth, authRevision, ...)`. (`txWr`). **Changes.** New (the old auth proofs had
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

/-- **Stores the auth revision** (eight big-endian bytes). -/
def authBatchTx.UnsafeSaveAuthRevision.spec : Prop :=
  ∀ (atx lg : Loc) (tx : GoInterface) (S : Scope) (R : View → IProp GF) (V : View) (m0 : BData)
    (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (atx ↦□ (go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.mk tx lg) : IProp GF) ∗ txWr tx S R ∗ R V ∗ ⌜S.has .auth authRevKey ∧ V .auth = some m0⌝ }}
    (App (Val (atx @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty @!! go!"UnsafeSaveAuthRevision")) (Val #rev))
  {{ RET #(); R (V.put .auth authRevKey (beU64 rev)) }}

end spec
end Schema
end EtcdGrove
end Perennial
