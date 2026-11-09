/-
## `(*authBatchTx).UnsafeSaveAuthEnabled(...)`

**Users.** `AuthEnable`, `AuthDisable` (`auth/store.go`), on the batch transaction under `Lock()`. Snippet: `examples/specreq/schema/schema.go`
(`ReqAuthWriteRead`). **Proof sketch.** `tx.UnsafePut(Auth, authEnabled, authEnabled|authDisabled)` (the package's read-only slices: `keyNames_init`). (`txWr`). **Changes.** New (the old auth proofs had
no batch-side spec). **Margin.** None.
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

/-- **Stores the enabled flag** (`[1]` or `[0]`). -/
def authBatchTx.UnsafeSaveAuthEnabled.spec : Prop :=
  ∀ (atx lg : Loc) (tx : GoInterface) (S : Scope) (R : View → IProp GF) (V : View) (m0 : BData)
    (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (atx ↦□ (go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.mk tx lg) : IProp GF) ∗ txWr tx S R ∗ R V ∗ ⌜S.has .auth authEnabledKey ∧ V .auth = some m0⌝ }}
    (App (Val (atx @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty @!! go!"UnsafeSaveAuthEnabled")) (Val #b))
  {{ RET #(); R (V.put .auth authEnabledKey (if b then [W8 1] else [W8 0])) }}

end spec
end Schema
end EtcdGrove
end Perennial
