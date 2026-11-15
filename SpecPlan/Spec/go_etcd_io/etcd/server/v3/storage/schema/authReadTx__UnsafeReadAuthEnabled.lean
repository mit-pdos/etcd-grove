/-
## `(*authReadTx).UnsafeReadAuthEnabled(...)`

**Users.** the auth store's `isAuthEnabled` reads (`auth/store.go`: on both transactions); 3d's auth store through `AuthBatchTx`/`AuthReadTx`. Snippet:
`examples/specreq/schema/schema.go` (`ReqAuthWriteRead`).
**Proof sketch.** Loads `atx.tx`, `atx.lg`; `unsafeReadAuthEnabled` (`unsafeReadAuthEnabled.spec`). **Changes.** From
`specs-ref`'s `authReadTx__UnsafeReadAuthEnabled.lean` where there was one: over the contract. **Margin.** None.
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

/-- **Whether auth is enabled** (`authEnabled` holding `[1]`). -/
def authReadTx.UnsafeReadAuthEnabled.spec : Prop :=
  ∀ (atx : Loc) (lg : Loc) (tx : GoInterface) (S : Scope) (R : View → IProp GF) (V : View) (m : BData),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (atx ↦□ (go_etcd_io.etcd.server.v3.storage.schema.authReadTx.mk tx lg) : IProp GF) ∗ txRd tx S R ∗ R V ∗ ⌜S.has .auth authEnabledKey ∧ V .auth = some m⌝ }}
    (App (Val (atx @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authReadTx.ty @!! go!"UnsafeReadAuthEnabled")) (Val #()))
  {{ RET #(authEnabledOf m); R V }}

end spec
end Schema
end EtcdGrove
end Perennial
