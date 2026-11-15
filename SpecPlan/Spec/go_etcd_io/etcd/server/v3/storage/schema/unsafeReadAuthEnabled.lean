/-
## `schema.unsafeReadAuthEnabled(...)` (internal)

**Users.** The `authBatchTx`/`authReadTx` methods of the same name (for the auth store's `isAuthEnabled` reads (`auth/store.go`: on both transactions)).
**Proof sketch.** `tx.UnsafeRange(Auth, authEnabled, nil, 0)` (`txRd`), `bytes.Equal` with `authEnabled`'s `[1]` (`keyNames_init`). **Changes.** From `specs-ref`'s `unsafeReadAuthEnabled.lean` (where it had one: the read
transaction's state): over the contract.
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
def unsafeReadAuthEnabled.spec : Prop :=
  ∀ (tx : GoInterface) (S : Scope) (R : View → IProp GF) (V : View) (m : BData),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ txRd tx S R ∗ R V ∗ ⌜S.has .auth authEnabledKey ∧ V .auth = some m⌝ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.unsafeReadAuthEnabled)) (Val #tx))
  {{ RET #(authEnabledOf m); R V }}

end spec
end Schema
end EtcdGrove
end Perennial
