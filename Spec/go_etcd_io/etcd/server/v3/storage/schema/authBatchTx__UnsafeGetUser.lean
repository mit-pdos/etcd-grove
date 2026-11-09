/-
## `(*authBatchTx).UnsafeGetUser(...)`

**Users.** the auth store's checks and admin operations (`auth/store.go:433,...`); 3d's auth store through `AuthBatchTx`/`AuthReadTx`. Snippet:
`examples/specreq/schema/schema.go` (`ReqAuthWriteRead`).
**Proof sketch.** Loads `atx.tx`, `atx.lg`; `unsafeGetUser` (`unsafeGetUser.spec`). **Changes.** From
`specs-ref`'s `authBatchTx__UnsafeGetUser.lean` where there was one: over the contract. **Margin.** None.
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

/-- **The user `name`**: `nil`, or a fresh message of its stored record. -/
def authBatchTx.UnsafeGetUser.spec : Prop :=
  ∀ (atx : Loc) (lg : Loc) (tx : GoInterface) (S : Scope) (R : View → IProp GF) (V : View) (m : BData) (name : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (atx ↦□ (go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.mk tx lg) : IProp GF) ∗ txRd tx S R ∗ R V ∗ ⌜S.has .authUsers name ∧ V .authUsers = some m ∧ recsWf go_etcd_io.etcd.api.v3.authpb.User.ty m⌝ }}
    (App (Val (atx @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty @!! go!"UnsafeGetUser")) (Val #name))
  {{ (p : Loc), RET #p; R V ∗ recRes go_etcd_io.etcd.api.v3.authpb.User.ty (m name) p }}

end spec
end Schema
end EtcdGrove
end Perennial
