/-
## `(*authBatchTx).UnsafeGetAllUsers(...)`

**Users.** `UserList`, `RoleDelete`'s user scan (`auth/store.go`); 3d's auth store through `AuthBatchTx`/`AuthReadTx`. Snippet:
`examples/specreq/schema/schema.go` (`ReqAuthWriteRead`).
**Proof sketch.** Loads `atx.tx`, `atx.lg`; `unsafeGetAllUsers` (`unsafeGetAllUsers.spec`). **Changes.** From
`specs-ref`'s `authBatchTx__UnsafeGetAllUsers.lean` where there was one: over the contract. **Margin.** None.
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

/-- **Every user**, each once, in some order (`nil` if none). -/
def authBatchTx.UnsafeGetAllUsers.spec : Prop :=
  ∀ (atx : Loc) (lg : Loc) (tx : GoInterface) (S : Scope) (R : View → IProp GF) (V : View) (m : BData),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (atx ↦□ (go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.mk tx lg) : IProp GF) ∗ txRd tx S R ∗ R V ∗ ⌜S.whole .authUsers ∧ V .authUsers = some m ∧ recsWf go_etcd_io.etcd.api.v3.authpb.User.ty m⌝ }}
    (App (Val (atx @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty @!! go!"UnsafeGetAllUsers")) (Val #()))
  {{ (sl : GoSlice), RET #sl; R V ∗ ∃ l, ⌜entsAny m l⌝ ∗ recsRes go_etcd_io.etcd.api.v3.authpb.User.ty sl (l.map Prod.snd) }}

end spec
end Schema
end EtcdGrove
end Perennial
