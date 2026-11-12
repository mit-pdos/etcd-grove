/-
## `(*authBatchTx).UnsafeGetAllRoles(...)`

**Users.** `RoleList`, `refreshRangePermCache` (`auth/store.go`, on the batch transaction only); 3d's auth store through `AuthBatchTx`/`AuthReadTx`. Snippet:
`examples/specreq/schema/schema.go` (`ReqAuthWriteRead`).
**Proof sketch.** Loads `atx.tx`, `atx.lg`; `unsafeGetAllRoles` (`unsafeGetAllRoles.spec`). **Changes.** From
`specs-ref`'s `authBatchTx__UnsafeGetAllRoles.lean` where there was one: over the contract. **Margin.** None.
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

/-- **Every role** whose name is in `[0x00, 0xff)`, in name order (`nil` if none). -/
def authBatchTx.UnsafeGetAllRoles.spec : Prop :=
  ∀ (atx : Loc) (lg : Loc) (tx : GoInterface) (S : Scope) (R : View → IProp GF) (V : View) (m : BData),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (atx ↦□ (go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.mk tx lg) : IProp GF) ∗ txRange tx S R ∗ R V ∗ ⌜S.whole .authRoles ∧ V .authRoles = some m ∧ recsWf go_etcd_io.etcd.api.v3.authpb.Role.ty m⌝ }}
    (App (Val (atx @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty @!! go!"UnsafeGetAllRoles")) (Val #()))
  {{ (sl : GoSlice), RET #sl; R V ∗ ∃ l, ⌜rangeOf m [W8 0] [W8 255] (-1) l⌝ ∗ recsRes go_etcd_io.etcd.api.v3.authpb.Role.ty sl (l.map Prod.snd) }}

end spec
end Schema
end EtcdGrove
end Perennial
