/-
## `schema.unsafeGetAllRoles(...)` (internal)

**Users.** The `authBatchTx`/`authReadTx` methods of the same name (for `RoleList`, `refreshRangePermCache` (`auth/store.go`, on the batch transaction only)).
**Proof sketch.** `tx.UnsafeRange(AuthRoles, [0], [0xff], -1)` (`txRange`: an interval range, which etcd's read transactions refuse on a non-safe-range bucket), `proto.Unmarshal` of each (`recsWf`). **Changes.** From `specs-ref`'s `unsafeGetAllRoles.lean` (where it had one: the read
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

/-- **Every role** whose name is in `[0x00, 0xff)`, in name order (`nil` if none). -/
def unsafeGetAllRoles.spec : Prop :=
  ∀ (lg : Loc) (tx : GoInterface) (S : Scope) (R : View → IProp GF) (V : View) (m : BData),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ txRange tx S R ∗ R V ∗ ⌜S.whole .authRoles ∧ V .authRoles = some m ∧ recsWf go_etcd_io.etcd.api.v3.authpb.Role.ty m⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.unsafeGetAllRoles)) (Val #lg)) (Val #tx))
  {{ (sl : GoSlice), RET #sl; R V ∗ ∃ l, ⌜rangeOf m [W8 0] [W8 255] (-1) l⌝ ∗ recsRes go_etcd_io.etcd.api.v3.authpb.Role.ty sl (l.map Prod.snd) }}

end spec
end Schema
end EtcdGrove
end Perennial
