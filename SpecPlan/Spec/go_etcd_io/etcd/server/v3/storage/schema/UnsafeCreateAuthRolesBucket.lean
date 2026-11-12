/-
## `schema.UnsafeCreateAuthRolesBucket(tx)`

**Users.** None translated (`etcdutl`'s migration). **Proof sketch.** `tx.UnsafeCreateBucket(AuthRoles)`.
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

/-- **Creates `AuthRoles`** (if absent). -/
def UnsafeCreateAuthRolesBucket.spec : Prop :=
  ∀ (tx : GoInterface) (S : Scope) (R : View → IProp GF) (V : View),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ txWr tx S R ∗ R V ∗ ⌜S.canCreate .authRoles⌝ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.UnsafeCreateAuthRolesBucket)) (Val #tx))
  {{ RET #(); R (V.create .authRoles) }}

end spec
end Schema
end EtcdGrove
end Perennial
