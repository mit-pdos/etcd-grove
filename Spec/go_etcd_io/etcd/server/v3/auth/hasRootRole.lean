/-
## `hasRootRole(u)` (internal helper)

**Users.** `AuthEnable`, `isOpPermitted`, `IsAdminPermitted`.

**Proof sketch.** `sort.SearchStrings(u.Roles, "root")` (Perennial's spec: the first index not below, in a sorted list) and the element test.

**Changes.** The old spec restated over `Api.lean`'s and `Internal.lean`'s vocabulary.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.Internal

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Auth

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **`hasRootRole(u)`** of a user whose roles are sorted: whether `root` is among them. -/
def hasRootRole.spec : Prop :=
  ∀ (p : Loc) (roles : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ userRolesAt p roles ∗ ⌜roles.Pairwise go.GoStringLe⌝ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.auth.hasRootRole)) (Val #p))
  {{ (b : Bool), RET #b; ⌜b = true ↔ rootRole ∈ roles⌝ }}

end spec
end Auth
end EtcdGrove
end Perennial
