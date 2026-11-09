/-
## `isValidPermissionRange(key, rangeEnd)` (internal helper)

**Users.** `RoleGrantPermission`.

**Proof sketch.** An empty key: `false`; an empty `rangeEnd`: `true`; `adt.BytesAffineComparable`'s `Compare` (bytes order: W0's `keyLt`); else `isOpenEnded`.

**Changes.** Unchanged.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.Api

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

/-- **`isValidPermissionRange(key, re)`**: the range a permission may have (`validPerms`). -/
def isValidPermissionRange.spec : Prop :=
  ∀ (key re : GoSlice) (dk de : DFrac) (k e : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ key ↦*{dk} k ∗ re ↦*{de} e }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.isValidPermissionRange)) (Val #key)) (Val #re))
  {{ (b : Bool), RET #b; key ↦*{dk} k ∗ re ↦*{de} e ∗
      ⌜b = true ↔ k ≠ [] ∧ (e = [] ∨ e = [0#8] ∨ keyLt k e)⌝ }}

end spec
end Auth
end EtcdGrove
end Perennial
