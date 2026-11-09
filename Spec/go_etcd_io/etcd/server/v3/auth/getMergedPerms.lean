/-
## `getMergedPerms(tx, userName)` (internal helper)

**Users.** `refreshRangePermCache`.

**Proof sketch.** The user read (absent: `nil`); two fresh interval trees (3f's `adt.NewIntervalTree`); for each of its roles that exists, each permission's interval (`"\x00"` as `nil`, the tree's infinity; a single key a point) inserted in the read tree, the write tree, or both (`READWRITE`); other types ignored.

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

/-- **`getMergedPerms(tx, u)`**: `nil` for a user absent from the transaction's state, else a cache
entry of its merged permissions there. -/
def getMergedPerms.spec : Prop :=
  ∀ (tx : GoInterface) (a : AuthState) (u : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ txAt tx a ∗ ⌜validPerms a⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.getMergedPerms)) (Val #tx)) (Val #u))
  {{ (p : Loc), RET #p; txAt tx a ∗
      (⌜p = null ∧ a.users u = none⌝ ∨ ⌜p ≠ null ∧ a.users u ≠ none⌝ ∗ cacheEntry p a u) }}

end spec
end Auth
end EtcdGrove
end Perennial
