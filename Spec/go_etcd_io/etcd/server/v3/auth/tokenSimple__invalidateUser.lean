/-
## `(*tokenSimple).invalidateUser(username)` (internal helper)

**Users.** `tp_invalidateUser`, through `UserDelete`, `UserChangePassword`.

**Proof sketch.** No keeper: nothing; else under `simpleTokensMu`, every token of the user deleted from the map and the keeper (`deleteSimpleToken`).

**Changes.** New (round 1, review S6: per (type, method); the old proofs' lemmas in `Proof/.../auth/TokenSimple*.lean`, `TokenKeeperRun.lean`, `TokenNop.lean`, `PermSorter.lean`).

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

/-- **`t.invalidateUser()`**: no panic, nothing a caller observes. -/
def tokenSimple.invalidateUser.spec : Prop :=
  ∀ (t : Loc) (γ : Cluster) (R : IProp GF) (username : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ simpleAt t γ R }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.tokenSimple.ty @!! go!"invalidateUser")) (Val #username))
  {{ RET #(); True }}

end spec
end Auth
end EtcdGrove
end Perennial
